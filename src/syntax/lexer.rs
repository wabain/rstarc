use std::{
    io::{self, Read},
    error,
    fmt,
    rc::Rc,
    borrow::{Cow, ToOwned},
};

use regex::{RegexBuilder, Regex};

use rstarc_types::{Value, RockstarNumber};
use lang_constructs::RockstarValue;
use syntax::source_loc::{SourceLocator, IntraLineSpan};

#[derive(Debug, PartialEq)]
pub enum LexicalError {
    UnexpectedInput(usize, usize),
}

impl error::Error for LexicalError {}

impl fmt::Display for LexicalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LexicalError::UnexpectedInput(_, _) => {
                write!(f, "Unexpected input")
            }
        }
    }
}

#[derive(PartialEq, Clone)]
pub enum Token<'input> {
    // Variables and friends
    ProperVar(Cow<'input, str>),
    CommonVar(Cow<'input, str>),
    Pronoun(Cow<'input, str>),
    CommonPrep(Cow<'input, str>),

    // Types
    StringLiteral(Rc<Cow<'input, str>>),
    BooleanLiteral(bool),
    NumberLiteral(RockstarNumber),
    MysteriousLiteral,
    NullLiteral,

    // Punctuation and keywords
    Newline,
    Comma,
    Keyword(Keyword),
    EOF,
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Keyword {
    Is,
    Was,
    Not,
    Isnt,
    Than,
    As,
    Greater,
    Less,
    Great,
    Little,
    Put,
    Into,
    Build,
    Up,
    Knock,
    Down,
    Plus,
    Minus,
    Times,
    Over,
    Listen,
    To,
    Say,
    Says,
    If,
    Else,
    While,
    Until,
    Continue,
    Break,
    Takes,
    Taking,
    Take,
    From,
    Give,
    Back,
    And,
    Or,
    Nor,
}

impl<'input> Token<'input> {
    pub fn make_owned(self) -> Token<'static> {
        match self {
            Token::StringLiteral(s) => {
                let string: String = match Rc::try_unwrap(s) {
                    Ok(cow) => cow.to_string(),
                    Err(rc) => rc.as_ref().to_string(),
                };
                Token::StringLiteral(Rc::new(Cow::Owned(string)))
            },

            Token::ProperVar(s) => Token::ProperVar(Cow::Owned(s.to_string())),
            Token::CommonVar(s) => Token::CommonVar(Cow::Owned(s.to_string())),
            Token::Pronoun(s) => Token::Pronoun(Cow::Owned(s.to_string())),
            Token::CommonPrep(s) => Token::CommonPrep(Cow::Owned(s.to_string())),

            Token::BooleanLiteral(b) => Token::BooleanLiteral(b),
            Token::NumberLiteral(n) => Token::NumberLiteral(n),
            Token::MysteriousLiteral => Token::MysteriousLiteral,
            Token::NullLiteral => Token::NullLiteral,

            Token::Newline => Token::Newline,
            Token::Comma => Token::Comma,
            Token::Keyword(kw) => Token::Keyword(kw),
            Token::EOF => Token::EOF,
        }
    }

    fn is_keyword(&self) -> bool {
        // FIXME: determine if it matters that EOF is treated as a keyword here
        match *self {
            Token::Keyword(_) | Token::EOF => true,
            _ => false,
        }
    }

    fn is_constant(&self) -> bool {
        use self::Token::*;

        match *self {
            BooleanLiteral(_) |
            MysteriousLiteral |
            NullLiteral => true,
            _ => false,
        }
    }

    fn opens_block(&self) -> bool {
        use self::Keyword::*;

        let keyword = match self {
            Token::Keyword(kw) => kw,
            _ => return false,
        };

        match keyword {
            If | Else | While | Until | Takes => true,
            _ => false,
        }
    }

    pub fn literal_value<F: fmt::Debug>(&self) -> Option<RockstarValue<F>> {
        let value = match *self {
            Token::StringLiteral(ref s) => Value::String(Rc::clone(s)),
            Token::BooleanLiteral(b) => Value::Boolean(b),
            Token::NumberLiteral(n) => Value::Number(n),
            Token::MysteriousLiteral => Value::Mysterious,
            Token::NullLiteral => Value::Null,
            _ => return None,
        };
        Some(value)
    }

    pub fn deref_proper_var(&self) -> &str {
        if let Token::ProperVar(ref s) = self {
            s
        } else {
            panic!("Expected ProperVar, got {:?}", self);
        }
    }

    pub fn deref_common_var(&self) -> &str {
        if let Token::CommonVar(ref s) = self {
            s
        } else {
            panic!("Expected CommonVar, got {:?}", self);
        }
    }

    pub fn deref_common_prep(&self) -> &str {
        if let Token::CommonPrep(ref s) = self {
            s
        } else {
            panic!("Expected CommonPrep, got {:?}", self);
        }
    }

    pub fn variant_name(&self) -> &'static str {
        match self {
            Token::ProperVar(_) => "ProperVar",
            Token::CommonVar(_) => "CommonVar",
            Token::Pronoun(_) => "Pronoun",
            Token::CommonPrep(_) => "CommonPrep",
            Token::StringLiteral(_) => "StringLiteral",
            Token::BooleanLiteral(_) => "BooleanLiteral",
            Token::NumberLiteral(_) => "NumberLiteral",
            Token::MysteriousLiteral => "MysteriousLiteral",
            Token::NullLiteral => "NullLiteral",
            Token::Newline => "Newline",
            Token::Comma => "Comma",
            Token::Keyword(_) => "Keyword",
            Token::EOF => "EOF",
        }
    }

    pub fn repr_payload(&self) -> PayloadRepr {
        PayloadRepr(self)
    }
}

impl<'input> fmt::Display for Token<'input> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Token::Keyword as Kw;
        use self::Keyword::*;

        match *self {
            Token::ProperVar(ref s) |
            Token::CommonVar(ref s) |
            Token::Pronoun(ref s) |
            Token::CommonPrep(ref s) => write!(f, "{}", s),

            Token::StringLiteral(ref s) => {
                assert!(s.find('"').is_none(), "string escaping not supported");
                write!(f, "\"{}\"", s)
            }

            Token::BooleanLiteral(b) => write!(f, "{}", b),
            Token::NumberLiteral(n) => write!(f, "{}", n),
            Token::MysteriousLiteral => write!(f, "mysterious"),
            Token::NullLiteral => write!(f, "null"),

            Token::Newline => write!(f, "⏎"),
            Token::Comma => write!(f, ","),

            Kw(Is) => write!(f, "is"),
            Kw(Was) => write!(f, "was"),
            Kw(Not) => write!(f, "not"),
            Kw(Isnt) => write!(f, "isn't"),
            Kw(Than) => write!(f, "than"),
            Kw(As) => write!(f, "as"),
            Kw(Greater) => write!(f, "greater"),
            Kw(Less) => write!(f, "less"),
            Kw(Great) => write!(f, "great"),
            Kw(Little) => write!(f, "little"),
            Kw(Put) => write!(f, "put"),
            Kw(Into) => write!(f, "into"),
            Kw(Build) => write!(f, "build"),
            Kw(Up) => write!(f, "up"),
            Kw(Knock) => write!(f, "knock"),
            Kw(Down) => write!(f, "down"),
            Kw(Plus) => write!(f, "plus"),
            Kw(Minus) => write!(f, "minus"),
            Kw(Times) => write!(f, "times"),
            Kw(Over) => write!(f, "over"),
            Kw(Listen) => write!(f, "listen"),
            Kw(To) => write!(f, "to"),
            Kw(Say) => write!(f, "say"),
            Kw(Says) => write!(f, "says"),
            Kw(If) => write!(f, "if"),
            Kw(Else) => write!(f, "else"),
            Kw(While) => write!(f, "while"),
            Kw(Until) => write!(f, "until"),
            Kw(Continue) => write!(f, "continue"),
            Kw(Break) => write!(f, "break"),
            Kw(Takes) => write!(f, "takes"),
            Kw(Taking) => write!(f, "taking"),
            Kw(Take) => write!(f, "take"),
            Kw(From) => write!(f, "from"),
            Kw(Give) => write!(f, "give"),
            Kw(Back) => write!(f, "back"),
            Kw(And) => write!(f, "and"),
            Kw(Or) => write!(f, "or"),
            Kw(Nor) => write!(f, "nor"),

            Token::EOF => write!(f, "<eof>"),
        }
    }
}

impl<'input> fmt::Debug for Token<'input> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Token::Keyword(kw) = self {
            return write!(f, "{:?}", kw);
        }

        let payload = format!("{:?}", self.repr_payload());

        if payload.is_empty() {
            write!(f, "{}", self.variant_name())
        } else {
            write!(f, "{}({})", self.variant_name(), payload)
        }
    }
}

pub struct PayloadRepr<'a>(&'a Token<'a>);

impl<'a> fmt::Debug for PayloadRepr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Token::ProperVar(ref s) |
            Token::CommonVar(ref s) |
            Token::Pronoun(ref s) |
            Token::CommonPrep(ref s) => write!(f, "{:?} {}", s, cow_type(s)),

            Token::StringLiteral(ref s) => {
                write!(
                    f,
                    "{:?} {} *[rc {}/{} weak]",
                    s, cow_type(s.as_ref()), Rc::strong_count(s), Rc::weak_count(s),
                )
            },

            Token::BooleanLiteral(b) => write!(f, "{:?}", b),
            Token::NumberLiteral(n) => write!(f, "{:?}", n),

            _ => Ok(()),
        }
    }
}

fn cow_type<T: ToOwned + ?Sized>(cow: &Cow<T>) -> &'static str {
    match &cow {
        Cow::Owned(_) => "owned",
        Cow::Borrowed(_) => "borrowed",
    }
}

struct TCtx {
    poetic_number_or_keyword: bool,
    prev_was_eol: bool,
    eof_reached: bool,
    at_start: bool,
}

impl Default for TCtx {
    fn default() -> Self {
        TCtx {
            poetic_number_or_keyword: false,
            prev_was_eol: false,
            eof_reached: false,
            at_start: false,
        }
    }
}

lazy_static! {
    static ref NEWLINE: Regex = Regex::new(r"^(\r\n|\n|\r)").unwrap();
    pub static ref NEWLINE_SEARCH: Regex = Regex::new(r"\r\n|\n|\r").unwrap();

    static ref LEADING_SPACE: Regex = Regex::new(r"^[\s&&[^\r\n]]+").unwrap();
    static ref COMMENT: Regex = RegexBuilder::new(r"^\(.*?\)")
        .dot_matches_new_line(true)
        .build()
        .unwrap();

    static ref APOS: Regex = Regex::new(r"^'").unwrap();

    // This are deliberately case-sensitive
    static ref APOS_S_START: Regex = Regex::new(r"^'s\b").unwrap();

    static ref NUMBER: Regex = Regex::new(r"^([0-9]*\.[0-9]+|[0-9]+)").unwrap();
    static ref STRING: Regex = Regex::new("^\"(.*?)\"").unwrap();
    static ref COMMA: Regex = Regex::new(r"^,").unwrap();

    // FIXME: Should this more for spaces?
    static ref TAKE_IT_TO_THE_TOP: Regex = RegexBuilder::new("^take it to the top")
        .case_insensitive(true)
        .build()
        .unwrap();
    static ref BREAK_IT_DOWN: Regex = RegexBuilder::new("^break it down")
        .case_insensitive(true)
        .build()
        .unwrap();

    // Spec seems to say we stick to ASCII
    static ref WORD_INPUT: Regex = Regex::new(r"^[a-zA-Z']+('|\b)").unwrap();
    static ref PROPER_VAR_WORD: Regex = Regex::new(r"^[A-Z][a-zA-Z']*('|\b)").unwrap();
    static ref COMMON_VAR: Regex = Regex::new(r"^[a-z']+('|\b)").unwrap();
}

pub struct Tokenizer {
    content: String,
    source_locator: SourceLocator,
}

impl Tokenizer {
    pub fn new(content: String) -> Self {
        let source_locator = SourceLocator::new(&content);
        Tokenizer { content, source_locator }
    }

    pub fn from_file<R: Read>(source: &mut R) -> io::Result<Self> {
        let mut content = String::new();
        source.read_to_string(&mut content)?;
        Ok(Self::new(content))
    }

    pub fn get_line_for_point(&self, point: usize) -> usize {
        self.source_locator.get_line_idx(point) + 1
    }

    pub fn get_line_with_number(&self, lineno: usize) -> &str {
        self.source_locator.get_line_at_idx(&self.content, lineno - 1)
    }

    pub fn get_line_span(&self, start: usize, end: usize) -> IntraLineSpan {
        self.source_locator.get_line_span(&self.content, start, end)
    }

    pub fn tokenize<'input>(&'input self) -> TokenIterator<'input> {
        TokenIterator::new(&self)
    }
}

/// Hack: This struct exists primarily to scan the token stream and drop
/// commas occurring before EOL. This can't easily be handled in parsing
/// without ambiguity and putting it directly in the lexing code would
/// be complicated.
pub struct TokenIterator<'input> {
    stream: TokenStream<'input>,
    has_error: bool,
    buf: Vec<(usize, Token<'input>, usize)>,
}

impl<'input> TokenIterator<'input> {
    fn new(tokenizer: &'input Tokenizer) -> Self {
        TokenIterator {
            stream: TokenStream::new(tokenizer),
            has_error: false,
            buf: Vec::new(),
        }
    }

    fn has_buffered_eol(&self) -> bool {
        self.buf.iter().find(|&(_, t, _)| t == &Token::Newline).is_some()
    }
}

impl<'input> Iterator for TokenIterator<'input> {
    type Item = Result<(usize, Token<'input>, usize), LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_error {
            return None;
        }

        if !self.stream.has_more() || self.has_buffered_eol() {
            if self.buf.is_empty() {
                return None;
            }

            return Some(Ok(self.buf.remove(0)));
        }

        while self.stream.has_more() && !self.has_buffered_eol() {
            match self.stream.take_more() {
                Ok(entries) => self.buf.extend(entries),
                Err(e) => {
                    self.has_error = true;
                    return Some(Err(e));
                }
            }
        }

        let mut i = 0;

        while i < self.buf.len() {
            if self.buf[i].1 != Token::Newline {
                i += 1;
                continue;
            }

            while i > 0 && self.buf[i - 1].1 == Token::Comma {
                self.buf.remove(i - 1);
                i -= 1;
            }

            i += 1;
        }

        Some(Ok(self.buf.remove(0)))
    }
}

struct TokenStream<'input> {
    tokenizer: &'input Tokenizer,
    idx: usize,
    ctx: TCtx,
    line_begins_with_keyword: bool,
    open_blocks: usize,
}

impl<'input> TokenStream<'input> {
    fn new(tokenizer: &'input Tokenizer) -> Self {
        let mut ctx = TCtx::default();
        ctx.at_start = true;
        TokenStream {
            tokenizer,
            idx: 0,
            ctx,
            line_begins_with_keyword: false,
            open_blocks: 0,
        }
    }

    fn emit(&mut self, length: usize, tok: Token<'input>, ctx: Option<TCtx>)
        -> (usize, Token<'input>, usize)
    {
        let new_ctx = ctx.unwrap_or_default();

        if self.ctx.prev_was_eol || self.ctx.at_start {
            self.line_begins_with_keyword = tok.is_keyword();
        }

        if tok.opens_block() {
            self.open_blocks += 1;
        } else if self.ctx.prev_was_eol && tok == Token::Newline && self.open_blocks > 0 {
            self.open_blocks -= 1;
        }

        self.ctx = new_ctx;

        let start = self.idx;
        let end = self.idx + length;
        self.idx = end;

        (start, tok, end)
    }

    fn emit_eof(&mut self) -> Vec<(usize, Token<'input>, usize)> {
        let mut toks = vec![];

        if !self.ctx.prev_was_eol {
            toks.push((self.idx, Token::Newline, self.idx));
        }

        for _ in 0..self.open_blocks {
            toks.push((self.idx, Token::Newline, self.idx));
        }

        toks.push((self.idx, Token::EOF, self.idx));

        let mut ctx = TCtx::default();
        ctx.eof_reached = true;
        self.ctx = ctx;

        toks
    }

    fn has_more(&self) -> bool {
        !self.ctx.eof_reached
    }

    fn rest(&self) -> &'input str {
        &self.tokenizer.content[self.idx..]
    }

    fn next_char(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn take_more(&mut self) -> Result<Vec<(usize, Token<'input>, usize)>, LexicalError> {
        // General guidelines: any mutation of the tokenization should
        // occur from this function or the emit functions.

        if !self.has_more() {
            panic!("take_more() called after EOF")
        }

        // Eat comments and leading whitespace and handle apostrophes
        loop {
            let prev_idx = self.idx;

            while let Some(end) = self.find_leading_ignored(self.rest()) {
                self.idx += end;
            }

            if let Some(end) = APOS_S_START.find(self.rest()).map(|m| m.end()) {
                let action = if self.line_is_poetic_string_candidate() {
                    LexAction::CheckKeywordOrPoeticString
                } else {
                    LexAction::NoAction
                };

                return self.emit_and_handle_lex_action(
                    end, Some(Token::Keyword(Keyword::Is)), action
                );
            }

            if let Some(end) = APOS.find(self.rest()).map(|m| m.end()) {
                self.idx += end;
            }

            if self.idx == prev_idx {
                break;
            }
        }

        // Handle EOF
        if self.rest().is_empty() {
            return Ok(self.emit_eof());
        }

        // Handle newline
        if let Some(end) = NEWLINE.find(self.rest()).map(|m| m.end()) {
            let mut ctx = TCtx::default();
            ctx.prev_was_eol = true;

            return Ok(vec![
                self.emit(end, Token::Newline, Some(ctx))
            ]);
        }

        // Handle string literal
        if let Some(captures) = STRING.captures(self.rest()) {
            let len = captures[0].len();

            let value = captures.get(1).expect("string capture").as_str();
            let tok = Token::StringLiteral(Rc::new(Cow::Borrowed(value)));

            return Ok(vec![
                self.emit(len, tok, None)
            ]);
        }

        // Handle number literal
        if let Some(end) = NUMBER.find(self.rest()).map(|m| m.end()) {
            let float: RockstarNumber = self.rest()[..end].parse().expect("number literal");
            return Ok(vec![
                self.emit(end, Token::NumberLiteral(float), None)
            ]);
        }

        // Handle comma
        if let Some(end) = COMMA.find(self.rest()).map(|m| m.end()) {
            return Ok(vec![
                self.emit(end, Token::Comma, None)
            ]);
        }

        // Handle "take it to the top" for continue
        if let Some(end) = TAKE_IT_TO_THE_TOP.find(self.rest()).map(|m| m.end()) {
            return Ok(vec![
                self.emit(end, Token::Keyword(Keyword::Continue), None)
            ]);
        }

        // Handle "break it down" for break
        if let Some(end) = BREAK_IT_DOWN.find(self.rest()).map(|m| m.end()) {
            return Ok(vec![
                self.emit(end, Token::Keyword(Keyword::Break), None)
            ]);
        }

        // From here on we should have a word (i.e. keyword or variable)
        let (word, word_len) = match self.find_word(self.rest(), &WORD_INPUT) {
            Some(end) => end,
            None => return Err(LexicalError::UnexpectedInput(self.idx, self.idx)),
        };

        // Optionally take a token for the word; optionally specify an
        // additional action if the word alone isn't sufficient
        let (tok, action) = self.handle_word(word)?;

        self.emit_and_handle_lex_action(word_len, tok, action)
    }

    /// Parse a keyword or variable and handle any contextually-triggered
    /// actions (e.g., poetic variables which break the normal lexing
    /// rules)
    fn emit_and_handle_lex_action(
        &mut self,
        word_len: usize,
        tok: Option<Token<'input>>,
        action: LexAction,
    ) -> Result<Vec<(usize, Token<'input>, usize)>, LexicalError> {
        let mut to_emit = vec![];

        if let Some(tok) = tok {
            let mut ctx = TCtx::default();

            ctx.poetic_number_or_keyword =
                action == LexAction::CheckKeywordOrPoeticString;

            to_emit.push(self.emit(word_len, tok, Some(ctx)));
        }

        // Dispatch lexing actions which generate a further token
        if let Some((skip, len, tok, ctx)) = self.handle_action(action)? {
            self.idx += skip;
            to_emit.push(self.emit(len, tok, ctx));
        }

        Ok(to_emit)
    }

    fn find_leading_ignored(&self, target: &str) -> Option<usize> {
        LEADING_SPACE.find(target)
            .or_else(|| COMMENT.find(target))
            .map(|m| m.end())
    }

    fn handle_word(&self, word: Cow<'input, str>)
        -> Result<(Option<Token<'input>>, LexAction), LexicalError>
    {
        let kw_or_const = self.match_keyword_or_constant(word);

        if let Ok(token) = kw_or_const {
            if self.ctx.poetic_number_or_keyword && !(token.is_keyword() || token.is_constant()) {
                return Ok((None, LexAction::TakePoeticNumber));
            }

            use self::Keyword::{Says, Was, Is};
            let action;

            match token {
                Token::Keyword(Says) => {
                    action = LexAction::TakePoeticString;
                }
                Token::Keyword(Was) => {
                    action = LexAction::TakePoeticNumber;
                }
                Token::Keyword(Is) if self.line_is_poetic_string_candidate() => {
                    action = LexAction::CheckKeywordOrPoeticString;
                }
                _ => {
                    action = LexAction::NoAction;
                }
            }

            return Ok((Some(token), action));
        }

        let word = kw_or_const.expect_err("recover word");

        if self.ctx.poetic_number_or_keyword {
            Ok((None, LexAction::TakePoeticNumber))
        } else if COMMON_VAR.is_match(&word) {
            let tok = Token::CommonVar(word);
            Ok((Some(tok), LexAction::NoAction))
        } else if PROPER_VAR_WORD.is_match(&word) {
            Ok((None, LexAction::TakeProperVar))
        } else {
            Err(LexicalError::UnexpectedInput(self.idx, self.idx))
        }
    }

    fn handle_action(&self, action: LexAction)
        -> Result<Option<(usize, usize, Token<'input>, Option<TCtx>)>, LexicalError>
    {
        match action {
            LexAction::NoAction | LexAction::CheckKeywordOrPoeticString => Ok(None),
            LexAction::TakePoeticString => {
                // Spec says we need one literal space and then the string goes to EOL
                //
                // This implementation assumes that comments aren't allowed in poetic strings

                if self.next_char() != Some(' ') {
                    return Err(LexicalError::UnexpectedInput(self.idx, self.idx + 1))
                }

                let skip = 1;

                let (end, tok) = {
                    let (content, end) = self.capture_to_end_of_line_from(skip);
                    let tok = Token::StringLiteral(Rc::new(Cow::Borrowed(content)));
                    (end, tok)
                };

                Ok(Some((skip, end - skip, tok, None)))
            }
            LexAction::TakePoeticNumber => {
                let (number, end) = self.compute_poetic_number();
                let skip = LEADING_SPACE.find(self.rest()).map_or(0, |m| m.end());
                assert!(skip < end);
                Ok(Some((skip, end - skip, Token::NumberLiteral(number), None)))
            }
            LexAction::TakeProperVar => {
                let mut normalized_var = None;
                let mut var_end = 0;

                for iter in 0.. {
                    let more = &self.rest()[var_end..];

                    // The spec specifies exactly one space between words in a
                    // common variable
                    if iter > 0 && more.chars().next() != Some(' ') {
                        break;
                    }

                    let skip = if iter == 0 {
                        0
                    } else {
                        1
                    };

                    // Each word must also start with an uppercase
                    let next = match self.find_word(&more[skip..], &PROPER_VAR_WORD) {
                        Some((word, end)) => (word, skip + end),
                        None => break,
                    };

                    let (next_word, next_end) = next;

                    // If the next word is a keyword, we're done
                    let next_word = match self.match_keyword_or_constant(next_word) {
                        Ok(_) => break,
                        Err(w) => w,
                    };

                    // If next_word is an owned string (meaning it's been
                    // normalized), or if we have previously started normalizing
                    // this var, we need to append the word to the normalized form.
                    match (&mut normalized_var, next_word) {
                        (None, Cow::Borrowed(_)) => {},
                        (None, Cow::Owned(next_word)) => {
                            normalized_var = if var_end == 0 {
                                Some(next_word)
                            } else {
                                let mut norm = self.rest()[..var_end + 1].to_owned();
                                norm += &next_word;
                                Some(norm)
                            };
                        }
                        (Some(ref mut norm), ref next_word) => {
                            norm.push_str(" ");
                            norm.push_str(next_word);
                        }
                    }

                    var_end += next_end;
                }

                let payload = match normalized_var {
                    Some(norm) => Cow::Owned(norm),
                    None => Cow::Borrowed(&self.rest()[..var_end]),
                };
                Ok(Some((0, var_end, Token::ProperVar(payload), None)))
            }
        }
    }

    fn match_keyword_or_constant(&self, word: Cow<'input, str>) -> Result<Token<'input>, Cow<'input, str>> {
        use self::Keyword::*;

        let lower = word.to_lowercase();

        // Restrict value keywords to be lowercase
        let initially_lower = lower == word.as_ref();

        let tok = match lower.as_str() {

            // Prepositions take a consistent case
            "a" | "an" | "the" | "my" | "your" => {
                let normalized = if initially_lower {
                    word
                } else {
                    Cow::Owned(lower)
                };

                Token::CommonPrep(normalized)
            }
            "it" | "he" | "she" | "him" | "her" | "they" | "them" |
            "ze" | "hir" | "zie" | "zir" | "xe" | "xem" | "ve" | "ver" => {
                Token::Pronoun(word)
            }

            "mysterious" if initially_lower => Token::MysteriousLiteral,

            // Keep these in sync with rstarc_types::string_is_null_keyword
            "null" | "nothing" | "nowhere" |
            "nobody" | "empty" | "gone" if initially_lower => {
                Token::NullLiteral
            }

            // Keep these in sync with rstarc_types::string_to_bool
            "true" | "right" | "yes" | "ok" if initially_lower => {
                Token::BooleanLiteral(true)
            },
            "false" | "wrong" | "no" | "lies" if initially_lower => {
                Token::BooleanLiteral(false)
            },

            "is" => Token::Keyword(Is),
            "was" | "were" => Token::Keyword(Was),
            "not" => Token::Keyword(Not),
            "isnt" | "aint" => Token::Keyword(Isnt),

            "as" => Token::Keyword(As),
            "than" => Token::Keyword(Than),

            "higher" | "greater" | "bigger" | "stronger" => Token::Keyword(Greater),
            "lower" | "less" | "smaller" | "weaker" => Token::Keyword(Less),

            "high" | "great" | "big" | "strong" => Token::Keyword(Great),
            "low" | "little" | "small" | "weak" => Token::Keyword(Little),

            "put" => Token::Keyword(Put),
            "into" => Token::Keyword(Into),

            "build" => Token::Keyword(Build),
            "up" => Token::Keyword(Up),

            "knock" => Token::Keyword(Knock),
            "down" => Token::Keyword(Down),

            "plus" | "with" => Token::Keyword(Plus),
            "minus" | "without" => Token::Keyword(Minus),
            "times" | "of" => Token::Keyword(Times),
            "over" => Token::Keyword(Over),

            "listen" => Token::Keyword(Listen),
            "to" => Token::Keyword(To),

            "say" | "shout" | "whisper" | "scream" => Token::Keyword(Say),
            "says" => Token::Keyword(Says),

            "if" => Token::Keyword(If),
            "else" => Token::Keyword(Else),
            "while" => Token::Keyword(While),
            "until" => Token::Keyword(Until),

            "continue" => Token::Keyword(Continue),
            "break" => Token::Keyword(Break),

            "takes" => Token::Keyword(Takes),
            "taking" => Token::Keyword(Taking),

            "take" => Token::Keyword(Take),
            "from" => Token::Keyword(From),

            "give" => Token::Keyword(Give),
            "back" => Token::Keyword(Back),

            "and" => Token::Keyword(And),
            "or" => Token::Keyword(Or),
            "nor" => Token::Keyword(Nor),

            _ => return Err(word),
        };
        Ok(tok)
    }

    fn find_word(&self, src: &'input str, pattern: &Regex) -> Option<(Cow<'input, str>, usize)> {
        pattern.find(src).map(|m| {
            let end = m.end();
            // Special case: leave a 's to be processed later
            if src[..end].ends_with("'s") {
                assert!(end > 2, "Standalone 's should be pre-processed");
                end - 2
            } else {
                end
            }
        }).map(|end| {
            if src[..end].contains('\'') {
                (src[..end].replace("'", "").into(), end)
            } else {
                (Cow::Borrowed(&src[..end]), end)
            }
        })
    }

    fn line_is_poetic_string_candidate(&self) -> bool {
        // FIXME: This depends on there being no productions in the
        // parser where an is occurs on a line that does not start
        // with a keyword except "<variable> is ..."
        //
        // This is not very forward compatible!
        !self.line_begins_with_keyword
    }

    fn compute_poetic_number(&self) -> (RockstarNumber, usize) {
        // FIXME: This assumes comments aren't allowed in the
        // poetic number clause, which seems like a reasonable thing
        // to want to do.

        let (content, len) = self.capture_to_end_of_line();

        let mut counts = vec![];
        let mut current_count = 0;
        let mut significand = None;

        for c in content.chars() {
            if c.is_ascii() && c.is_alphabetic() {
                current_count += 1;
                continue;
            }

            if c.is_ascii_whitespace() && current_count > 0 {
                counts.push(current_count % 10);
                current_count = 0;
            }

            if significand.is_none() && c == '.' {
                significand = Some(counts.len());
            }
        }

        if current_count > 0 {
            counts.push(current_count);
        }

        // Very theoretical, but...
        assert!(counts.len() <= i32::max_value() as usize);

        let significand = significand.unwrap_or(counts.len() - 1) as i32;
        let mut number: RockstarNumber = 0.0;

        for (i, n) in counts.into_iter().enumerate() {
            let place = significand - (i as i32);
            number += (n as RockstarNumber) * (10.0 as RockstarNumber).powi(place);
        }

        (number, len)
    }

    fn capture_to_end_of_line(&self) -> (&str, usize) {
        self.capture_to_end_of_line_from(0)
    }

    fn capture_to_end_of_line_from(&self, idx: usize) -> (&'input str, usize) {
        let slice = &self.rest()[idx..];

        match NEWLINE_SEARCH.find(slice) {
            Some(m) => {
                let newline_start = m.start();
                (&slice[..newline_start], idx + newline_start)
            }
            None => {
                (slice, idx + slice.len())
            }
        }
    }
}

#[derive(PartialEq)]
enum LexAction {
    NoAction,
    TakePoeticNumber,
    TakePoeticString,
    TakeProperVar,
    CheckKeywordOrPoeticString,
}

#[cfg(test)]
mod test {
    use std::{
        borrow::Cow,
        rc::Rc,
    };
    use super::{LexicalError, Token, Keyword, Tokenizer};

    fn toks<S, F>(input: S, f: F)
        where
            S: Into<String>,
            F: for<'input> FnOnce(Vec<(usize, Token<'input>, usize)>),
    {
        let tokenizer = Tokenizer::new(input.into());
        let tokens = tokenizer.tokenize().collect::<Result<Vec<_>, _>>().unwrap();

        f(tokens);
    }

    fn tok_err<S>(input: S) -> LexicalError
        where S: Into<String>
    {
        let tokenizer = Tokenizer::new(input.into());
        tokenizer.tokenize().collect::<Result<Vec<_>, _>>().unwrap_err()
    }

    macro_rules! assert_toks {
        ($input:expr, $($x:tt)*) => {
            toks($input, |out| assert_eq!(out, $($x)*));
        };
    }

    macro_rules! assert_first_tok {
        ($input:expr, $($x:tt)*) => {
            toks($input, |out| assert_eq!(out[0], $($x)*));
        };
    }

    macro_rules! extend_vec {
        ($vec:expr, $more:expr) => (
            $vec.clone().into_iter().chain($more).collect::<Vec<_>>()
        );
    }

    #[test]
    fn tokenize_newlines() {
        let input = " \n \r \r\n ";
        //           01 23 45 6 7

        let expected = vec![
            (1, Token::Newline, 2),
            (3, Token::Newline, 4),
            (5, Token::Newline, 7),
            (8, Token::EOF, 8),
        ];

        assert_toks!(input, expected);
    }

    #[test]
    fn insert_final_newline() {
        let input = "abc\ndef";
        //           0123 456

        let expected = vec![
            (0, Token::CommonVar("abc".into()), 3),
            (3, Token::Newline, 4),
            (4, Token::CommonVar("def".into()), 7),
            (7, Token::Newline, 7),
            (7, Token::EOF, 7),
        ];

        assert_toks!(input, expected);
    }

    #[test]
    fn insert_block_terminations_at_eof() {
        let input = "while true is true\nSay \"okay\"";
        //           0123456789012345678 90123 45678 9

        toks(input, |t| {
            assert_eq!(&t[t.len() - 4..], &[
                (23, Token::StringLiteral(Rc::new(Cow::Owned("okay".to_owned()))), 29),
                (29, Token::Newline, 29),
                (29, Token::Newline, 29),
                (29, Token::EOF, 29),
            ]);
        });
    }

    #[test]
    fn drop_commas_before_eol() {
        let input = "its very,,,\n,,\ninteresting, indeed,";
        //           012345678901 234 56789012345678901234

        assert_toks!(input, vec![
            (0, Token::CommonVar("its".into()), 3),
            (4, Token::CommonVar("very".into()), 8),
            (11, Token::Newline, 12),
            (14, Token::Newline, 15),
            (15, Token::CommonVar("interesting".into()), 26),
            (26, Token::Comma, 27),
            (28, Token::CommonVar("indeed".into()), 34),
            (35, Token::Newline, 35),
            (35, Token::EOF, 35),
        ]);
    }

    #[test]
    fn handle_comments() {
        let input = "If (and this is\nimportant to know) X is true";
        //           0123456789012345 6789012345678901234567890123
        //           0         1          2         3         4

        assert_toks!(input, &[
            (0, Token::Keyword(Keyword::If), 2),
            (35, Token::ProperVar("X".into()), 36),
            (37, Token::Keyword(Keyword::Is), 39),
            (40, Token::BooleanLiteral(true), 44),
            (44, Token::Newline, 44),
            (44, Token::Newline, 44),
            (44, Token::EOF, 44),
        ]);
    }

    #[test]
    fn lexing_errors() {
        assert_eq!(tok_err("abc忠犬ハチ公"), LexicalError::UnexpectedInput(0, 0));
        assert_eq!(tok_err("aSciIbuTNotAccEptaBlE"),
                   LexicalError::UnexpectedInput(0, 0));
        assert_eq!(tok_err("my friend says\u{205F}okay"),
                   LexicalError::UnexpectedInput(14, 15));
    }

    #[test]
    fn parse_proper_var() {
        let input = "If Johnny B Goode Great";
        //           01234567890123456789012

        let expected = &[
            (0, Token::Keyword(Keyword::If), 2),
            (3, Token::ProperVar("Johnny B Goode".into()), 17),
            (18, Token::Keyword(Keyword::Great), 23),
        ];

        toks(input, |t| assert_eq!(&t[..3], expected));
    }

    #[test]
    fn parse_poetic_string() {
        let input = "Johnny says  忠犬ハチ公,,";
        //           0123456789012..

        let end = input.len();

        let base = vec![
            (0, Token::ProperVar("Johnny".into()), 6),
            (7, Token::Keyword(Keyword::Says), 11),
            (12, Token::StringLiteral(Rc::new(Cow::Owned(" 忠犬ハチ公,,".to_owned()))), end),
        ];

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end),
            (end, Token::EOF, end),
        ]);

        assert_toks!(input, expected, "no EOL");

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end + 1),
            (end + 1, Token::EOF, end + 1),
        ]);

        assert_toks!(input.to_owned() + "\n", expected, "with EOL");
    }

    #[test]
    fn parse_poetic_number_without_dec_place() {
        let input = "My dreams were    ice and snow";
        //           012345678901234567890123456789
        //           0         1         2

        let end = input.len();

        let base = vec![
            (0, Token::CommonPrep("my".into()), 2),
            (3, Token::CommonVar("dreams".into()), 9),
            (10, Token::Keyword(Keyword::Was), 14),
            (18, Token::NumberLiteral(334.0), end),
        ];

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end),
            (end, Token::EOF, end),
        ]);

        assert_toks!(input, expected, "no EOL");

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end + 1),
            (end + 1, Token::EOF, end + 1),
        ]);

        assert_toks!(input.to_owned() + "\n", expected, "with EOL");
    }

    #[test]
    fn parse_poetic_number_with_dec_place() {
        let input = "My dreams were     ice. A life unfulfilled; \
                     wakin' everybody up, taking booze and pills";

        let end = input.len();

        let base = vec![
            (0, Token::CommonPrep("my".into()), 2),
            (3, Token::CommonVar("dreams".into()), 9),
            (10, Token::Keyword(Keyword::Was), 14),
            (19, Token::NumberLiteral(3.1415926535), end),
        ];

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end),
            (end, Token::EOF, end),
        ]);

        assert_toks!(input, expected, "no EOL");

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end + 1),
            (end + 1, Token::EOF, end + 1),
        ]);

        assert_toks!(input.to_owned() + "\n", expected, "with EOL");
    }

    #[test]
    fn parse_literal_number() {
        assert_first_tok!("0.2", (0, Token::NumberLiteral(0.2), 3));
        assert_first_tok!(".2", (0, Token::NumberLiteral(0.2), 2));
        assert_first_tok!("100", (0, Token::NumberLiteral(100.0), 3));
    }

    #[test]
    fn parse_long_loop_controls() {
        assert_first_tok!("Take it to the top", (0, Token::Keyword(Keyword::Continue), 18));
        assert_first_tok!("Break it down", (0, Token::Keyword(Keyword::Break), 13));
    }

    #[test]
    fn apos_s_at_end_of_word() {
        let input = "Union's been on strike";
        //           0123456789012345678901
        //           0         1         2
        assert_toks!(input, vec![
            (0, Token::ProperVar("Union".into()), 5),
            (5, Token::Keyword(Keyword::Is), 7),
            (8, Token::NumberLiteral(426.0), 22),
            (22, Token::Newline, 22),
            (22, Token::EOF, 22),
        ]);
    }

    #[test]
    fn apos_s_with_space_before() {
        let input = "Union 's been on strike";
        //           01234567890123456789012
        //           0         1         2
        assert_toks!(input, vec![
            (0, Token::ProperVar("Union".into()), 5),
            (6, Token::Keyword(Keyword::Is), 8),
            (9, Token::NumberLiteral(426.0), 23),
            (23, Token::Newline, 23),
            (23, Token::EOF, 23),
        ]);
    }

    #[test]
    fn parse_apostrophe() {
        let input = "a '''' wakin'up Sleepin' I''n";
        //           012345678901234567890123456789
        //           0         1         2
        assert_toks!(input, vec![
            (0, Token::CommonPrep("a".into()), 1),
            (7, Token::CommonVar("wakinup".into()), 15),
            (16, Token::ProperVar("Sleepin In".into()), 29),
            (29, Token::Newline, 29),
            (29, Token::EOF, 29),
        ]);
    }

    #[test]
    fn parse_aint() {
        let input = "It ain't nothing";
        //           0123456789012345
        assert_toks!(input, vec![
            (0, Token::Pronoun("It".into()), 2),
            (3, Token::Keyword(Keyword::Isnt), 8),
            (9, Token::NullLiteral, 16),
            (16, Token::Newline, 16),
            (16, Token::EOF, 16),
        ]);
    }
}
