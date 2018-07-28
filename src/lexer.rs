use std::io::{self, Read};
use std::error;
use std::fmt;

use regex::{RegexBuilder, Regex};

use source_loc::{SourceLocator, IntraLineSpan};

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

// FIXME: Spec calls for DEC64
pub type RockstarNumber = f64;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    // Variables and friends
    ProperVar(String),
    CommonVar(String),
    Pronoun(String),
    CommonPrep(String),

    // Types
    StringLiteral(String),
    BooleanLiteral(bool),
    NumberLiteral(RockstarNumber),
    MysteriousLiteral,
    NullLiteral,

    // Punctuation
    Newline,
    Comma,

    // Other keywords
    Is,
    Was,
    Not,
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

    EOF,
}

impl Token {
    fn is_keyword(&self) -> bool {
        use self::Token::*;

        // XXX: All of this is pretty iffy
        match *self {
            // Variables etc.
            ProperVar(_) |
            CommonVar(_) |
            Pronoun(_) |
            CommonPrep(_) => false,

            // Types - Tokens whose values form a finite set are keywords
            StringLiteral(_) | NumberLiteral(_) => false,

            BooleanLiteral(_) |
            MysteriousLiteral |
            NullLiteral => true,

            // Punctuation
            Newline |
            Comma => false,

            // Actual keywords
            _ => true,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

            Token::Is => write!(f, "is"),
            Token::Was => write!(f, "was"),
            Token::Not => write!(f, "not"),
            Token::Than => write!(f, "than"),
            Token::As => write!(f, "as"),
            Token::Greater => write!(f, "greater"),
            Token::Less => write!(f, "less"),
            Token::Great => write!(f, "great"),
            Token::Little => write!(f, "little"),
            Token::Put => write!(f, "put"),
            Token::Into => write!(f, "into"),
            Token::Build => write!(f, "build"),
            Token::Up => write!(f, "up"),
            Token::Knock => write!(f, "knock"),
            Token::Down => write!(f, "down"),
            Token::Plus => write!(f, "plus"),
            Token::Minus => write!(f, "minus"),
            Token::Times => write!(f, "times"),
            Token::Over => write!(f, "over"),
            Token::Listen => write!(f, "listen"),
            Token::To => write!(f, "to"),
            Token::Say => write!(f, "say"),
            Token::Says => write!(f, "says"),
            Token::If => write!(f, "if"),
            Token::While => write!(f, "while"),
            Token::Until => write!(f, "until"),
            Token::Continue => write!(f, "continue"),
            Token::Break => write!(f, "break"),
            Token::Takes => write!(f, "takes"),
            Token::Taking => write!(f, "taking"),
            Token::Take => write!(f, "take"),
            Token::From => write!(f, "from"),
            Token::Give => write!(f, "give"),
            Token::Back => write!(f, "back"),
            Token::And => write!(f, "and"),
            Token::Or => write!(f, "or"),

            Token::EOF => write!(f, "<eof>"),
        }
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
    static ref WORD: Regex = Regex::new(r"^[a-zA-Z]+\b").unwrap();
    static ref PROPER_VAR_WORD: Regex = Regex::new(r"^[A-Z][a-zA-Z]*\b").unwrap();
    static ref COMMON_VAR: Regex = Regex::new(r"^[a-z]+\b").unwrap();
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

    pub fn get_line_span(&self, start: usize, end: usize) -> IntraLineSpan {
        self.source_locator.get_line_span(&self.content, start, end)
    }

    pub fn tokenize(&self) -> TokenIterator {
        TokenIterator::new(&self)
    }
}

/// Hack: This struct exists primarily to scan the token stream and drop
/// commas occurring before EOL. This can't easily be handled in parsing
/// without ambiguity and putting it directly in the lexing code would
/// be complicated.
pub struct TokenIterator<'a> {
    stream: TokenStream<'a>,
    has_error: bool,
    buf: Vec<(usize, Token, usize)>,
}

impl<'a> TokenIterator<'a> {
    fn new(tokenizer: &'a Tokenizer) -> Self {
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

impl<'a> ::std::iter::Iterator for TokenIterator<'a> {
    type Item = Result<(usize, Token, usize), LexicalError>;

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

struct TokenStream<'a> {
    tokenizer: &'a Tokenizer,
    idx: usize,
    ctx: TCtx,
    line_begins_with_keyword: bool,
}

impl<'a> TokenStream<'a> {
    fn new(tokenizer: &'a Tokenizer) -> Self {
        let mut ctx = TCtx::default();
        ctx.at_start = true;
        TokenStream {
            tokenizer,
            idx: 0,
            ctx,
            line_begins_with_keyword: false,
        }
    }

    fn emit(&mut self, length: usize, tok: Token, ctx: Option<TCtx>)
        -> (usize, Token, usize)
    {
        let new_ctx = ctx.unwrap_or_default();

        if self.ctx.prev_was_eol || self.ctx.at_start {
            self.line_begins_with_keyword = tok.is_keyword();
        }

        self.ctx = new_ctx;

        let start = self.idx;
        let end = self.idx + length;
        self.idx = end;

        (start, tok, end)
    }

    fn emit_eof(&mut self) -> Vec<(usize, Token, usize)> {
        let mut toks = vec![];

        if !self.ctx.prev_was_eol {
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

    fn rest(&self) -> &str {
        &self.tokenizer.content[self.idx..]
    }

    fn next_char(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn take_more(&mut self) -> Result<Vec<(usize, Token, usize)>, LexicalError> {
        // General guidelines: any mutation of the tokenization should
        // occur from this function or the emit functions.

        if !self.has_more() {
            panic!("take_more() called after EOF")
        }

        // Eat any leading whitespace
        if let Some(end) = LEADING_SPACE.find(self.rest()).map(|m| m.end()) {
            self.idx += end;
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
        if let Some((len, s)) = STRING.captures(self.rest()).map(|c| (c[0].len(), c[1].to_owned())) {
            let tok = Token::StringLiteral(s);
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
                self.emit(end, Token::Continue, None)
            ]);
        }

        // Handle "break it down" for break
        if let Some(end) = BREAK_IT_DOWN.find(self.rest()).map(|m| m.end()) {
            return Ok(vec![
                self.emit(end, Token::Break, None)
            ]);
        }

        // From here on we should have a word (i.e. keyword or variable)
        let word_len = match WORD.find(self.rest()) {
            Some(m) => m.end(),
            None => return Err(LexicalError::UnexpectedInput(self.idx, self.idx)),
        };

        // Optionally take a token for the word; optionally specify an
        // additional action if the word alone isn't sufficient
        let (tok, action) = self.handle_word(&self.rest()[..word_len])?;

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

    fn handle_word(&self, word: &str) -> Result<(Option<Token>, LexAction), LexicalError> {
        if let Some(token) = self.match_special_word(word) {
            if self.ctx.poetic_number_or_keyword && !token.is_keyword() {
                return Ok((None, LexAction::TakePoeticNumber));
            }

            let action;

            match token {
                Token::Says => {
                    action = LexAction::TakePoeticString;
                }
                Token::Was => {
                    action = LexAction::TakePoeticNumber;
                }
                // FIXME: This depends on there being no productions in the
                // parser where an is occurs on a line that does not start
                // with a keyword except "<variable> is ..."
                //
                // This is not very forward compatible!
                Token::Is if !self.line_begins_with_keyword => {
                    action = LexAction::CheckKeywordOrPoeticString;
                }
                _ => {
                    action = LexAction::NoAction;
                }
            }

            return Ok((Some(token), action));
        }

        if self.ctx.poetic_number_or_keyword {
            Ok((None, LexAction::TakePoeticNumber))
        } else if COMMON_VAR.is_match(word) {
            let tok = Token::CommonVar(word.into());
            Ok((Some(tok), LexAction::NoAction))
        } else if PROPER_VAR_WORD.is_match(word) {
            Ok((None, LexAction::TakeProperVar))
        } else {
            Err(LexicalError::UnexpectedInput(self.idx, self.idx))
        }
    }

    fn handle_action(&self, action: LexAction)
        -> Result<Option<(usize, usize, Token, Option<TCtx>)>, LexicalError>
    {
        match action {
            LexAction::NoAction | LexAction::CheckKeywordOrPoeticString => Ok(None),
            LexAction::TakePoeticString => {
                // Spec says we need one literal space here
                if self.next_char() != Some(' ') {
                    return Err(LexicalError::UnexpectedInput(self.idx, self.idx + 1))
                }

                let skip = 1;

                let (end, tok) = {
                    let (content, end) = self.capture_to_end_of_line_from(skip);
                    let tok = Token::StringLiteral(content.into());
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
                    let next_end = match PROPER_VAR_WORD.find(&more[skip..]) {
                        Some(m) => skip + m.end(),
                        None => break,
                    };

                    if self.match_special_word(&more[skip..next_end]).is_some() {
                        break;
                    }

                    var_end += next_end;
                }

                let var = self.rest()[..var_end].to_owned();
                Ok(Some((0, var.len(), Token::ProperVar(var), None)))
            }
        }
    }

    fn match_special_word(&self, word: &str) -> Option<Token> {
        let tok = match word.to_lowercase().as_str() {
            "a" | "an" | "the" | "my" | "your" => {
                Token::CommonPrep(word.into())
            }
            "it" | "he" | "she" | "him" | "her" | "them" | "they" => {
                Token::Pronoun(word.into())
            }

            "mysterious" => Token::MysteriousLiteral,
            "null" | "nothing" | "nowhere" | "nobody" => Token::NullLiteral,

            "true" | "right" | "yes" | "ok" => Token::BooleanLiteral(true),
            "false" | "wrong" | "no" | "lies" => Token::BooleanLiteral(false),

            "is" => Token::Is,
            "was" | "were" => Token::Was,
            "not" => Token::Not,

            "as" => Token::As,
            "than" => Token::Than,

            "higher" | "greater" | "bigger" | "stronger" => Token::Greater,
            "lower" | "less" | "smaller" | "weaker" => Token::Less,

            "high" | "great" | "big" | "strong" => Token::Great,
            "low" | "little" | "small" | "weak" => Token::Little,

            "put" => Token::Put,
            "into" => Token::Into,

            "build" => Token::Build,
            "up" => Token::Up,

            "knock" => Token::Knock,
            "down" => Token::Down,

            "plus" | "with" => Token::Plus,
            "minus" | "without" => Token::Minus,
            "times" | "of" => Token::Times,
            "over" | "by" => Token::Over,

            "listen" => Token::Listen,
            "to" => Token::To,

            "say" | "shout" | "whisper" | "scream" => Token::Say,
            "says" => Token::Says,

            "if" => Token::If,
            "while" => Token::While,
            "until" => Token::Until,

            "continue" => Token::Continue,
            "break" => Token::Break,

            "takes" => Token::Takes,
            "taking" => Token::Taking,

            "take" => Token::Take,
            "from" => Token::From,

            "give" => Token::Give,
            "back" => Token::Back,

            "and" => Token::And,
            "or" => Token::Or,

            _ => return None,
        };
        Some(tok)
    }

    fn compute_poetic_number(&self) -> (RockstarNumber, usize) {
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

        let significand = significand.unwrap_or(counts.len()) as i32;
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

    fn capture_to_end_of_line_from(&self, idx: usize) -> (&str, usize) {
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
    use super::{LexicalError, Token, Tokenizer};

    fn toks<S>(input: S) -> Vec<(usize, Token, usize)>
        where S: Into<String>
    {
        let tokenizer = Tokenizer::new(input.into());
        tokenizer.tokenize().collect::<Result<Vec<_>, _>>().unwrap()
    }

    fn tok_err<S>(input: S) -> LexicalError
        where S: Into<String>
    {
        let tokenizer = Tokenizer::new(input.into());
        tokenizer.tokenize().collect::<Result<Vec<_>, _>>().unwrap_err()
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

        assert_eq!(toks(input), expected);
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

        assert_eq!(toks(input), expected);
    }

    #[test]
    fn drop_commas_before_eol() {
        let input = "its very,,,\n,,\ninteresting, indeed,";
        //           012345678901 234 56789012345678901234

        assert_eq!(toks(input), vec![
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
    fn lexing_errors() {
        assert_eq!(tok_err("abc忠犬ハチ公"), LexicalError::UnexpectedInput(0, 0));
        assert_eq!(tok_err("aSciIbuTNotAccEptaBlE"),
                   LexicalError::UnexpectedInput(0, 0));
        assert_eq!(tok_err("my friend says\u{205F}okay"),
                   LexicalError::UnexpectedInput(14, 15));
    }

    #[test]
    fn parse_proper_var() {
        let input = "If Johnny B Goode Right";
        //           01234567890123456789012

        let expected = vec![
            (0, Token::If, 2),
            (3, Token::ProperVar("Johnny B Goode".into()), 17),
            (18, Token::BooleanLiteral(true), 23),
            (23, Token::Newline, 23),
            (23, Token::EOF, 23),
        ];

        assert_eq!(toks(input), expected);
    }

    #[test]
    fn parse_poetic_string() {
        let input = "Johnny says  忠犬ハチ公,,";
        //           0123456789012..

        let end = input.len();

        let base = vec![
            (0, Token::ProperVar("Johnny".into()), 6),
            (7, Token::Says, 11),
            (12, Token::StringLiteral(" 忠犬ハチ公,,".into()), end),
        ];

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end),
            (end, Token::EOF, end),
        ]);

        assert_eq!(toks(input), expected, "no EOL");

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end + 1),
            (end + 1, Token::EOF, end + 1),
        ]);

        assert_eq!(toks(input.to_owned() + "\n"), expected, "with EOL");
    }

    #[test]
    fn parse_poetic_number() {
        let input = "My dreams were     ice. A life unfulfilled; \
                     wakin' everybody up, taking booze and pills";

        let end = input.len();

        let base = vec![
            (0, Token::CommonPrep("My".into()), 2),
            (3, Token::CommonVar("dreams".into()), 9),
            (10, Token::Was, 14),
            (19, Token::NumberLiteral(3.1415926535), end),
        ];

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end),
            (end, Token::EOF, end),
        ]);

        assert_eq!(toks(input), expected, "no EOL");

        let expected = extend_vec!(base, vec![
            (end, Token::Newline, end + 1),
            (end + 1, Token::EOF, end + 1),
        ]);

        assert_eq!(toks(input.to_owned() + "\n"), expected, "with EOL");
    }

    #[test]
    fn parse_literal_number() {
        assert_eq!(toks("0.2")[0], (0, Token::NumberLiteral(0.2), 3));
        assert_eq!(toks(".2")[0], (0, Token::NumberLiteral(0.2), 2));
        assert_eq!(toks("100")[0], (0, Token::NumberLiteral(100.0), 3));
    }

    #[test]
    fn parse_long_loop_controls() {
        assert_eq!(toks("Take it to the top")[0], (0, Token::Continue, 18));
        assert_eq!(toks("Break it down")[0], (0, Token::Break, 13));
    }
}
