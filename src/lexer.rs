use std::io::{self, Read};
use std::fmt;

use regex::Regex;

#[derive(Debug)]
pub enum LexicalError {
    // TODO
}

impl fmt::Display for LexicalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "lexical error")
    }
}

// FIXME: Spec calls for DEC64
pub type RockstarNumber = f64;

#[derive(Debug, PartialEq)]
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

    fn is_literal(&self) -> bool {
        use self::Token::*;

        match *self {
            StringLiteral(_) |
            NumberLiteral(_) |
            BooleanLiteral(_) |
            MysteriousLiteral |
            NullLiteral => true,
            _ => false,
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
            Token::NumberLiteral(_) => unimplemented!(),
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

fn string_starts<F>(word: &str, pred: F) -> bool where F: Fn(char) -> bool {
    match word.chars().next() {
        Some(c) => pred(c),
        None => false,
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

pub struct Tokenizer {
    content: String,
    idx: usize,
    ctx: TCtx,
    line_begins_with_keyword: bool,
}

impl Tokenizer {
    pub fn new(content: String) -> Self {
        let mut ctx = TCtx::default();
        ctx.at_start = true;
        Tokenizer {
            content,
            idx: 0,
            ctx,
            line_begins_with_keyword: false,
        }
    }

    pub fn from_file<R: Read>(source: &mut R) -> io::Result<Self> {
        let mut content = String::new();
        source.read_to_string(&mut content)?;
        Ok(Self::new(content))
    }

    pub fn get_location(&self, start: usize, end: usize) -> (&str, usize, usize, usize) {
        let mut line_start = 0;
        let mut lineno = 1;

        for (i, b) in self.content[..start].bytes().enumerate() {
            if b == b'\n' {
                line_start = i + 1;
                lineno += 1;
            }
        }

        let line_end = self.content[end..]
            .find('\n')
            .map_or(self.content.len(), |i| i + end);

        (&self.content[line_start..line_end], lineno, start - line_start, end - line_start)
    }

    pub fn tokenize(&mut self) -> Vec<(usize, Token, usize)> {
        let mut toks = vec![];

        if !self.has_more() {
            panic!("tokenize() called repeatedly");
        }

        while self.has_more() {
            toks.extend(self.take_more());
        }

        drop_trailing_commas(&mut toks);

        toks
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

    fn take_more(&mut self) -> Vec<(usize, Token, usize)> {
        if !self.has_more() {
            panic!("take_more() called after EOF")
        }

        let mut extent;

        loop {
            extent = self.content[self.idx..].find(|c: char| {
                !(('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z'))
            });

            if extent != Some(0) {
                break;
            }

            let non_alpha = self.content[self.idx..].chars().next().expect("non-alpha");

            if non_alpha == '"' {
                let start = self.idx + 1;

                if let Some(n) = self.content[start..].find('"') {
                    let tok = {
                        let out = &self.content[start..start + n];
                        Token::StringLiteral(out.into())
                    };
                    // length is n + delimiters
                    return vec![self.emit(n + 2, tok, None)];
                } else {
                    panic!("Unmatched string opening from {}", self.idx);
                }
            }

            let single_char_tok = match non_alpha {
                '\n' => Some(Token::Newline),
                ',' => Some(Token::Comma),
                _ if non_alpha.is_whitespace() => None,
                _ => panic!("Unexpected character '{}'", non_alpha),
            };

            if let Some(tok) = single_char_tok {
                let mut ctx = TCtx::default();
                if tok == Token::Newline {
                    ctx.prev_was_eol = true;
                }
                return vec![self.emit(1, tok, Some(ctx))];
            }

            self.idx += 1;
        }

        let word_len = match extent {
            Some(n) => n,
            None => {
                if self.idx == self.content.len() {
                    return self.emit_eof();
                }
                self.idx - (self.content.len() - 1)
            }
        };

        let mut ctx = TCtx::default();
        let mut take_poetic_string = false;
        let mut take_poetic_number = false;

        let tok =
            self.prepare_keyword(word_len,
                                 &mut ctx,
                                 &mut take_poetic_string,
                                 &mut take_poetic_number);

        let mut to_emit = vec![];

        if let Some(tok) = tok {
            to_emit.push(self.emit(word_len, tok, Some(ctx)));
        }

        if take_poetic_string {
            unimplemented!("poetic string");
        }

        if take_poetic_number {
            unimplemented!("poetic number");
        }

        to_emit
    }

    fn prepare_keyword(&self,
                       word_len: usize,
                       ctx: &mut TCtx,
                       take_poetic_string: &mut bool,
                       take_poetic_number: &mut bool)
        -> Option<Token>
    {
        let out = &self.content[self.idx..self.idx + word_len];

        if let Some(keyword) = self.match_keyword(out) {
            if self.ctx.poetic_number_or_keyword {
                // XXX: Need to make terminology better
                if !keyword.is_keyword() {
                    *take_poetic_number = true;
                    return None;
                }
            }

            match keyword {
                Token::Says => { *take_poetic_string = true }
                Token::Was => { *take_poetic_number = true }
                Token::Is => {
                    ctx.poetic_number_or_keyword = !self.line_begins_with_keyword;
                }
                _ => {}
            }

            return Some(keyword);
        }

        if self.ctx.poetic_number_or_keyword {
            *take_poetic_number = true;
            return None;
        }

        if string_starts(out, char::is_lowercase) {
            // FIXME: Must be all lower case
            Some(Token::CommonVar(out.into()))
        } else {
            // FIXME: This isn't right
            Some(Token::ProperVar(out.into()))
        }
    }

    fn match_keyword(&self, word: &str) -> Option<Token> {
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
}

/// Hack: Drop commas before EOL (can't be handled in parsing without ambiguity)
fn drop_trailing_commas(toks: &mut Vec<(usize, Token, usize)>) {
    let tok_kinds: Vec<_> = toks.iter()
        .map(|&(_, ref t, _)| (t == &Token::Comma, t == &Token::Newline))
        .collect();

    let mut prev_was_comma = false;
    for (i, (is_comma, is_newline)) in tok_kinds.into_iter().enumerate() {
        if is_newline {
            if prev_was_comma {
                toks.remove(i - 1);
            }
        }
        prev_was_comma = is_comma;
    }
}
