use std::cmp::Ordering;

use syntax::lexer::NEWLINE_SEARCH;

#[derive(Debug, PartialEq, Clone)]
pub struct IntraLineSpan<'a> {
    pub line: &'a str,
    pub lineno: usize,
    pub start: usize,
    pub end: usize,
    __private: (),
}

impl<'a> IntraLineSpan<'a> {
    pub fn leading_chars(&self) -> usize {
        self.line[..self.start].chars().count()
    }

    pub fn spanned_chars(&self) -> usize {
        self.line[self.start..self.end].chars().count()
    }
}

pub(super) struct SourceLocator {
    line_locations: Vec<(usize, usize)>,
}

impl SourceLocator {
    pub(super) fn new(content: &str) -> Self {
        let mut start = 0;
        let mut locs = Vec::new();
        for m in NEWLINE_SEARCH.find_iter(content) {
            locs.push((start, m.start()));
            start = m.end();
        }
        // By design, this gives a (0, 0) range for an empty string
        locs.push((start, content.len()));

        SourceLocator {
            line_locations: locs,
        }
    }

    pub(super) fn get_line_at_idx<'a>(&self, content: &'a str, idx: usize) -> &'a str {
        let (line_start, line_end) = self.line_locations[idx];
        &content[line_start..line_end]
    }

    pub(super) fn get_line_idx(&self, point: usize) -> usize {
        let searcher = |&(a, b)| if a <= point && point <= b {
            Ordering::Equal
        } else if point < a {
            Ordering::Greater
        } else {
            Ordering::Less
        };

        match self.line_locations.binary_search_by(searcher) {
            Ok(i) => i,
            Err(i) => if i < self.line_locations.len() {
                i
            } else {
                self.line_locations.len() - 1
            },
        }
    }

    pub(super) fn get_line_span<'a>(&self, content: &'a str, start: usize, end: usize)
        -> IntraLineSpan<'a>
    {
        let line_idx = self.get_line_idx(start);
        let (line_start, line_end) = self.line_locations[line_idx];

        let mut char_start = start;

        if char_start > line_end {
            char_start = line_end;
        } else {
            while !content.is_char_boundary(char_start) {
                char_start -= 1;
            }
        }

        let mut char_end = end;

        if char_end > line_end {
            char_end = line_end;
        } else {
            while !content.is_char_boundary(char_end) {
                char_end += 1;
            }
        }

        IntraLineSpan {
            line: self.get_line_at_idx(content, line_idx),
            lineno: line_idx + 1,
            start: char_start - line_start,
            end: char_end - line_start,
            __private: ()
        }
    }
}

#[cfg(test)]
mod test {
    use super::{SourceLocator, IntraLineSpan};

    #[test]
    fn newline_bounds() {
        let src = "abc\ndef";
        let loc = SourceLocator::new(src);

        assert_eq!(loc.get_line_span(src, 0, 0), IntraLineSpan {
            line: "abc",
            lineno: 1,
            start: 0,
            end: 0,
            __private: (),
        });

        assert_eq!(loc.get_line_span(src, 0, 3), IntraLineSpan {
            line: "abc",
            lineno: 1,
            start: 0,
            end: 3,
            __private: (),
        });

        assert_eq!(loc.get_line_span(src, 3, 4), IntraLineSpan {
            line: "abc",
            lineno: 1,
            start: 3,
            end: 3,
            __private: (),
        });

        assert_eq!(loc.get_line_span(src, 4, 4), IntraLineSpan {
            line: "def",
            lineno: 2,
            start: 0,
            end: 0,
            __private: (),
        });

        assert_eq!(loc.get_line_span(src, 4, 8), IntraLineSpan {
            line: "def",
            lineno: 2,
            start: 0,
            end: 3,
            __private: (),
        });

        assert_eq!(loc.get_line_span(src, 7, 8), IntraLineSpan {
            line: "def",
            lineno: 2,
            start: 3,
            end: 3,
            __private: (),
        });
    }

    #[test]
    fn char_bounds() {
        let src = "忠犬ハチ公";
        let loc = SourceLocator::new(src);

        assert_eq!(loc.get_line_span(src, 1, 2), IntraLineSpan {
            line: "忠犬ハチ公",
            lineno: 1,
            start: 0,
            end: src.chars().next().unwrap().len_utf8(),
            __private: (),
        });
    }
}
