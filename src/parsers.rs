use once_cell::sync::Lazy;
use regex::Regex;

// Parser<T> を Fn(&str) -> Option<(T, &str)> の別名(のようなもの)として定義する。
pub trait Parser<T>: Fn(&str) -> Option<(T, &str)> {}
impl<T, F> Parser<T> for F where F: Fn(&str) -> Option<(T, &str)> {}

// クロージャの型推論を補助するための関数
// cf. https://github.com/rust-lang/rust/issues/70263#issuecomment-623169045
fn generalize_lifetime<T, F>(f: F) -> F
where
    F: Fn(&str) -> Option<(T, &str)>,
{
    f
}

// s の先頭にある整数をパースし、整数値と残りの文字列を返す。
// パースに失敗した場合は None を返す。
pub fn digits(s: &str) -> Option<(i64, &str)> {
    let end = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
    match s[..end].parse() {
        Ok(value) => Some((value, &s[end..])),
        Err(_) => None,
    }
}

#[test]
fn test_digits() {
    assert_eq!(digits("123"),         Some((123, "")));
    assert_eq!(digits("123 hello"),   Some((123, " hello")));
    assert_eq!(digits("hello world"), None);
    assert_eq!(digits(""),            None);
}

// 先頭の一文字が c であるときに成功して () を返すようなパーサーを返す。
pub fn character(c: char) -> impl Parser<()> {
    generalize_lifetime(move |s| {
        let mut chars = s.chars();
        if chars.next() == Some(c) {
            Some(((), chars.as_str()))
        } else {
            None
        }
    })
}

#[test]
fn test_character() {
    let parser = character('🍰');
    assert_eq!(parser("🍰 yey!"), Some(((), " yey!")));
    assert_eq!(parser("no cake"), None);
    assert_eq!(parser(""), None);
}

// パーサーを受け取って、先頭の空白を読み飛ばすようにしたパーサーを返す
pub fn lexeme<T>(parser: impl Parser<T>) -> impl Parser<T> {
    generalize_lifetime(move |s| {
        parser(s.trim_start())
    })
}

#[test]
fn test_lexeme() {
    let parser = lexeme(digits);
    assert_eq!(parser("    123    hello"), Some((123, "    hello")));
}

pub fn string<'a>(target: &'a str) -> impl Parser<()> + 'a {
    generalize_lifetime(move |s| {
        s.strip_prefix(target).map(|rest| ((), rest))
    })
}

#[test]
fn test_string() {
    let parser = string("hello");
    assert_eq!(parser("hello world"), Some(((), " world")));
    assert_eq!(parser("hell world"), None);
}

pub fn map<A, B>(
    parser: impl Parser<A>,
    f: impl Fn(A) -> B,
) -> impl Parser<B> {
    generalize_lifetime(move |s| {
        parser(s).map(|(value, rest)| (f(value), rest))
    })
}

#[test]
fn test_map() {
    let parser = map(digits, |x| x + 1);
    assert_eq!(parser("1"), Some((2, "")));
    assert_eq!(parser("X"), None);
}

pub fn choice<T>(
    parser1: impl Parser<T>,
    parser2: impl Parser<T>,
) -> impl Parser<T> {
    generalize_lifetime(move |s| {
        parser1(s).or_else(|| parser2(s))
    })
}

#[test]
fn test_choice() {
    let parser = choice(
        digits,
        map(string("null"), |_| 0),
    );
    assert_eq!(parser("1234"), Some((1234, "")));
    assert_eq!(parser("null"), Some((0, "")));
    assert_eq!(parser("hoge"), None);
}

#[macro_export]
macro_rules! choice {
    ($parser0:expr, $($parser:expr),*) => {{
        let p = $parser0;
        $(
            let p = $crate::parsers::choice(p, $parser);
        )*
        p
    }};
}

#[test]
fn test_choice_macro() {
    let parser = choice![
        map(string("zero"), |_| 0),
        map(string("one"),  |_| 1),
        digits
    ];
    assert_eq!(parser("zero"), Some((0,  "")));
    assert_eq!(parser("one"),  Some((1,  "")));
    assert_eq!(parser("42"),   Some((42, "")));
    assert_eq!(parser("hoge"), None);
}

pub fn join<A, B>(
    parser1: impl Parser<A>,
    parser2: impl Parser<B>,
) -> impl Parser<(A, B)> {
    generalize_lifetime(move |s| {
        parser1(s).and_then(|(value1, rest1)| {
            parser2(rest1).map(|(value2, rest2)| {
                ((value1, value2), rest2)
            })
        })
    })
}

#[test]
fn test_join() {
    let plus_minus = choice(
        map(character('+'), |_| '+'),
        map(character('-'), |_| '-'),
    );
    // 符号付き整数パーサー
    let parser = join(plus_minus, digits);   
    assert_eq!(parser("+123"), Some((('+', 123), "")));
    assert_eq!(parser("-123"), Some((('-', 123), "")));
    assert_eq!(parser("-abc"), None);
    assert_eq!(parser("*123"), None);
}

#[macro_export]
macro_rules! join {
    ($parser0:expr, $($parser:expr),*) => {{
        let p = $parser0;
        $(
            let p = $crate::parsers::join(p, $parser);
        )*
        p
    }};
}

#[test]
fn test_join_macro() {
    // スペース区切りで数値をちょうど3つ受け付けるパーサー
    let parser = join![
        lexeme(digits),
        lexeme(digits),
        lexeme(digits)
    ];
    assert_eq!(parser("10 20 30"), Some((((10, 20), 30), "")));
    assert_eq!(parser("10 20 AA"), None);
}

pub fn many<T>(parser: impl Parser<T>) -> impl Parser<Vec<T>> {
    generalize_lifetime(move |mut s| {
        let mut ret = vec![];
        while let Some((value, rest)) = parser(s) {
            ret.push(value);
            s = rest;
        }
        Some((ret, s))
    })
}

#[test]
fn test_many() {
    let parser = many(lexeme(digits));
    assert_eq!(parser("10 20 30"), Some((vec![10, 20, 30], "")));
    assert_eq!(parser(""),         Some((vec![], "")));
    assert_eq!(parser("10 hello"), Some((vec![10], " hello")));
}

pub fn separated<T>(
    parser: impl Parser<T>,
    separator: impl Parser<()>,
) -> impl Parser<Vec<T>> {
    generalize_lifetime(move |mut s| {
        let mut ret = vec![];

        match parser(s) {
            Some((value, rest)) => {
                ret.push(value);
                s = rest;
            }
            None => {
                return Some((ret, s));
            }
        }

        while let Some((_, rest)) = separator(s) {
            s = rest;
            match parser(s) {
                Some((value, rest)) => {
                    ret.push(value);
                    s = rest;
                }
                None => {
                    return None;
                }
            }
        }

        Some((ret, s))
    })
}

#[test]
fn test_separated() {
    // カンマ区切りの数値の列のパーサー
    let parser = separated(digits, character(','));
    assert_eq!(parser("1,2,3"), Some((vec![1, 2, 3], "")));
    assert_eq!(parser(""),      Some((vec![],        "")));
}

pub fn regex<'a, T>(
    re: &'a Regex,
    f: impl Fn(&str) -> Option<T> + 'a,
) -> impl Parser<T> + 'a {
    generalize_lifetime(move |s| {
        re.find(s).and_then(|matched| {
            f(matched.as_str()).map(|value| {
                let rest = &s[matched.end()..];
                (value, rest)
            })
        })
    })
}

#[test]
fn test_regex() {
    // 識別子っぽい文字列をパース
    const PATTERN: &str = r"^[a-zA-Z_][a-zA-Z0-9_]*";
    static RE: Lazy<Regex> = Lazy::new(|| Regex::new(PATTERN).unwrap());
    let parser = regex(&RE, |s| Some(s.to_owned()));
    assert_eq!(parser("x_1=0"), Some(("x_1".to_owned(), "=0")));
    assert_eq!(parser("0_1=0"), None);
}

#[macro_export]
macro_rules! regex {
    ($pattern:expr, $f:expr) => {{
        use regex::Regex;
        use once_cell::sync::Lazy;
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new($pattern).unwrap());
        $crate::parsers::regex(&RE, $f)
    }};
}

#[test]
fn test_regex_macro() {
    let parser = regex!(r"^[a-zA-Z_][a-zA-Z0-9_]*", |s| Some(s.to_owned()));
    assert_eq!(parser("x_1=0"), Some(("x_1".to_owned(), "=0")));
    assert_eq!(parser("0_1=0"), None);
}
