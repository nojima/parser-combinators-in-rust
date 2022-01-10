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
pub fn character(c: char) -> impl Fn(&str) -> Option<((), &str)> {
    move |s| {
        let mut chars = s.chars();
        if chars.next() == Some(c) {
            Some(((), chars.as_str()))
        } else {
            None
        }
    }
}

#[test]
fn test_character() {
    let parser = character('🍰');
    assert_eq!(parser("🍰 yey!"), Some(((), " yey!")));
    assert_eq!(parser("no cake"), None);
    assert_eq!(parser(""), None);
}
