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
