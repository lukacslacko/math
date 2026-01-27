#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub text: String,
    pub location: String,
    pub line_no: usize,
}

pub const PREFIXES: &[(&str, &str)] = &[
    ("/*", "/*"),
    ("*/", "*/"),
    (";", ";"),
    ("●", "●"),
    ("<arg>", "●"),
    ("↵", "↵"),
    ("λ", "λ"),
    ("[", "["),
    ("]", "]"),
    ("⊦", "⊦"),
    ("|-", "⊦"),
    (":=", "≔"),
    ("≔", "≔"),
    ("≠", "≠"),
    ("!=", "≠"),
    ("/", "/"),
    ("⇒", "⇒"),
    ("=>", "⇒"),
    ("->", "⇒"),
    ("<=>", "⇔"),
    ("⇔", "⇔"),
    ("<->", "⇔"),
    ("≤", "≤"),
    ("<=", "≤"),
    (".<", "↙"),
    ("↙", "↙"),
    (".v", "↓"),
    ("↓", "↓"),
    (".>", "↘"),
    ("↘", "↘"),
    (".", "."),
    ("=", "="),
    ("+", "+"),
    ("*", "*"),
    ("!", "∀"),
    ("∀", "∀"),
    ("?", "∃"),
    ("∃", "∃"),
    ("(", "("),
    (")", ")"),
    ("¬", "¬"),
    ("~", "¬"),
    ("⁇", "⁇"),
    ("𝗦", "𝗦"),
    ("{", "{"),
    ("}", "}"),
    ("⤷", "⤷"),
    ("⤶", "⤶"),
    ("|", "|"),
    ("∣", "∣"),
    ("⇆", "⇆"),
    ("↶", "↶"),
    ("⪮", "⪮"),
    ("↺", "↺"),
    ("✂", "✂"),
    ("⇅", "⇅"),
    ("ⅰ", "ⅰ"),
    ("ⅱ", "ⅱ"),
    ("ⅲ", "ⅲ"),
    ("ⅳ", "ⅳ"),
    ("ⅴ", "ⅴ"),
    ("⛔", "⛔"),
    ("📜", "📜"),
    ("<S>", "𝗦"),
    ("<div>", "∣"),
    ("<distribute>", "⇆"),
    ("<eq_subs>", "⪮"),
    ("<induction>", "↺"),
    ("<cut>", "✂"),
    ("<match>", "⇅"),
    ("<stop>", "⛔"),
    ("<proof>", "📜"),
    ("<prove>", "⁇"),
    ("<prev>", "↶"),
    ("<1>", "ⅰ"),
    ("<2>", "ⅱ"),
    ("<3>", "ⅲ"),
    ("<4>", "ⅳ"),
    ("<5>", "ⅴ"),
    ("<", "<"),
];

pub const KEYWORDS: &[(&str, &str)] = &[
    ("export", "⤶"),
    ("import", "⤷"),
    ("FAX", "℻"),
    ("return", "↵"),
    ("lambda", "λ"),
    ("or", "∨"),
    ("and", "∧"),
];

fn tokenize_word(
    word: &str,
    filename: &str,
    line_no: usize,
    codepoint_index: usize,
) -> Vec<Token> {
    let location = format!("{filename}:{line_no}:{codepoint_index}");

    // Empty word, no tokens.
    if word.is_empty() {
        return vec![];
    }

    let mut tokens = Vec::new();

    // Is the word equal to any keyword?
    for (keyword, symbol) in KEYWORDS.iter() {
        if word == *keyword {
            tokens.push(Token {
                text: symbol.to_string(),
                location: location.clone(),
                line_no,
            });
            return tokens;
        }
    }

    // Does the word start with any tokens?
    for (prefix, symbol) in PREFIXES.iter() {
        if let Some(rest) = word.strip_prefix(prefix) {
            tokens.push(Token {
                text: symbol.to_string(),
                location: location.clone(),
                line_no,
            });
            tokens.extend(tokenize_word(
                rest,
                filename,
                line_no,
                codepoint_index + prefix.chars().count(),
            ));
            return tokens;
        }
    }

    // No known token found as prefix, gather characters until one is found or the word ends.
    let mut current_token = String::new();
    for (start_byte, ch) in word.char_indices() {
        current_token.push(ch);

        // Does the remaining part start with any prefix?
        let rest = &word[start_byte + ch.len_utf8()..];
        let mut matched_prefix = false;
        for (prefix, _) in PREFIXES.iter() {
            if rest.starts_with(prefix) {
                matched_prefix = true;
                break;
            }
        }
        if matched_prefix {
            break;
        }
    }
    if !current_token.is_empty() {
        if let Some((_, symbol)) = KEYWORDS
            .iter()
            .find(|(keyword, _)| current_token == *keyword)
        {
            tokens.push(Token {
                text: symbol.to_string(),
                location: location.clone(),
                line_no,
            });
        } else {
            tokens.push(Token {
                text: current_token.clone(),
                location: location.clone(),
                line_no,
            });
        }
    }
    let rest = &word[current_token.len()..];
    tokens.extend(tokenize_word(
        rest,
        filename,
        line_no,
        codepoint_index + current_token.chars().count(),
    ));

    tokens
}

fn tokenize_line(line: &str, filename: &str, line_no: usize) -> Vec<Token> {
    let mut tokens = Vec::new();

    let mut codepoint_index = 0; // 0-based Unicode codepoint index
    let mut iter = line.char_indices().peekable();

    while let Some((start_byte, ch)) = iter.next() {
        let is_ws = ch.is_whitespace();
        let start_codepoint = codepoint_index;

        codepoint_index += 1;

        if is_ws {
            continue;
        }

        let mut end_byte = start_byte + ch.len_utf8();

        while let Some(&(next_byte, next_ch)) = iter.peek() {
            if next_ch.is_whitespace() {
                break;
            }
            iter.next();
            end_byte = next_byte + next_ch.len_utf8();
            codepoint_index += 1;
        }

        let word = &line[start_byte..end_byte];

        tokens.extend(tokenize_word(word, filename, line_no, start_codepoint));
    }

    tokens
}

pub fn tokenize(input: &str, filename: &str) -> Vec<Token> {
    input
        .lines()
        .enumerate()
        .flat_map(|(line_no, line)| tokenize_line(line, filename, line_no + 1))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(text: &str, line: usize, col: usize) -> Token {
        Token {
            text: text.to_string(),
            location: format!("test_input.ll:{line},{col}"),
            line_no: line,
        }
    }

    #[test]
    fn test_tokenize_example_ll() {
        let input = include_str!("test_input.ll");
        let tokens = tokenize(input, "test_input.ll");
        let expected = vec![
            // Line 1
            t("ignore", 1, 0),
            t("≔", 1, 7),
            t("'A", 1, 9),
            t("⇒", 1, 12),
            t("'B", 1, 14),
            t("⇒", 1, 17),
            t("'A", 1, 19),
            //
            // Line 2
            t("distr", 2, 0),
            t("≔", 2, 6),
            t("(", 2, 8),
            t("'A", 2, 9),
            t("⇒", 2, 12),
            t("'B", 2, 14),
            t("⇒", 2, 17),
            t("'C", 2, 19),
            t(")", 2, 21),
            t("⇒", 2, 23),
            t("(", 2, 25),
            t("'A", 2, 26),
            t("⇒", 2, 29),
            t("'B", 2, 31),
            t(")", 2, 33),
            t("⇒", 2, 35),
            t("'A", 2, 37),
            t("⇒", 2, 40),
            t("'C", 2, 42),
            //
            // Line 3
            t("ignore", 3, 0),
            t("[", 3, 6),
            t("'A", 3, 7),
            t("/", 3, 10),
            t("'x", 3, 12),
            t("]", 3, 14),
            t("[", 3, 15),
            t("'B", 3, 16),
            t("/", 3, 19),
            t("'x", 3, 21),
            t("⇒", 3, 24),
            t("'x", 3, 26),
            t("]", 3, 28),
            //
            // Line 4
            t("ignore", 4, 0),
            t("[", 4, 6),
            t("'A", 4, 7),
            t("/", 4, 10),
            t("'x", 4, 12),
            t("]", 4, 14),
            t("[", 4, 15),
            t("'B", 4, 16),
            t("/", 4, 19),
            t("'x", 4, 21),
            t("]", 4, 23),
            //
            // Line 5
            t("distr", 5, 0),
            t("[", 5, 5),
            t("'A", 5, 6),
            t("/", 5, 9),
            t("'x", 5, 11),
            t("]", 5, 13),
            t("[", 5, 14),
            t("'B", 5, 15),
            t("/", 5, 18),
            t("'x", 5, 20),
            t("⇒", 5, 23),
            t("'x", 5, 25),
            t("]", 5, 27),
            t("[", 5, 28),
            t("'C", 5, 29),
            t("/", 5, 32),
            t("'x", 5, 34),
            t("]", 5, 36),
            t(".", 5, 37),
            t("MP", 5, 38),
            t(".", 5, 40),
            t("MP", 5, 41),
            //
            // Line 6
            t("1", 6, 0),
            t("≔", 6, 2),
            t("𝗦", 6, 5),
            t("(", 6, 9),
            t("0", 6, 10),
            t(")", 6, 11),
            //
            // Line 7
            t("⊦", 7, 0),
            t("'x", 7, 3),
            t("⇒", 7, 6),
            t("'x", 7, 8),
        ];
        assert_eq!(tokens, expected);
    }
}
