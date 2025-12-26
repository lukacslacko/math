use crate::lexer::{PREFIXES, Token, tokenize};
use std::fmt::Write;

pub fn format_file(input_file: &str, output_file: &str) {
    let tokens = tokenize(
        &std::fs::read_to_string(input_file)
            .expect("Failed to read input file"),
        input_file,
    );
    write_formatted_file(&tokens, output_file);
}

pub fn write_formatted_file(tokens: &[Token], output_file: &str) {
    let nice_tokens = [
        ("/", " / "),
        ("⊦", "⊦ "),
        ("≔", " ≔ "),
        ("⇒", " ⇒ "),
        ("⤷", "⤷ "),
        ("⤶", "⤶ "),
        ("℻", " ℻ "),
        ("+", " + "),
        ("*", " * "),
        ("=", " = "),
        (";", "; "),
        ("|", " | "),
        ("⇆", " ⇆"),
        ("⪮", "⪮"),
        ("↺", "↺"),
    ];

    let mut depth = 0;
    let max_line = tokens.iter().map(|t| t.line_no).max().unwrap_or(1);

    let mut output = String::new();

    for line in 1..=max_line {
        let line_tokens: Vec<&Token> =
            tokens.iter().filter(|t| t.line_no == line).collect();
        if line_tokens.is_empty() {
            writeln!(output).unwrap();
            continue;
        }
        let first_token = &line_tokens[0];
        if first_token.text == "}"
            || first_token.text == "⟫"
            || first_token.text == "⟧"
        {
            depth -= 1;
        }
        for _ in 0..depth {
            write!(output, "    ").unwrap();
        }
        let mut previous_token_was_special = true;
        let mut is_first_token = true;
        for token in line_tokens {
            let token_text = &token.text;
            if PREFIXES.iter().any(|(_, symbol)| *symbol == *token_text) {
                let nice_text = nice_tokens
                    .iter()
                    .find(|(orig, _)| *orig == token_text)
                    .map(|(_, nice)| *nice)
                    .unwrap_or(token_text);
                write!(output, "{}", nice_text).unwrap();
                previous_token_was_special = true;
            } else {
                if !previous_token_was_special {
                    write!(output, " ").unwrap();
                }
                write!(output, "{}", token_text).unwrap();
                previous_token_was_special = false;
            }
            if token.text == "{" || token.text == "⟪" || token.text == "⟦" {
                depth += 1;
            }
            if (token.text == "}" || token.text == "⟫" || token.text == "⟧")
                && !is_first_token
            {
                depth -= 1;
            }
            is_first_token = false;
        }
        writeln!(output).unwrap();
    }
    std::fs::write(output_file, output).expect("Failed to write to file");
}
