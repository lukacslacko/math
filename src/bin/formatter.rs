use core::panic;

use math::lexer::tokenize;
use std::fmt::Write;

// Run with cargo run --bin formatter [input_file]
fn main() {
    // Select input file from command line arguments.
    let args: Vec<String> = std::env::args().collect();
    let input_file = if args.len() == 2 {
        &args[1]
    } else {
        panic!("Usage: formatter [input_file]");
    };

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
        ("⪮", " ⪮"),
        ("↺", " ↺"),
    ];

    let tokens = tokenize(
        &std::fs::read_to_string(input_file)
            .expect("Failed to read input file"),
        input_file,
    );
    let mut depth = 0;
    let max_line = tokens.iter().map(|t| t.line_no).max().unwrap_or(1);

    let mut output = String::new();

    for line in 1..=max_line {
        let line_tokens: Vec<&math::lexer::Token> =
            tokens.iter().filter(|t| t.line_no == line).collect();
        if line_tokens.is_empty() {
            writeln!(output).unwrap();
            continue;
        }
        let first_token = &line_tokens[0];
        if first_token.text == "}" {
            depth -= 1;
        }
        for _ in 0..depth {
            write!(output, "    ").unwrap();
        }
        let mut prev_token: Option<&math::lexer::Token> = None;
        for token in line_tokens {
            let token_text = &token.text;
            let nice_text = nice_tokens
                .iter()
                .find(|(orig, _)| *orig == token_text)
                .map(|(_, nice)| *nice)
                .unwrap_or(token_text);
            write!(output, "{}", nice_text).unwrap();
            if let Some(prev) = &prev_token
                && prev.text == "∀"
            {
                write!(output, " ").unwrap();
            }
            if token.text == "{" {
                depth += 1;
            }
            prev_token = Some(token);
        }
        writeln!(output).unwrap();
    }
    std::fs::write(input_file, output).expect("Failed to write to file");
}
