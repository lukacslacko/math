use crate::lexer::{Token, tokenize};

pub const ABBREVIATIONS: &[(&str, &[&str])] = &[
    ("ⅰ", &["↙"]),
    ("ⅱ", &["↘", "↙"]),
    ("ⅲ", &["↘", "↘", "↙"]),
    ("ⅳ", &["↘", "↘", "↘", "↙"]),
    ("ⅴ", &["↘", "↘", "↘", "↘", "↙"]),
];

pub fn apply_abbreviations(tokens: Vec<Token>) -> Vec<Token> {
    let mut new_tokens = Vec::new();
    for token in tokens {
        let new_texts =
            match ABBREVIATIONS.iter().find(|(abbr, _)| *abbr == token.text) {
                Some((_, expansion)) => expansion.to_vec(),
                None => vec![token.text.as_str()],
            };
        for new_text in new_texts {
            let mut new_token = token.clone();
            new_token.text = new_text.to_string();
            new_tokens.push(new_token);
        }
    }
    new_tokens
}

pub fn remove_comments(
    tokens: Vec<Token>,
) -> Result<Vec<Token>, Box<dyn std::error::Error>> {
    let mut new_tokens = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        let token = &tokens[i];
        if token.text == "/*" {
            let mut depth = 1;
            i += 1;
            while i < tokens.len() && depth > 0 {
                if tokens[i].text == "/*" {
                    depth += 1;
                } else if tokens[i].text == "*/" {
                    depth -= 1;
                }
                i += 1;
            }
            if depth != 0 {
                Err(format!(
                    "Unterminated comment starting at {}",
                    token.location
                ))?;
            }
            continue;
        }
        new_tokens.push(token.clone());
        i += 1;
    }
    Ok(new_tokens)
}

pub fn preprocess(
    input_file: &str,
) -> std::result::Result<Vec<Token>, Box<dyn std::error::Error>> {
    let input = std::fs::read_to_string(input_file)?;
    let tokens = tokenize(&input, input_file);
    let tokens = remove_comments(tokens)?;
    Ok(tokens)
}
