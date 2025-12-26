use crate::lexer::{Token, tokenize};

pub const ABBREVIATIONS: &[(&str, &[&str])] = &[
    ("ⅰ", &["↙"]),
    ("ⅱ", &["↘", "↙"]),
    ("ⅲ", &["↘", "↘", "↙"]),
    ("ⅳ", &["↘", "↘", "↘", "↙"]),
    ("ⅴ", &["↘", "↘", "↘", "↘", "↙"]),
];

fn preprocess_tokens(
    tokens: Vec<Token>,
) -> Result<(bool, Vec<Token>), Box<dyn std::error::Error>> {
    let mut new_tokens = Vec::new();
    let mut changed = false;
    let mut i = 0;
    let mut macros = std::collections::HashMap::new();
    while i < tokens.len() {
        let token = &tokens[i];
        if token.text == "⟪" {
            new_tokens.push(token.clone());
            if i == 0 {
                Err(format!(
                    "Macro name missing before ⟪ at {}",
                    token.location
                ))?;
            }
            let macro_name = tokens[i - 1].text.clone();
            if macros.contains_key(&macro_name) {
                Err(format!(
                    "Redefinition of macro {} at {}",
                    macro_name, token.location
                ))?;
            }
            let mut depth = 1;
            let mut end = i + 1;
            while end < tokens.len() && depth > 0 {
                new_tokens.push(tokens[end].clone());
                if tokens[end].text == "⟪" {
                    depth += 1;
                } else if tokens[end].text == "⟫" {
                    depth -= 1;
                }
                end += 1;
            }
            if depth != 0 {
                Err(format!(
                    "Unterminated macro definition starting at {}",
                    token.location
                ))?;
            }
            let macro_body = tokens[i + 1..end - 1].to_vec();
            macros.insert(macro_name, macro_body);
            i = end;
            continue;
        }
        if token.text == "⟦" {
            if let Some(macro_name_token) = new_tokens.pop() {
                if let Some(macro_body) = macros.get(&macro_name_token.text) {
                    let mut end = i + 1;
                    let mut depth = 1;
                    while end < tokens.len() && depth > 0 {
                        if tokens[end].text == "⟦" {
                            depth += 1;
                        } else if tokens[end].text == "⟧" {
                            depth -= 1;
                        }
                        end += 1;
                    }
                    if depth != 0 {
                        Err(format!(
                            "Unterminated macro invocation starting at {}",
                            token.location
                        ))?;
                    }
                    let arg = tokens[i + 1..end - 1].to_vec();
                    i = end;
                    for body_token in macro_body {
                        if body_token.text == "●" {
                            new_tokens.push(Token {
                                text: "(".to_string(),
                                location: "magic".to_string(),
                                line_no: token.line_no,
                            });
                            for arg_token in &arg {
                                let mut new_token = arg_token.clone();
                                new_token.line_no = token.line_no;
                                new_tokens.push(new_token);
                            }
                            new_tokens.push(Token {
                                text: ")".to_string(),
                                location: "magic".to_string(),
                                line_no: token.line_no,
                            });
                        } else {
                            let mut new_token = body_token.clone();
                            new_token.line_no = token.line_no;
                            new_tokens.push(new_token);
                        }
                    }
                    changed = true;
                    continue;
                } else {
                    Err(format!(
                        "Undefined macro {} at {}",
                        macro_name_token.text, token.location
                    ))?;
                }
            } else {
                Err(format!(
                    "Macro name missing before ⟦ at {}",
                    token.location
                ))?;
            }
        }
        new_tokens.push(token.clone());
        i += 1;
    }
    Ok((changed, new_tokens))
}

pub fn strip_macro_definitions(tokens: Vec<Token>) -> Vec<Token> {
    let mut new_tokens = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        let token = &tokens[i];
        if token.text == "⟪" {
            new_tokens.pop();
            let mut depth = 1;
            i += 1;
            while i < tokens.len() && depth > 0 {
                if tokens[i].text == "⟪" {
                    depth += 1;
                } else if tokens[i].text == "⟫" {
                    depth -= 1;
                }
                i += 1;
            }
            continue;
        }
        new_tokens.push(token.clone());
        i += 1;
    }
    new_tokens
}

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
    let (mut changed, mut preprocessed_tokens) = preprocess_tokens(tokens)?;
    while changed {
        let (new_changed, new_tokens) = preprocess_tokens(preprocessed_tokens)?;
        changed = new_changed;
        preprocessed_tokens = new_tokens;
    }
    Ok(preprocessed_tokens)
}
