use crate::logger::{LogEntry, Logger};
use std::fmt::Write;

fn render_entry(entry: &LogEntry) -> String {
    let mut div = String::new();
    let (start, middle, end) = if entry.details.borrow().entries.is_empty() {
        ("<div class=\"log-entry\">", "", "</div>")
    } else {
        (
            "<details class=\"log-entry\"><summary><div class=\"summary-content\">",
            "</div></summary>",
            "</details>",
        )
    };
    writeln!(div, "{}", start).unwrap();
    writeln!(div, "<div>{}</div>", escape_html(&entry.info)).unwrap();
    writeln!(div, "<div>{}</div>", render_formula_html(&entry.phrase)).unwrap();
    writeln!(div, "{}", middle).unwrap();
    writeln!(div, "{}", render_logger(&entry.details.borrow())).unwrap();
    writeln!(div, "{}", end).unwrap();
    div
}

fn render_logger(logger: &Logger) -> String {
    let mut div = String::new();
    for entry in &logger.entries {
        writeln!(div, "{}", render_entry(entry)).unwrap();
    }
    div
}

pub fn render_html(logger: &Logger) -> String {
    let mut html = String::new();
    writeln!(html, "<html>").unwrap();
    writeln!(html, "<head><style>

/* Ensure the summary uses flex to keep the icon and text on the same row */
summary {{
//    display: flex;
//    align-items: flex-start; /* Aligns the triangle with the first line of text */
display: list-item;
    cursor: pointer;
    outline: none;
}}

/* Remove default margins from the internal divs so they don't push the summary apart */
summary > div {{
    margin: 0;
    padding-left: 5px; /* Adds a little space between the triangle and your text */
}}

/* Optional: if you want the 'Substitution' and 'Formula' to stay stacked
   but move as a single block next to the icon */
.summary-content {{
    // display: flex;
    display: inline-flex;
    flex-direction: column;
}}

    .log-entry {{
  width: 100%;
  border-left: 2px solid #ccc;
  border-top: 2px solid #ccc;
  border-bottom: 2px solid #ccc;
  border-radius: 4px;
  padding: 2px 0 2px 15px;
  background-color: rgba(0, 0, 0, 0.05);
  margin-top: 5px;
  margin-bottom: 5px;
                margin-left: 20px;
                font-family: Arial, sans-serif;
            }}
            details {{
                margin-top: 5px;
                margin-bottom: 5px;
            }}


  .formula {{
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, \"Liberation Mono\", monospace;
    font-size: 14px;
    line-height: 1.5;
    white-space: pre-wrap;
    word-break: break-word;
    }}

  .grp {{
    display: inline-block;
    padding: 1px 3px;
    border-radius: 6px;
    margin: 1px 2px;
    }}

  .br {{
    opacity: 0.65;
    }}



  /* repeating depth colors */
  .depth-0 {{ background: rgba(202, 201, 201, 1); }}
  .depth-1 {{ background: rgba(255, 255, 255, 1); }}
  .depth-2 {{ background: rgba(205, 217, 246, 1); }}
  .depth-3 {{ background: rgba(247, 244, 212, 1); }}
  .depth-4 {{ background: rgba(193, 242, 187, 1); }}
  .depth-5 {{ background: rgba(253, 226, 240, 1); }}
</style>
</head>").unwrap();
    writeln!(html, "<body>").unwrap();
    writeln!(html, "{}", render_logger(logger)).unwrap();
    writeln!(html, "<br>Execution succeeded.</br>").unwrap();
    writeln!(html, "</body>").unwrap();
    writeln!(html, "</html>").unwrap();
    html
}

fn escape_html_char(ch: char, out: &mut String) {
    match ch {
        '&' => out.push_str("&amp;"),
        '<' => out.push_str("&lt;"),
        '>' => out.push_str("&gt;"),
        '"' => out.push_str("&quot;"),
        '\'' => out.push_str("&#39;"),
        _ => out.push(ch),
    }
}

fn escape_html(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    for ch in input.chars() {
        escape_html_char(ch, &mut out);
    }
    out
}

fn is_open(ch: char) -> bool {
    matches!(ch, '(' | '[' | '{')
}

fn matching_close(open: char) -> char {
    match open {
        '(' => ')',
        '[' => ']',
        '{' => '}',
        _ => '\0',
    }
}

/// Render bracket groups as nested spans with depth classes.
/// `max_depth_classes` should match the number of `.depth-N` CSS rules you defined.
pub fn render_bracket_groups(input: &str, max_depth_classes: usize) -> String {
    let mut out = String::with_capacity(input.len() + input.len() / 2);
    let mut depth: usize = 0;
    let mut stack: Vec<char> = Vec::new(); // expected closing chars

    out.push_str(r#"<span class="formula">"#);

    for ch in input.chars() {
        if is_open(ch) {
            let cls = if max_depth_classes == 0 {
                0
            } else {
                depth % max_depth_classes
            };
            // Open a group span for this bracketed region
            let _ = write!(out, r#"<span class="grp depth-{}">"#, cls);
            // Emit the opening bracket
            let _ = write!(out, r#"<span class="br">{}</span>"#, ch);
            // Track expected close and increase depth
            stack.push(matching_close(ch));
            depth += 1;
        } else if matches!(ch, ')' | ']' | '}') {
            // Balanced input assumed. We'll still be defensive.
            depth = depth.saturating_sub(1);
            if let Some(expected) = stack.pop() {
                // If it doesn't match, still emit what we got and close one group.
                // (With your generator, it should always match.)
                let _ = write!(out, r#"<span class="br">{}</span></span>"#, ch);
                if expected != ch {
                    // no-op: you could add a class for mismatches if you ever want
                }
            } else {
                // Unmatched closing bracket, just emit it
                let _ = write!(out, r#"<span class="br">{}</span>"#, ch);
            }
        } else {
            escape_html_char(ch, &mut out);
        }
    }

    // Close any still-open groups (should be zero for balanced input)
    while stack.pop().is_some() {
        out.push_str("</span>");
    }

    out.push_str("</span>");
    out
}

fn render_formula_html(input: &str) -> String {
    render_bracket_groups(input, 6)
}
