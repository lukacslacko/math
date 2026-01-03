use math::*;

fn main() -> UnitResult {
    logic::axioms()?;
    peano::axioms()?;
    let args: Vec<String> = std::env::args().collect();
    let input_file = if args.len() == 2 {
        &args[1]
    } else {
        "example.ll"
    };
    let tokens = preprocessor::preprocess(input_file)?;
    let tokens = preprocessor::apply_abbreviations(tokens);
    format::write_formatted_file(
        &tokens,
        "preprocessed.ll",
        /*as_ascii=*/ false,
    );
    let logger = logger::Logger::new();
    interpreter::interpret(tokens.iter(), logger.clone())?;
    #[cfg(feature = "html")]
    std::fs::write("log.html", html::render_html(&logger.borrow()))?;
    println!("Hello, world!");
    Ok(())
}
