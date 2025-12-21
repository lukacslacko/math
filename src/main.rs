use std::error::Error;

mod interpreter;
mod lexer;
mod logic;
mod peano;
mod phrase;

type UnitResult = std::result::Result<(), Box<dyn Error>>;

fn main() -> UnitResult {
    logic::axioms()?;
    peano::axioms()?;
    let input = std::fs::read_to_string("example.ll")?;
    let tokens = lexer::tokenize(&input);
    interpreter::interpret(tokens.into_iter())?;
    println!("Hello, world!");
    Ok(())
}
