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
    println!("Hello, world!");
    Ok(())
}
