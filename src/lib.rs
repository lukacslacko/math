use std::error::Error;

pub mod format;
#[cfg(feature = "html")]
pub mod html;
pub mod interpreter;
pub mod lexer;
pub mod logger;
pub mod logic;
pub mod peano;
pub mod phrase;
pub mod preprocessor;

pub type UnitResult = std::result::Result<(), Box<dyn Error>>;
