use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

fn main() {
    println!("Hello, world!");
}

thread_local! {
    static PHRASES: RefCell<HashSet<Rc<Phrase>>> = RefCell::new(HashSet::new());
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum PhraseKind {
    LogicVariable,
    NumericVariable,
    NumericConstant,
    Implies,
    Not,
    Equals,
    Successor,
    Add,
    Multiply,
    Quantify,
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Children {
    Zero(),
    One(Rc<Phrase>),
    Two(Rc<Phrase>, Rc<Phrase>),
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Phrase {
    kind: PhraseKind,
    children: Children,
    is_known_truth: bool,
    variable_name: Option<String>,
}
