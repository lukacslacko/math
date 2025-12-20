use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;

thread_local! {
    static KNOWN_TRUTHS: RefCell<HashSet<Phrase>> = RefCell::new(HashSet::new());
}

pub type Phrase = Rc<PhraseData>;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum PhraseKind {
    LogicVariable,
    NumericVariable,
    NumericConstant,
    Imply,
    Not,
    Equals,
    Successor,
    Add,
    Multiply,
    Quantify,
}

pub use PhraseKind::*;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Children {
    Zero(),
    One(Phrase),
    Two(Phrase, Phrase),
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct PhraseData {
    kind: PhraseKind,
    children: Children,
    variable_name: Option<String>,
}

impl fmt::Display for PhraseData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            LogicVariable | NumericVariable | NumericConstant => {
                self.children.unwrap_zero();
                if let Some(variable_name) = &self.variable_name {
                    write!(f, "{variable_name}")
                } else {
                    Ok(())
                }
            }
            Imply => {
                let (left, right) = self.children.unwrap_two();
                write!(f, "({left} ⇒ {right})")
            }
            Not => {
                let child = self.children.unwrap_one();
                write!(f, "¬{child}")
            }
            Equals => {
                let (left, right) = self.children.unwrap_two();
                write!(f, "({left} = {right})")
            }
            Successor => {
                let child = self.children.unwrap_one();
                write!(f, "𝗦({child})")
            }
            Add => {
                let (left, right) = self.children.unwrap_two();
                write!(f, "({left} + {right})")
            }
            Multiply => {
                let (left, right) = self.children.unwrap_two();
                write!(f, "({left} * {right})")
            }
            Quantify => {
                let (left, right) = self.children.unwrap_two();
                write!(f, "∀{left} {right}")
            }
        }
    }
}

impl fmt::Binary for PhraseData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let is_known_truth = if self.get_is_proven() {
            "Proven"
        } else {
            "Unproven"
        };
        write!(f, "{is_known_truth}:{self}")
    }
}

impl Children {
    pub fn unwrap_zero(&self) {
        let Children::Zero() = self else {
            unreachable!();
        };
    }
    pub fn unwrap_one(&self) -> &Phrase {
        let Children::One(child) = self else {
            unreachable!();
        };
        child
    }
    pub fn unwrap_two(&self) -> (&Phrase, &Phrase) {
        let Children::Two(left, right) = self else {
            unreachable!();
        };
        (left, right)
    }
}

impl PhraseData {
    pub fn get_children(&self) -> &Children {
        &self.children
    }
    pub fn get_kind(&self) -> PhraseKind {
        self.kind
    }
    pub fn get_is_proven(&self) -> bool {
        KNOWN_TRUTHS.with_borrow(|known_truths| known_truths.contains(self))
    }
    pub fn get_variable_name(&self) -> &Option<String> {
        &self.variable_name
    }
    pub fn is_numeric(&self) -> bool {
        matches!(
            self.kind,
            NumericVariable | NumericConstant | Successor | Add | Multiply
        )
    }
    pub fn is_proposition(&self) -> bool {
        matches!(self.kind, LogicVariable | Imply | Not | Equals | Quantify)
    }
}

pub fn make_logic_variable(name: String) -> Option<Phrase> {
    if !name.starts_with('%') {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: LogicVariable,
        children: Children::Zero(),
        variable_name: Some(name),
    }))
}

pub fn make_numeric_variable(name: String) -> Option<Phrase> {
    if name.starts_with('%') {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: NumericVariable,
        children: Children::Zero(),
        variable_name: Some(name),
    }))
}

pub fn make_numeric_constant_zero(name: String) -> Option<Phrase> {
    assert_eq!(name, "0");
    Some(Rc::new(PhraseData {
        kind: NumericConstant,
        children: Children::Zero(),
        variable_name: Some(name),
    }))
}

// TODO: witness

pub fn make_imply(antecedent: Phrase, consequent: Phrase) -> Option<Phrase> {
    if !antecedent.is_proposition() || !consequent.is_proposition() {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: Imply,
        children: Children::Two(antecedent, consequent),
        variable_name: None,
    }))
}

pub fn make_not(negand: Phrase) -> Option<Phrase> {
    if !negand.is_proposition() {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: Not,
        children: Children::One(negand),
        variable_name: None,
    }))
}

pub fn make_equals(left: Phrase, right: Phrase) -> Option<Phrase> {
    if !left.is_numeric() || !right.is_numeric() {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: Equals,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_successor(number: Phrase) -> Option<Phrase> {
    if !number.is_numeric() {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: Successor,
        children: Children::One(number),
        variable_name: None,
    }))
}

pub fn make_add(left: Phrase, right: Phrase) -> Option<Phrase> {
    if !left.is_numeric() || !right.is_numeric() {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: Add,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_multiply(left: Phrase, right: Phrase) -> Option<Phrase> {
    if !left.is_numeric() || !right.is_numeric() {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: Multiply,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_quantify(variable: Phrase, predicate: Phrase) -> Option<Phrase> {
    if variable.kind != NumericVariable || !predicate.is_proposition() {
        return None;
    }
    Some(Rc::new(PhraseData {
        kind: Quantify,
        children: Children::Two(variable, predicate),
        variable_name: None,
    }))
}
