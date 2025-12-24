use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::rc::Rc;

thread_local! {
    static KNOWN_TRUTHS: RefCell<HashMap<Phrase, Proof>> = RefCell::new(HashMap::new());
}

pub type Phrase = Rc<PhraseData>;
pub type Result = std::result::Result<Phrase, Box<dyn Error>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Proof {
    Name(&'static str),
    NamePhrase(&'static str, Phrase),
    NameVariablePhrase(&'static str, String, Phrase),
    NamePhrasePhrase(&'static str, Phrase, Phrase),
}

pub use Proof::*;

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
        KNOWN_TRUTHS.with_borrow(|known_truths| known_truths.contains_key(self))
    }
    pub fn is_free(
        &self,
        variable: &PhraseData,
    ) -> std::result::Result<bool, Box<dyn Error>> {
        if !matches!(variable.kind, NumericVariable | LogicVariable) {
            Err("is_free")?
        }
        Ok(self == variable
            || if self.kind == Quantify {
                let (left, right) = self.children.unwrap_two();
                if &**left == variable {
                    false
                } else {
                    right.is_free(variable)?
                }
            } else {
                match &self.children {
                    Children::Zero() => false,
                    Children::One(child) => child.is_free(variable)?,
                    Children::Two(left, right) => {
                        left.is_free(variable)? || right.is_free(variable)?
                    }
                }
            })
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
    pub fn assert_axiom(self: Phrase, proof: Proof) -> Result {
        match &proof {
            NamePhrase(_, phrase) if !phrase.get_is_proven() => {
                Err("assert_axiom")?
            }
            NameVariablePhrase(_, _, phrase) if !phrase.get_is_proven() => {
                Err("assert_axiom")?
            }
            NamePhrasePhrase(_, phrase1, phrase2)
                if !phrase1.get_is_proven() || !phrase2.get_is_proven() =>
            {
                Err("assert_axiom")?
            }
            _ => {}
        }
        KNOWN_TRUTHS.with_borrow_mut(|known_truths| {
            known_truths.insert(self.clone(), proof)
        });
        Ok(self)
    }
    pub fn substitute(self: Phrase, variable: Phrase, term: Phrase) -> Result {
        match variable.kind {
            LogicVariable if term.is_proposition() => {}
            NumericVariable if term.is_numeric() => {}
            _ => Err("substitute")?,
        }
        if self == variable {
            return Ok(term.clone());
        } else if matches!(self.children, Children::Zero()) {
            return Ok(self.clone());
        }
        let new = {
            if self.kind == Quantify {
                let (left, _) = self.children.unwrap_two();
                if **left == *variable {
                    return Ok(self);
                } else if term.is_free(left)? {
                    Err("substitute")?
                }
            }
            Rc::new(PhraseData {
                kind: self.kind,
                children: match &self.children {
                    Children::Zero() => Children::Zero(),
                    Children::One(child) => Children::One(
                        child
                            .clone()
                            .substitute(variable.clone(), term.clone())?,
                    ),
                    Children::Two(left, right) => Children::Two(
                        left.clone()
                            .substitute(variable.clone(), term.clone())?,
                        right
                            .clone()
                            .substitute(variable.clone(), term.clone())?,
                    ),
                },
                variable_name: self.variable_name.clone(),
            })
        };
        if self.get_is_proven() {
            new.clone().assert_axiom(NameVariablePhrase(
                "substitute",
                variable.variable_name.clone().unwrap(),
                self,
            ))?;
        }
        Ok(new)
    }
    pub fn modus_ponens(self: Phrase) -> Result {
        if self.kind != Imply {
            Err("modus_ponens not implication")?
        }
        let (antecedent, consequent) = self.children.unwrap_two();
        if !antecedent.get_is_proven() {
            Err("modus_ponens antecedent not proven")?
        }
        if !self.get_is_proven() {
            Err("modus_ponens implication not proven")?
        }
        consequent.clone().assert_axiom(NamePhrasePhrase(
            "modus ponens",
            self.clone(),
            antecedent.clone(),
        ))
    }
}

pub fn make_logic_variable(name: String) -> Result {
    if !name.starts_with('\'') {
        Err("make_logic_variable")?
    }
    Ok(Rc::new(PhraseData {
        kind: LogicVariable,
        children: Children::Zero(),
        variable_name: Some(name),
    }))
}

pub fn make_numeric_variable(name: String) -> Result {
    if name.starts_with('\'') {
        Err("make_numeric_variable")?
    }
    Ok(Rc::new(PhraseData {
        kind: NumericVariable,
        children: Children::Zero(),
        variable_name: Some(name),
    }))
}

pub fn make_numeric_constant_zero(name: String) -> Result {
    if name != "0" {
        Err("make_numeric_constant_zero")?
    }
    Ok(Rc::new(PhraseData {
        kind: NumericConstant,
        children: Children::Zero(),
        variable_name: Some(name),
    }))
}

// TODO: witness

pub fn make_imply(antecedent: Phrase, consequent: Phrase) -> Result {
    if !antecedent.is_proposition() || !consequent.is_proposition() {
        Err("make_imply")?
    }
    Ok(Rc::new(PhraseData {
        kind: Imply,
        children: Children::Two(antecedent, consequent),
        variable_name: None,
    }))
}

pub fn make_not(negand: Phrase) -> Result {
    if !negand.is_proposition() {
        Err("make_not")?
    }
    Ok(Rc::new(PhraseData {
        kind: Not,
        children: Children::One(negand),
        variable_name: None,
    }))
}

pub fn make_equals(left: Phrase, right: Phrase) -> Result {
    if !left.is_numeric() || !right.is_numeric() {
        Err("make_equals")?
    }
    Ok(Rc::new(PhraseData {
        kind: Equals,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_successor(number: Phrase) -> Result {
    if !number.is_numeric() {
        Err("make_successor")?
    }
    Ok(Rc::new(PhraseData {
        kind: Successor,
        children: Children::One(number),
        variable_name: None,
    }))
}

pub fn make_add(left: Phrase, right: Phrase) -> Result {
    if !left.is_numeric() || !right.is_numeric() {
        Err("make_add")?
    }
    Ok(Rc::new(PhraseData {
        kind: Add,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_multiply(left: Phrase, right: Phrase) -> Result {
    if !left.is_numeric() || !right.is_numeric() {
        Err("make_multiply")?
    }
    Ok(Rc::new(PhraseData {
        kind: Multiply,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_quantify(variable: Phrase, predicate: Phrase) -> Result {
    if variable.kind != NumericVariable || !predicate.is_proposition() {
        Err("make_quantify")?
    }
    let new = Rc::new(PhraseData {
        kind: Quantify,
        children: Children::Two(variable, predicate.clone()),
        variable_name: None,
    });
    if predicate.clone().get_is_proven() {
        new.clone().assert_axiom(NamePhrase(
            "universal generalization",
            predicate.clone(),
        ))?;
    }
    Ok(new)
}
