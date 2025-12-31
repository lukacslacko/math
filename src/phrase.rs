use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::rc::Rc;

thread_local! {
    static KNOWN_TRUTHS: RefCell<HashMap<Phrase, Proof>> = RefCell::new(HashMap::new());
    static ZERO: Phrase = Rc::new(PhraseData{kind: Zero,children:Children::Zero(),variable_name:None});
}

pub type Phrase = Rc<PhraseData>;
pub type Result = std::result::Result<Phrase, Box<dyn Error>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Proof {
    Name(&'static str),
    NamePhrase(&'static str, Phrase),
    NameVariablePhrase(&'static str, Rc<str>, Phrase),
    NamePhrasePhrase(&'static str, Phrase, Phrase),
}

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name(name) => write!(f, "Axiom: {name}"),
            NamePhrase(name, phrase) => write!(f, "Proof: {name} on {phrase}"),
            NameVariablePhrase(name, var_name, phrase) => {
                write!(f, "Proof: {name} on {var_name} in {phrase}")
            }
            NamePhrasePhrase(name, phrase1, phrase2) => {
                write!(f, "Proof: {name} on {phrase1} and {phrase2}")
            }
        }
    }
}

pub use Proof::*;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum PhraseKind {
    LogicVariable,
    NumericVariable,
    Zero,
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

#[derive(Debug, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
    Child,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct PhraseData {
    kind: PhraseKind,
    children: Children,
    variable_name: Option<Rc<str>>,
}

impl fmt::Display for PhraseData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            LogicVariable | NumericVariable => {
                self.children.unwrap_zero();
                if let Some(variable_name) = &self.variable_name {
                    write!(f, "{variable_name}")
                } else {
                    Ok(())
                }
            }
            Zero => write!(f, "0"),
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

pub struct CutResult {
    pub new_phrase: Phrase,
    pub removed: Phrase,
}

pub struct Substitution {
    pub variable: Phrase,
    pub term: Phrase,
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
            Err(format!(
                "freedom can only be checked for a variable, got {variable:?}"
            ))?
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
        !self.is_proposition()
    }
    pub fn is_proposition(&self) -> bool {
        matches!(self.kind, LogicVariable | Imply | Not | Equals | Quantify)
    }
    pub fn assert_axiom(self: Phrase, proof: Proof) -> Result {
        match &proof {
            NamePhrase(_, phrase) if !phrase.get_is_proven() => {
                Err(format!("assert_axiom: phrase not proven: {phrase}"))?
            }
            NameVariablePhrase(_, _, phrase) if !phrase.get_is_proven() => {
                Err(format!("assert_axiom: phrase not proven: {phrase}"))?
            }
            NamePhrasePhrase(_, phrase1, phrase2)
                if !phrase1.get_is_proven() || !phrase2.get_is_proven() =>
            {
                Err(format!(
                    "assert_axiom: phrases are not both proven: {phrase1} and {phrase2}"
                ))?
            }
            _ => {}
        }
        KNOWN_TRUTHS.with_borrow_mut(|known_truths| {
            known_truths.entry(self.clone()).or_insert(proof);
        });
        Ok(self)
    }
    pub fn substitute(self: Phrase, variable: Phrase, term: Phrase) -> Result {
        match variable.kind {
            LogicVariable if term.is_proposition() => {}
            NumericVariable if term.is_numeric() => {}
            _ => Err(format!(
                "substitute requires a variable and a term of matching kind, got variable: {variable:?}, term: {term}"
            ))?,
        }
        if self == variable {
            return Ok(term);
        }
        if !self.is_free(&variable)? {
            return Ok(self);
        }
        let new = {
            if self.kind == Quantify {
                let (left, _) = self.children.unwrap_two();
                if **left == *variable {
                    return Ok(self);
                } else if term.is_free(left)? {
                    Err(format!(
                        "substitute would capture a free variable in the quantification {self} when substituting {term} for {variable}"
                    ))?
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

    pub fn left(&self) -> Result {
        match &self.children {
            Children::Two(left, _) => Ok(left.clone()),
            _ => Err(format!("left() called on non-binary phrase: {self}"))?,
        }
    }

    pub fn right(&self) -> Result {
        match &self.children {
            Children::Two(_, right) => Ok(right.clone()),
            _ => Err(format!("right() called on non-binary phrase: {self}"))?,
        }
    }

    pub fn child(&self) -> Result {
        match &self.children {
            Children::One(child) => Ok(child.clone()),
            _ => Err(format!("child() called on non-unary phrase: {self}"))?,
        }
    }

    pub fn cut(
        self: Phrase,
        path: &[Direction],
        var: Phrase,
    ) -> std::result::Result<CutResult, Box<dyn Error>> {
        /*
        Follows the path in the phrase, removes the subtree at that position,
        and replaces it with the provided variable.
         */
        if path.is_empty() {
            return Ok(CutResult {
                new_phrase: var,
                removed: self,
            });
        }
        let first_direction = &path[0];
        let rest_path = &path[1..];
        let (new_children, removed) = match &self.children {
            Children::Zero() => Err(format!(
                "cut() called on leaf phrase: {self} with path {path:?}"
            ))?,
            Children::One(child) => {
                if first_direction != &Direction::Child {
                    Err(format!(
                        "cut() path direction mismatch at phrase {self}: expected Child, got {first_direction:?}"
                    ))?
                }
                let cut_result = child.clone().cut(rest_path, var)?;
                (Children::One(cut_result.new_phrase), cut_result.removed)
            }
            Children::Two(left, right) => match first_direction {
                Direction::Left => {
                    let cut_result = left.clone().cut(rest_path, var)?;
                    (
                        Children::Two(cut_result.new_phrase, right.clone()),
                        cut_result.removed,
                    )
                }
                Direction::Right => {
                    let cut_result = right.clone().cut(rest_path, var)?;
                    (
                        Children::Two(left.clone(), cut_result.new_phrase),
                        cut_result.removed,
                    )
                }
                Direction::Child => Err(format!(
                    "cut() path direction mismatch at phrase {self}: expected Left or Right, got Child"
                ))?,
            },
        };
        let new_phrase = Rc::new(PhraseData {
            kind: self.kind,
            children: new_children,
            variable_name: self.variable_name.clone(),
        });
        Ok(CutResult {
            new_phrase,
            removed,
        })
    }

    pub fn find_parallel_substitutions(
        self: &Phrase,
        other: &Phrase,
    ) -> std::result::Result<Vec<Substitution>, Box<dyn Error>> {
        match &self.children {
            Children::Zero() => match self.kind {
                LogicVariable | NumericVariable => Ok(vec![Substitution {
                    variable: self.clone(),
                    term: other.clone(),
                }]),
                _ => Ok(vec![]),
            },
            Children::One(child) => {
                if self.kind != other.kind {
                    Err(format!(
                        "find_parallel_substitutions kind mismatch: {self} vs {other}"
                    ))?
                }
                match &other.children {
                    Children::One(other_child) => {
                        child.find_parallel_substitutions(other_child)
                    }
                    _ => Err(format!(
                        "find_parallel_substitutions number of children mismatch: {self} vs {other}"
                    ))?,
                }
            }
            Children::Two(left, right) => {
                if self.kind != other.kind {
                    Err(format!(
                        "find_parallel_substitutions kind mismatch: {self} vs {other}"
                    ))?
                }
                match &other.children {
                    Children::Two(other_left, other_right) => {
                        let mut subs_left =
                            left.find_parallel_substitutions(other_left)?;
                        let subs_right =
                            right.find_parallel_substitutions(other_right)?;
                        subs_left.extend(subs_right);
                        Ok(subs_left)
                    }
                    _ => Err(format!(
                        "find_parallel_substitutions number of children mismatch: {self} vs {other}"
                    ))?,
                }
            }
        }
    }

    /// Try to substitute `self` to get `other`.
    ///
    /// Returns the substituted phrase if successful.
    pub fn parallel(self: &Phrase, other: &Phrase) -> Result {
        let substitutions = self.find_parallel_substitutions(other)?;
        let mut new_phrase = self.clone();
        for substitution in substitutions {
            new_phrase = new_phrase
                .substitute(substitution.variable, substitution.term)?;
        }
        if new_phrase == *other {
            Ok(new_phrase)
        } else {
            Err(format!(
                "Structure matches but phrases differ after substitution, self: {self}, other: {other}, new_phrase: {new_phrase}"
            ))?
        }
    }

    pub fn try_prove(self: Phrase) -> Result {
        if self.get_is_proven() {
            return Ok(self);
        }
        let known_true_phrases = KNOWN_TRUTHS.with_borrow(|known_truths| {
            known_truths.keys().cloned().collect::<Vec<Phrase>>()
        });
        for known_true in known_true_phrases {
            if let Ok(matched_phrase) = known_true.parallel(&self) {
                return Ok(matched_phrase);
            }
        }
        Err(format!("Cannot prove phrase: {self}"))?
    }

    pub fn modus_ponens(self: Phrase) -> Result {
        if self.kind != Imply {
            Err(format!("modus_ponens requires an implication, got {self}"))?
        }
        let (antecedent, consequent) = self.children.unwrap_two();
        if !antecedent.get_is_proven() {
            Err(format!("modus ponens antecedent not proven: {antecedent}"))?
        }
        if !self.get_is_proven() {
            Err(format!("modus ponens implication not proven: {self}"))?
        }
        consequent.clone().assert_axiom(NamePhrasePhrase(
            "modus ponens",
            self.clone(),
            antecedent.clone(),
        ))
    }

    pub fn show_proof(&self) -> Option<Vec<(String, Proof)>> {
        if !self.get_is_proven() {
            panic!("I am false! {self}");
        }
        KNOWN_TRUTHS.with_borrow(|known_truths| {
            let my_proof = known_truths.get(self)?;
            let me_and_my_proof = (self.to_string(), my_proof.clone());
            match my_proof {
                Name(_) => Some(vec![me_and_my_proof]),
                NamePhrase(_, phrase) => {
                    if **phrase == *self {
                        panic!("circular proof detected for {self}");
                    }
                    let mut subproof = phrase.show_proof()?;
                    if subproof.contains(&me_and_my_proof) {
                        panic!("circular proof detected for {self}");
                    }
                    subproof.push(me_and_my_proof);
                    Some(subproof)
                }
                NameVariablePhrase(_, _, phrase) => {
                    let mut subproof = phrase.show_proof()?;
                    if **phrase == *self {
                        panic!("circular proof detected for {self}");
                    }
                    if subproof.contains(&me_and_my_proof) {
                        panic!("circular proof detected for {self}");
                    }
                    subproof.push(me_and_my_proof);
                    Some(subproof)
                }
                NamePhrasePhrase(_, phrase1, phrase2) => {
                    if **phrase1 == *self {
                        panic!("circular proof detected for {self}");
                    }
                    if **phrase2 == *self {
                        panic!("circular proof detected for {self}");
                    }
                    let mut subproof = phrase1.show_proof()?;
                    for proof in phrase2.show_proof()? {
                        if subproof.contains(&proof) {
                            continue;
                        }
                        subproof.push(proof);
                    }
                    if subproof.contains(&me_and_my_proof) {
                        panic!("circular proof detected for {self}");
                    }
                    subproof.push(me_and_my_proof);
                    Some(subproof)
                }
            }
        })
    }

    pub fn to_html(&self) -> String {
        format!("{}{}", self, if self.get_is_proven() {
            " ✅"
        } else {
            ""
        })
    }
}

pub fn make_logic_variable(name: Rc<str>) -> Result {
    if !name.starts_with('\'') {
        Err(format!(
            "logic variable must start with an apostrophe, got {name}"
        ))?
    }
    Ok(Rc::new(PhraseData {
        kind: LogicVariable,
        children: Children::Zero(),
        variable_name: Some(name),
    }))
}

pub fn make_numeric_variable(name: Rc<str>) -> Result {
    if name.starts_with('\'') {
        Err(format!(
            "numeric variable must not start with an apostrophe, got {name}"
        ))?
    }
    Ok(Rc::new(PhraseData {
        kind: NumericVariable,
        children: Children::Zero(),
        variable_name: Some(name),
    }))
}

pub fn make_numeric_constant_zero() -> Phrase {
    ZERO.with(Rc::clone)
}

pub fn make_imply(antecedent: Phrase, consequent: Phrase) -> Result {
    if !antecedent.is_proposition() || !consequent.is_proposition() {
        Err(format!(
            "make_imply requires propositions, got antecedent: {antecedent}, consequent: {consequent}"
        ))?
    }
    Ok(Rc::new(PhraseData {
        kind: Imply,
        children: Children::Two(antecedent, consequent),
        variable_name: None,
    }))
}

pub fn make_not(negand: Phrase) -> Result {
    if !negand.is_proposition() {
        Err(format!("make_not requires a proposition, got {negand}"))?
    }
    Ok(Rc::new(PhraseData {
        kind: Not,
        children: Children::One(negand),
        variable_name: None,
    }))
}

pub fn make_equals(left: Phrase, right: Phrase) -> Result {
    if !left.is_numeric() || !right.is_numeric() {
        Err(format!(
            "make_equals requires numeric phrases, got left: {left}, right: {right}"
        ))?
    }
    Ok(Rc::new(PhraseData {
        kind: Equals,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_successor(number: Phrase) -> Result {
    if !number.is_numeric() {
        Err(format!(
            "make_successor requires a numeric phrase, got {number}"
        ))?
    }
    Ok(Rc::new(PhraseData {
        kind: Successor,
        children: Children::One(number),
        variable_name: None,
    }))
}

pub fn make_add(left: Phrase, right: Phrase) -> Result {
    if !left.is_numeric() || !right.is_numeric() {
        Err(format!(
            "make_add requires numeric phrases, got left: {left}, right: {right}"
        ))?
    }
    Ok(Rc::new(PhraseData {
        kind: Add,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_multiply(left: Phrase, right: Phrase) -> Result {
    if !left.is_numeric() || !right.is_numeric() {
        Err(format!(
            "make_multiply requires numeric phrases, got left: {left}, right: {right}"
        ))?
    }
    Ok(Rc::new(PhraseData {
        kind: Multiply,
        children: Children::Two(left, right),
        variable_name: None,
    }))
}

pub fn make_quantify(variable: Phrase, predicate: Phrase) -> Result {
    if variable.kind != NumericVariable || !predicate.is_proposition() {
        Err(format!(
            "make_quantify requires a numeric variable and a proposition, got variable: {variable}, predicate: {predicate}"
        ))?
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
