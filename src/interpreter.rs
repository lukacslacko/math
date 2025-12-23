use crate::UnitResult;
use crate::lexer::Token;
use crate::logic;
use crate::peano;
use crate::phrase::*;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, Default)]
struct Namespace {
    parent: Option<Rc<Namespace>>,
    stuff: RefCell<Vec<Thing>>,
}

impl Namespace {
    fn find(&self, name: &str) -> Option<Thing> {
        self.stuff
            .borrow()
            .iter()
            .rev()
            .find(|thing| thing.name() == name)
            .cloned()
    }
    fn set(&self, thing: Thing) {
        self.stuff.borrow_mut().push(thing);
    }
}

#[derive(Debug, Clone)]
enum Thing {
    LogicPhrase(String, Phrase),
    NumericPhrase(String, Phrase),
}

impl Thing {
    fn name(&self) -> &str {
        match self {
            Self::LogicPhrase(name, _) | Self::NumericPhrase(name, _) => name,
        }
    }
}

pub fn interpret(tokens: impl Iterator<Item = Token>) -> UnitResult {
    let namespace: Rc<Namespace> = Rc::default();
    namespace.set(Thing::NumericPhrase(
        "0".to_string(),
        make_numeric_constant_zero("0".to_string())?,
    ));
    interpret_inner(tokens, namespace)
}

#[derive(Debug, PartialEq, Eq)]
enum Node {
    Identifier(String),
    LogicPhrase(Phrase),
    NumericPhrase(Phrase),
    Successor,
    Assertion,
    CloseRound,
    OpenRound,
    ImplyTok,
    AssignTok,
    NotTok,
    EqualsTok,
    OpenSquare,
    CloseSquare,
    OpenCurly,
    CloseCurly,
    Slash,
    Dot,
    ModusPonens,
    Right,
    Child,
    Left,
}

impl Node {
    fn is_operator(&self) -> bool {
        match self {
            Node::Successor
            | Node::Assertion
            | Node::OpenRound
            | Node::ImplyTok
            | Node::AssignTok
            | Node::NotTok
            | Node::EqualsTok
            | Node::OpenSquare
            | Node::OpenCurly
            | Node::Slash
            | Node::Dot => true,

            Node::Identifier(_)
            | Node::LogicPhrase(_)
            | Node::NumericPhrase(_)
            | Node::CloseRound
            | Node::CloseSquare
            | Node::CloseCurly
            | Node::ModusPonens
            | Node::Right
            | Node::Child
            | Node::Left => false,
        }
    }
}

#[derive(Debug)]
struct Peek<I: Iterator<Item = Token>>(Option<Token>, I);

impl<I: Iterator<Item = Token>> Peek<I> {
    fn peek(&mut self) -> Option<String> {
        if self.0.is_none() {
            self.0 = self.1.next();
        }
        self.0.clone().map(|token| token.text)
    }
    fn take(&mut self) -> Option<Token> {
        self.0.take()
    }
    fn location(&self) -> String {
        self.0
            .clone()
            .map(|token| token.location)
            .unwrap_or("eof".to_string())
    }
}

fn back(stack: &[Node], index: usize) -> Option<&Node> {
    stack.iter().nth_back(index - 1)
}

fn interpret_inner(
    tokens: impl Iterator<Item = Token>,
    mut namespace: Rc<Namespace>,
) -> UnitResult {
    let mut peek = Peek(None, tokens);
    let mut stack = vec![];
    loop {
        // eprintln!("{stack:#?}");
        // let mut line = String::new();
        // std::io::stdin().read_line(&mut line)?;
        let token = peek.peek();
        if let (
            Some(Node::OpenRound),
            Some(Node::LogicPhrase(_) | Node::NumericPhrase(_)),
            Some(Node::CloseRound),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            stack.pop();
            stack.swap_remove(stack.len() - 2);
            continue;
        }
        if let (Some(Node::OpenRound), Some(Node::CloseRound)) =
            (back(&stack, 2), back(&stack, 1))
        {
            stack.pop();
            stack.pop();
            continue;
        }
        if let (
            Some(Node::OpenCurly),
            Some(Node::LogicPhrase(_) | Node::NumericPhrase(_)),
            Some(Node::CloseCurly),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            let len = stack.len();
            stack.swap(len - 3, len - 2);
            continue;
        }
        if let (Some(Node::OpenCurly), Some(Node::CloseCurly)) =
            (back(&stack, 2), back(&stack, 1))
        {
            let Some(parent) = namespace.parent.clone() else {
                Err(format!("syntax error @ {}", peek.location()))?
            };
            namespace = parent;
            stack.pop();
            stack.pop();
            continue;
        }
        if let Some(Node::CloseCurly) = back(&stack, 1) {
            Err(format!("syntax error @ {}", peek.location()))?
        }
        if let (
            Some(Node::LogicPhrase(logic_phrase)),
            Some(Node::OpenSquare),
            Some(Node::LogicPhrase(variable) | Node::NumericPhrase(variable)),
            Some(Node::Slash),
            Some(Node::LogicPhrase(term) | Node::NumericPhrase(term)),
            Some(Node::CloseSquare),
        ) = (
            back(&stack, 6),
            back(&stack, 5),
            back(&stack, 4),
            back(&stack, 3),
            back(&stack, 2),
            back(&stack, 1),
        ) {
            if variable.get_kind() != LogicVariable
                && variable.get_kind() != NumericVariable
            {
                Err(format!("TODO1 @ {}", peek.location()))?
            }
            if variable.is_numeric() != term.is_numeric() {
                Err(format!("TODO2 @ {}", peek.location()))?
            }
            let phrase = match logic_phrase
                .clone()
                .substitute(variable.clone(), term.clone())
            {
                Ok(phrase) => phrase,
                Err(err) => Err(format!("{err} @ {}", peek.location()))?,
            };
            stack.pop();
            stack.pop();
            stack.pop();
            stack.pop();
            stack.pop();
            stack.pop();
            stack.push(Node::LogicPhrase(phrase));
        }
        if let (
            Some(Node::NumericPhrase(numeric_phrase)),
            Some(Node::OpenSquare),
            Some(Node::LogicPhrase(variable) | Node::NumericPhrase(variable)),
            Some(Node::Slash),
            Some(Node::LogicPhrase(term) | Node::NumericPhrase(term)),
            Some(Node::CloseSquare),
        ) = (
            back(&stack, 6),
            back(&stack, 5),
            back(&stack, 4),
            back(&stack, 3),
            back(&stack, 2),
            back(&stack, 1),
        ) {
            if variable.get_kind() != LogicVariable
                && variable.get_kind() != NumericVariable
            {
                Err(format!("TODO1 @ {}", peek.location()))?
            }
            if variable.is_numeric() != term.is_numeric() {
                Err(format!("TODO2 @ {}", peek.location()))?
            }
            stack.push(Node::NumericPhrase(
                numeric_phrase
                    .clone()
                    .substitute(variable.clone(), term.clone())?,
            ));
            stack.swap_remove(stack.len() - 7);
            stack.pop();
            stack.pop();
            stack.pop();
            stack.pop();
            stack.pop();
        }
        if let (
            Some(Node::LogicPhrase(logic_phrase)),
            Some(Node::Dot),
            Some(Node::ModusPonens),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            if logic_phrase.get_kind() != Imply {
                Err(format!("TODO3 @ {}", peek.location()))?
            }
            if !logic_phrase.clone().get_is_proven() {
                Err(format!(
                    "modus ponens implication not proven @ {}",
                    peek.location()
                ))?
            }
            if !logic_phrase
                .get_children()
                .unwrap_two()
                .0
                .clone()
                .get_is_proven()
            {
                Err(format!(
                    "modus ponens antecedent not proven @ {}",
                    peek.location()
                ))?
            }
            stack.push(Node::LogicPhrase(logic_phrase.clone().modus_ponens()?));
            stack.swap_remove(stack.len() - 4);
            stack.pop();
            stack.pop();
        }
        if let (
            Some(Node::LogicPhrase(phrase) | Node::NumericPhrase(phrase)),
            Some(Node::Left),
        ) = (back(&stack, 2), back(&stack, 1))
        {
            let child = match phrase.get_children() {
                Children::Two(left, _) => left,
                _ => Err(format!("error @ {}", peek.location()))?,
            };
            if child.is_proposition() {
                stack.push(Node::LogicPhrase(child.clone()));
            } else {
                stack.push(Node::NumericPhrase(child.clone()));
            }
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let (
            Some(Node::LogicPhrase(phrase) | Node::NumericPhrase(phrase)),
            Some(Node::Right),
        ) = (back(&stack, 2), back(&stack, 1))
        {
            let child = match phrase.get_children() {
                Children::Two(_, right) => right,
                _ => Err(format!("error @ {}", peek.location()))?,
            };
            if child.is_proposition() {
                stack.push(Node::LogicPhrase(child.clone()));
            } else {
                stack.push(Node::NumericPhrase(child.clone()));
            }
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let (
            Some(Node::LogicPhrase(phrase) | Node::NumericPhrase(phrase)),
            Some(Node::Child),
        ) = (back(&stack, 2), back(&stack, 1))
        {
            let child = match phrase.get_children() {
                Children::One(child) => child,
                _ => Err(format!("error @ {}", peek.location()))?,
            };
            if child.is_proposition() {
                stack.push(Node::LogicPhrase(child.clone()));
            } else {
                stack.push(Node::NumericPhrase(child.clone()));
            }
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if token == Some("MP".to_string()) {
            peek.take();
            stack.push(Node::ModusPonens);
            continue;
        }
        if token == Some(".".to_string()) {
            peek.take();
            stack.push(Node::Dot);
            continue;
        }
        if token == Some("↙".to_string()) {
            peek.take();
            stack.push(Node::Left);
            continue;
        }
        if token == Some("↘".to_string()) {
            peek.take();
            stack.push(Node::Right);
            continue;
        }
        if token == Some("↓".to_string()) {
            peek.take();
            stack.push(Node::Child);
            continue;
        }
        if let (
            Some(Node::Successor),
            Some(Node::NumericPhrase(numeric_phrase)),
        ) = (back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::NumericPhrase(make_successor(
                numeric_phrase.clone(),
            )?));
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let (Some(Node::NotTok), Some(Node::LogicPhrase(logic_phrase))) =
            (back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::LogicPhrase(make_not(logic_phrase.clone())?));
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let (
            Some(Node::NumericPhrase(l)),
            Some(Node::EqualsTok),
            Some(Node::NumericPhrase(r)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::LogicPhrase(make_equals(l.clone(), r.clone())?));
            stack.swap_remove(stack.len() - 4);
            stack.pop();
            stack.pop();
            continue;
        }
        if token == Some("=".to_string()) {
            peek.take();
            stack.push(Node::EqualsTok);
            continue;
        }
        if token == Some("⇒".to_string()) {
            peek.take();
            stack.push(Node::ImplyTok);
            continue;
        }
        if token == Some("[".to_string()) {
            peek.take();
            stack.push(Node::OpenSquare);
            continue;
        }
        if token == Some("/".to_string()) {
            peek.take();
            stack.push(Node::Slash);
            continue;
        }
        if let (
            Some(Node::LogicPhrase(a)),
            Some(Node::ImplyTok),
            Some(Node::LogicPhrase(c)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::LogicPhrase(make_imply(a.clone(), c.clone())?));
            stack.swap_remove(stack.len() - 4);
            stack.pop();
            stack.pop();
            continue;
        }
        if let (
            Some(Node::Identifier(ident)),
            Some(Node::AssignTok),
            Some(Node::NumericPhrase(numeric_phrase)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            namespace.set(Thing::NumericPhrase(
                ident.clone(),
                numeric_phrase.clone(),
            ));
            stack.pop();
            stack.pop();
            stack.pop();
        }
        if let (
            Some(Node::Identifier(ident)),
            Some(Node::AssignTok),
            Some(Node::LogicPhrase(logic_phrase)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            namespace
                .set(Thing::LogicPhrase(ident.clone(), logic_phrase.clone()));
            stack.pop();
            stack.pop();
            stack.pop();
        }
        if let (Some(Node::Assertion), Some(Node::LogicPhrase(logic_phrase))) =
            (back(&stack, 2), back(&stack, 1))
        {
            if !logic_phrase.get_is_proven() {
                Err(format!(
                    "assertion failed {:b} @ {}",
                    **logic_phrase,
                    peek.location(),
                ))?
            }
            stack.pop();
            stack.pop();
            continue;
        }
        if token == Some("]".to_string()) {
            peek.take();
            stack.push(Node::CloseSquare);
            continue;
        }
        if token == Some(")".to_string()) {
            peek.take();
            stack.push(Node::CloseRound);
            continue;
        }
        if token == Some("}".to_string()) {
            peek.take();
            stack.push(Node::CloseCurly);
            continue;
        }
        if let Some(Node::LogicPhrase(phrase) | Node::NumericPhrase(phrase)) =
            back(&stack, 1)
        {
            if token == Some("℻".to_string()) {
                peek.take();
                println!("{:b}", **phrase);
            }
            stack.pop();
            continue;
        }
        if token == Some("{".to_string()) {
            peek.take();
            namespace = Namespace {
                parent: Some(namespace),
                stuff: vec![].into(),
            }
            .into();
            stack.push(Node::OpenCurly);
            continue;
        }
        if token == Some("⤷".to_string()) {
            peek.take();
            let Some(ident) = peek.peek() else {
                Err("unexpected eof")?
            };
            if namespace.find(&ident).is_some() {
                Err(format!("TODO @ {}", peek.location()))?
            }
            let Some(parent) = namespace.parent.clone() else {
                Err(format!(
                    "cannot import into global namespace @ {}",
                    peek.location()
                ))?
            };
            let Some(thing) = parent.find(&ident) else {
                Err(format!(
                    "parent namespace does not contain {ident} @ {}",
                    peek.location()
                ))?
            };
            namespace.set(thing);
            peek.take();
            continue;
        }
        if token == Some("⤶".to_string()) {
            peek.take();
            let Some(ident) = peek.peek() else {
                Err("unexpected eof")?
            };
            let Some(thing) = namespace.find(&ident) else {
                Err(format!(
                    "namespace does not contain {ident} @ {}",
                    peek.location()
                ))?
            };
            let Some(parent) = namespace.parent.clone() else {
                Err(format!(
                    "cannot export from global namespace @ {}",
                    peek.location()
                ))?
            };
            if parent.find(&ident).is_some() {
                Err(format!("TODO @ {}", peek.location()))?
            }
            parent.set(thing);
            continue;
        }
        if token == Some("⊦".to_string()) {
            peek.take();
            stack.push(Node::Assertion);
            continue;
        }
        if token == Some("(".to_string()) {
            peek.take();
            stack.push(Node::OpenRound);
            continue;
        }
        if token == Some("𝗦".to_string()) {
            peek.take();
            stack.push(Node::Successor);
            continue;
        }
        if token == Some("¬".to_string()) {
            peek.take();
            stack.push(Node::NotTok);
            continue;
        }
        if token == Some("≔".to_string()) {
            let Some(Node::Identifier(_)) = back(&stack, 1) else {
                Err(format!("syntax error @ {}", peek.location()))?
            };
            peek.take();
            stack.push(Node::AssignTok);
            continue;
        }

        if let Some(top) = back(&stack, 1)
            && !top.is_operator()
        {
            Err(format!("syntax error @ {}", peek.location()))?
        }
        if token.as_ref().map(|t| t.starts_with('\'')) == Some(true) {
            peek.take();
            stack.push(Node::LogicPhrase(make_logic_variable(token.unwrap())?));
            continue;
        }
        if let Some(token) = token {
            peek.take();
            match namespace.find(&token) {
                Some(Thing::LogicPhrase(_, logic_phrase)) => {
                    stack.push(Node::LogicPhrase(logic_phrase))
                }
                Some(Thing::NumericPhrase(_, numeric_phrase)) => {
                    stack.push(Node::NumericPhrase(numeric_phrase))
                }
                None => stack.push(Node::Identifier(token)),
            }
            continue;
        }
        if !stack.is_empty() {
            Err("unexpected eof")?
        }
        return Ok(());
    }
}
