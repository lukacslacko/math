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
    fn find_self(&self, name: &str) -> Option<Thing> {
        self.stuff
            .borrow()
            .iter()
            .rev()
            .find(|thing| thing.name() == name)
            .cloned()
    }
    fn find(self: &Rc<Self>, name: &str) -> Option<Thing> {
        let mut this = Some(self.clone());
        while let Some(namespace) = this {
            if let Some(thing) = namespace.find_self(name) {
                return Some(thing);
            }
            this = namespace.parent.clone();
        }
        None
    }
    fn set(self: &Rc<Self>, thing: Thing) {
        self.stuff.borrow_mut().push(thing);
    }
}

#[derive(Debug, Clone)]
enum Thing {
    LogicPhrase(String, Phrase),
    NumericConstant(String, Phrase),
}

impl Thing {
    fn name(&self) -> &str {
        match self {
            Self::LogicPhrase(name, _) | Self::NumericConstant(name, _) => name,
        }
    }
}

pub fn interpret(tokens: impl Iterator<Item = Token>) -> UnitResult {
    let namespace: Rc<Namespace> = Rc::default();
    namespace.set(Thing::NumericConstant(
        "0".to_string(),
        make_numeric_constant_zero("0".to_string())?,
    ));
    interpret_inner(tokens, namespace)
}

#[derive(Debug, PartialEq, Eq)]
enum Node {
    Identifier(String),
    LogicPhrase(Phrase),
    Assertion,
    CloseRound,
    OpenRound,
    ImplyTok,
    AssignTok,
    NotTok,
    OpenSquare,
    CloseSquare,
    Slash,
}

impl Node {
    fn is_operator(&self) -> bool {
        match self {
            Node::Assertion
            | Node::OpenRound
            | Node::ImplyTok
            | Node::AssignTok
            | Node::NotTok
            | Node::OpenSquare
            | Node::Slash => true,

            Node::Identifier(_)
            | Node::LogicPhrase(_)
            | Node::CloseRound
            | Node::CloseSquare => false,
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
    if stack.len() < index {
        None
    } else {
        stack.get(stack.len() - index)
    }
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
            Some(Node::LogicPhrase(_)),
            Some(Node::CloseRound),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            stack.pop();
            stack.swap_remove(stack.len() - 2);
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
            Some(Node::LogicPhrase(logic_phrase)),
            Some(Node::OpenSquare),
            Some(Node::LogicPhrase(variable)),
            Some(Node::Slash),
            Some(Node::LogicPhrase(term)),
            Some(Node::CloseSquare),
        ) = (
            back(&stack, 6),
            back(&stack, 5),
            back(&stack, 4),
            back(&stack, 3),
            back(&stack, 2),
            back(&stack, 1),
        ) {
            if variable.get_kind() != LogicVariable {
                Err("TODO")?
            }
            stack.push(Node::LogicPhrase(
                logic_phrase
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
        if token == Some("⇒".to_string()) {
            peek.take();
            stack.push(Node::ImplyTok);
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
            Some(Node::LogicPhrase(logic_phrase)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            namespace
                .set(Thing::LogicPhrase(ident.clone(), logic_phrase.clone()));
            stack.pop();
            stack.pop();
            stack.pop();
        }
        if token == Some("[".to_string()) {
            peek.take();
            stack.push(Node::OpenSquare);
            continue;
        }
        if token == Some("]".to_string()) {
            peek.take();
            stack.push(Node::CloseSquare);
            continue;
        }
        if token == Some("/".to_string()) {
            peek.take();
            stack.push(Node::Slash);
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
        if token == Some(")".to_string()) {
            peek.take();
            stack.push(Node::CloseRound);
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
        if let Some(Node::LogicPhrase(_)) = back(&stack, 1) {
            stack.pop();
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
                Some(Thing::NumericConstant(_, numeric_constant)) => todo!(),
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
