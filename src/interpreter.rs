use crate::UnitResult;
use crate::lexer::Token as LToken;
use crate::logic;
use crate::peano;
use crate::phrase::*;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Write;
use std::rc::Rc;

#[derive(Debug, Clone)]
struct Token {
    text: Rc<str>,
    location: Rc<str>,
}

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
    fn save(self: &Rc<Namespace>) -> SavedNamespace {
        SavedNamespace {
            namespace: self.clone(),
            i: self.stuff.borrow().len(),
        }
    }
    fn from_saved(saved: SavedNamespace) -> Rc<Namespace> {
        Rc::new(Namespace {
            parent: None,
            stuff: saved.namespace.stuff.borrow()[..saved.i].to_vec().into(),
        })
    }
}

#[derive(Debug, Clone)]
struct SavedNamespace {
    namespace: Rc<Namespace>,
    i: usize,
}

#[derive(Debug, Clone)]
enum Thing {
    LogicPhrase(Rc<str>, Phrase),
    NumericPhrase(Rc<str>, Phrase),
    List(Rc<str>, Vec<Phrase>),
    Lambda(Rc<str>, SavedNamespace, Rc<[Token]>),
}

impl Thing {
    fn name(&self) -> &str {
        match self {
            Self::LogicPhrase(name, _)
            | Self::NumericPhrase(name, _)
            | Self::List(name, _)
            | Self::Lambda(name, _, _) => name,
        }
    }
}

#[derive(Debug)]
enum Node {
    Identifier(Rc<str>),
    LogicPhrase(Phrase),
    NumericPhrase(Phrase),
    List(Vec<Phrase>),
    Lambda(SavedNamespace, Rc<[Token]>),
    QuantifyVar(Phrase),
    Quantify,
    Successor,
    Assertion,
    Return,
    CloseRound,
    OpenRound,
    ImplyTok,
    AssignTok,
    NotTok,
    EqSubs,
    Induction,
    Cut,
    AddTok,
    Multiply,
    EqualsTok,
    Match,
    OpenSquare,
    CloseSquare,
    OpenCurly,
    CloseCurly,
    TryProve,
    Semicolon,
    Slash,
    Dot,
    ModusPonens,
    DistributeQuantification,
    Right,
    Child,
    Left,
}

impl Node {
    fn is_operator(&self) -> bool {
        match self {
            Node::Quantify
            | Node::QuantifyVar(_)
            | Node::Successor
            | Node::Assertion
            | Node::Return
            | Node::OpenRound
            | Node::ImplyTok
            | Node::AssignTok
            | Node::NotTok
            | Node::AddTok
            | Node::Multiply
            | Node::EqualsTok
            | Node::Match
            | Node::OpenSquare
            | Node::OpenCurly
            | Node::Semicolon
            | Node::Slash
            | Node::Dot => true,

            Node::Identifier(_)
            | Node::LogicPhrase(_)
            | Node::NumericPhrase(_)
            | Node::List(_)
            | Node::Lambda(_, _)
            | Node::CloseRound
            | Node::EqSubs
            | Node::Induction
            | Node::Cut
            | Node::CloseSquare
            | Node::CloseCurly
            | Node::TryProve
            | Node::ModusPonens
            | Node::DistributeQuantification
            | Node::Right
            | Node::Child
            | Node::Left => false,
        }
    }
}

thread_local! {
    static STRINGS: RefCell<HashSet<Rc<str>>> = RefCell::default();
}

fn make_str(string: &str) -> Rc<str> {
    STRINGS.with_borrow_mut(|strings| {
        if let Some(rc) = strings.get(string) {
            return rc.clone();
        }
        let rc: Rc<str> = string.into();
        strings.insert(rc.clone());
        rc
    })
}

#[derive(Debug)]
struct Peek<I: Iterator<Item = Token>>(Option<Token>, I);

impl<I: Iterator<Item = Token>> Peek<I> {
    fn peek(&mut self) -> Option<Rc<str>> {
        if self.0.is_none() {
            self.0 = self.1.next();
        }
        self.0.as_ref().map(|token| token.text.clone())
    }
    fn take(&mut self) -> Option<Token> {
        if self.0.is_none() {
            self.0 = self.1.next();
        }
        self.0.take()
    }
    fn location(&self) -> Rc<str> {
        self.0
            .as_ref()
            .map(|token| token.location.clone())
            .unwrap_or_else(|| make_str("eof"))
    }
}

fn back(stack: &[Node], index: usize) -> Option<&Node> {
    stack.iter().nth_back(index - 1)
}

pub fn interpret<'a>(tokens: impl Iterator<Item = &'a LToken>) -> UnitResult {
    let mut peek = Peek(
        None,
        tokens.map(|token| Token {
            text: make_str(&token.text),
            location: make_str(&token.location),
        }),
    );
    let namespace: Rc<Namespace> = Rc::default();
    namespace.set(Thing::NumericPhrase(
        make_str("0"),
        make_numeric_constant_zero(),
    ));
    interpret_middle(&mut peek, namespace, None)
}

fn interpret_middle(
    peek: &mut Peek<impl Iterator<Item = Token>>,
    namespace: Rc<Namespace>,
    ret: Option<&mut Option<Node>>,
) -> UnitResult {
    let mut new_identifiers = HashSet::new();
    interpret_inner(peek, namespace, ret, &mut new_identifiers).map_err(|err| {
        {
            let hint = if new_identifiers.is_empty() {
                "good luck!".to_string()
            } else {
                let mut new_ids = new_identifiers.iter().cloned().collect::<Vec<_>>();
                new_ids.sort();
                format!("implicitly created identifiers: {}, maybe you need to import some of these?", new_ids.join(", "))
            };
            format!("{err} @ {}, hint: {}", peek.location(), hint)
        }
        .into()
    })
}

fn interpret_inner(
    peek: &mut Peek<impl Iterator<Item = Token>>,
    mut namespace: Rc<Namespace>,
    ret: Option<&mut Option<Node>>,
    new_identifiers: &mut HashSet<Rc<str>>,
) -> UnitResult {
    let mut stack = vec![];
    loop {
        // eprintln!("{stack:#?}");
        // let mut line = String::new();
        // std::io::stdin().read_line(&mut line)?;
        let token = peek.peek();
        let token = token.as_deref();
        if token == Some("⛔") {
            Err("stopping the program as requested")?;
        }
        if token == Some("≔") {
            let Some(Node::Identifier(_)) = back(&stack, 1) else {
                Err("missing identifier to assign to")?
            };
            peek.take();
            stack.push(Node::AssignTok);
            continue;
        }
        if let (Some(Node::Quantify), Some(Node::Identifier(ident))) =
            (back(&stack, 2), back(&stack, 1))
        {
            stack
                .push(Node::QuantifyVar(make_numeric_variable(ident.clone())?));
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let Some(Node::Identifier(ident)) = back(&stack, 1) {
            new_identifiers.insert(ident.clone());
            stack.push(Node::NumericPhrase(make_numeric_variable(
                ident.clone(),
            )?));
            stack.swap_remove(stack.len() - 2);
            continue;
        }
        if let (
            Some(Node::OpenRound),
            Some(
                Node::LogicPhrase(_)
                | Node::NumericPhrase(_)
                | Node::List(_)
                | Node::Lambda(_, _),
            ),
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
            Some(
                Node::LogicPhrase(_)
                | Node::NumericPhrase(_)
                | Node::List(_)
                | Node::Lambda(_, _),
            ),
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
                Err(
                    "parent namespace does not exist, this should never happen",
                )?
            };
            namespace = parent;
            stack.pop();
            stack.pop();
            continue;
        }
        if let Some(Node::CloseCurly) = back(&stack, 1) {
            Err("} without matching {")?
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
                Err(format!(
                    "substitution requires a numeric or logic variable before the slash, got '{variable:?}'"
                ))?
            }
            if variable.is_numeric() != term.is_numeric() {
                Err(format!(
                    "substitution requires the variable and the term before and after the slash to be both numeric or both logic, got variable '{variable:?}' and term '{term}'"
                ))?
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
            continue;
        }
        if let (
            Some(Node::LogicPhrase(logic_phrase)),
            Some(Node::OpenSquare),
            Some(Node::NumericPhrase(numeric_term)),
            Some(Node::CloseSquare),
        ) = (
            back(&stack, 4),
            back(&stack, 3),
            back(&stack, 2),
            back(&stack, 1),
        ) {
            stack.push(Node::LogicPhrase(logic::instantiate(
                logic_phrase.clone(),
                numeric_term.clone(),
            )?));
            stack.swap_remove(stack.len() - 5);
            stack.pop();
            stack.pop();
            stack.pop();
            continue;
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
                Err(format!(
                    "substitution requires a numeric or logic variable before the slash, got '{variable:?}'"
                ))?
            }
            if variable.is_numeric() != term.is_numeric() {
                Err(format!(
                    "substitution requires the variable and the term before and after the slash to be both numeric or both logic, got variable '{variable:?}' and term '{term}'"
                ))?
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
            continue;
        }
        if let (
            Some(Node::NumericPhrase(_) | Node::LogicPhrase(_) | Node::List(_)),
            Some(Node::Dot),
            Some(Node::Lambda(saved, tokens)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            let new_namespace = Namespace::from_saved(saved.clone());
            let tokens = tokens.clone();
            stack.pop();
            stack.pop();
            let arg = match stack.pop() {
                Some(Node::NumericPhrase(numeric_phrase)) => {
                    Thing::NumericPhrase(make_str("●"), numeric_phrase)
                }
                Some(Node::LogicPhrase(logic_phrase)) => {
                    Thing::LogicPhrase(make_str("●"), logic_phrase)
                }
                Some(Node::List(list)) => Thing::List(make_str("●"), list),
                _ => unreachable!(),
            };
            new_namespace.set(arg);
            let mut peek = Peek(None, tokens.iter().cloned());
            let mut ret = None;
            interpret_middle(&mut peek, new_namespace, Some(&mut ret))?;
            if let Some(ret) = ret {
                stack.push(ret);
            }
            continue;
        }
        if let (Some(Node::List(list)), Some(Node::Dot), Some(Node::EqSubs)) =
            (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            if list.len() != 3 {
                Err(format!(
                    "⪮ requires three elements in its argument list, a logic phrase and two variables, got {list:?}"
                ))?
            }
            let phrase = list[0].clone();
            let x = list[1].clone();
            let y = list[2].clone();
            if !phrase.is_proposition() {
                Err(format!(
                    "⪮ requires a proposition as the first element in its argument list, got {phrase}"
                ))?
            }
            stack.pop();
            stack.pop();
            stack.pop();
            stack.push(Node::LogicPhrase(peano::eq_subs(phrase, x, y)?));
            continue;
        }
        if let (
            Some(Node::List(list)),
            Some(Node::Dot),
            Some(Node::Induction),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            if list.len() != 2 {
                Err(format!(
                    "↺ requires two elements in its argument list, a logic phrase and a variable, got {list:?}"
                ))?
            }
            let phrase = list[0].clone();
            let x = list[1].clone();
            if !phrase.is_proposition() {
                Err(format!(
                    "↺ requires a proposition as the first element in its argument list, got {phrase}"
                ))?
            }
            stack.pop();
            stack.pop();
            stack.pop();
            stack.push(Node::LogicPhrase(peano::induction(phrase, x)?));
            continue;
        }
        if let (Some(Node::Dot), Some(Node::Cut)) =
            (back(&stack, 2), back(&stack, 1))
        {
            stack.pop();
            stack.pop();
            let mut path = Vec::new();
            // Keep on popping while we get left, right or child.
            while let Some(node) = stack.pop() {
                match node {
                    Node::Left => path.push(Direction::Left),
                    Node::Right => path.push(Direction::Right),
                    Node::Child => path.push(Direction::Child),
                    Node::Semicolon => break,
                    _ => Err(format!(
                        "cut path must consist of ↙, ↘, ↓ tokens after a ;, got {node:?}"
                    ))?,
                }
            }
            let args = match stack.pop() {
                Some(Node::List(args)) => args,
                _ => {
                    Err("cut requires a phrase and a variable before the path")?
                }
            };
            if args.len() != 2 {
                Err(format!(
                    "cut requires two arguments, a phrase and a variable, got {args:?}"
                ))?
            }
            let phrase = args[0].clone();
            let variable = args[1].clone();
            path.reverse();
            let CutResult {
                new_phrase,
                removed,
            } = phrase.cut(&path, variable)?;
            stack.push(Node::List(vec![new_phrase, removed]));
            continue;
        }
        if let (
            Some(Node::LogicPhrase(logic_phrase)),
            Some(Node::DistributeQuantification),
        ) = (back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::LogicPhrase(logic::distribute(
                logic_phrase.clone(),
            )?));
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let (
            Some(Node::LogicPhrase(l)) | Some(Node::NumericPhrase(l)),
            Some(Node::Match),
            Some(Node::LogicPhrase(r)) | Some(Node::NumericPhrase(r)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            if l.is_numeric() != r.is_numeric() {
                Err(
                    "both phrases in a parallel match must be either numeric or logic",
                )?
            }
            let result = r.parallel(l)?;
            stack.push(if r.is_numeric() {
                Node::NumericPhrase(result)
            } else {
                Node::LogicPhrase(result)
            });
            stack.swap_remove(stack.len() - 4);
            stack.pop();
            stack.pop();
            continue;
        }

        if let (
            Some(Node::LogicPhrase(logic_phrase)),
            Some(Node::Dot),
            Some(Node::ModusPonens),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            if logic_phrase.get_kind() != Imply {
                Err(format!(
                    "modus ponens requires an implication, got {logic_phrase}"
                ))?
            }
            if !logic_phrase.clone().get_is_proven() {
                Err(format!(
                    "modus ponens requires a proven implication, got {logic_phrase}"
                ))?
            }
            let antecedent = logic_phrase.get_children().unwrap_two().0;
            if !antecedent.clone().get_is_proven() {
                match antecedent.clone().try_prove() {
                    Ok(_) => {}
                    Err(err) => Err(format!(
                        "modus ponens requires the antecedent to be proven, got {antecedent} which couldn't be proven: {err}"
                    ))?,
                }
            }
            stack.push(Node::LogicPhrase(logic_phrase.clone().modus_ponens()?));
            stack.swap_remove(stack.len() - 4);
            stack.pop();
            stack.pop();
            continue;
        }
        if let (
            Some(Node::LogicPhrase(phrase) | Node::NumericPhrase(phrase)),
            Some(Node::Left),
        ) = (back(&stack, 2), back(&stack, 1))
        {
            let child = phrase.left()?;
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
            let child = phrase.right()?;
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
            let child = phrase.child()?;
            if child.is_proposition() {
                stack.push(Node::LogicPhrase(child.clone()));
            } else {
                stack.push(Node::NumericPhrase(child.clone()));
            }
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let (Some(Node::LogicPhrase(phrase)), Some(Node::TryProve)) =
            (back(&stack, 2), back(&stack, 1))
        {
            let proved_phrase = phrase.clone().try_prove()?;
            stack.push(Node::LogicPhrase(proved_phrase));
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let (Some(Node::List(list)), Some(Node::Left)) =
            (back(&stack, 2), back(&stack, 1))
        {
            if list.is_empty() {
                Err("cannot get head of empty list")?
            }
            let first = list[0].clone();
            stack.pop();
            stack.pop();
            if first.is_proposition() {
                stack.push(Node::LogicPhrase(first));
            } else if first.is_numeric() {
                stack.push(Node::NumericPhrase(first));
            } else {
                unreachable!("list element neither numeric nor logic {first}");
            }
            continue;
        }
        if let (Some(Node::List(list)), Some(Node::Right)) =
            (back(&stack, 2), back(&stack, 1))
        {
            if list.is_empty() {
                Err("cannot get tail of empty list")?
            }
            stack.push(Node::List(list[1..].to_vec()));
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let Some(Node::Dot) = back(&stack, 1) {
            if token == Some("MP") {
                peek.take();
                stack.push(Node::ModusPonens);
                continue;
            }
            if token == Some("⪮") {
                peek.take();
                stack.push(Node::EqSubs);
                continue;
            }
            if token == Some("↺") {
                peek.take();
                stack.push(Node::Induction);
                continue;
            }
            if token == Some("✂") {
                peek.take();
                stack.push(Node::Cut);
                continue;
            }
        }
        if token == Some("λ") {
            peek.take();
            let saved = namespace.save();
            let mut depth = 0;
            let mut tokens = vec![];
            while let Some(token) = peek.take() {
                if &*token.text == "}" {
                    depth -= 1;
                }
                if depth > 0 {
                    tokens.push(token.clone());
                }
                if &*token.text == "{" {
                    depth += 1;
                }
                if depth <= 0 {
                    break;
                }
            }
            if depth != 0 {
                Err("unexpected eof in lambda")?
            }
            stack.push(Node::Lambda(saved, tokens.into()));
            continue;
        }
        if token == Some(".") {
            peek.take();
            stack.push(Node::Dot);
            continue;
        }
        if token == Some("↙") {
            peek.take();
            stack.push(Node::Left);
            continue;
        }
        if token == Some("↘") {
            peek.take();
            stack.push(Node::Right);
            continue;
        }
        if token == Some("↓") {
            peek.take();
            stack.push(Node::Child);
            continue;
        }
        if token == Some("[") {
            peek.take();
            stack.push(Node::OpenSquare);
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
            Some(Node::Multiply),
            Some(Node::NumericPhrase(r)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::NumericPhrase(make_multiply(
                l.clone(),
                r.clone(),
            )?));
            stack.swap_remove(stack.len() - 4);
            stack.pop();
            stack.pop();
            continue;
        }
        if token == Some("*") {
            peek.take();
            stack.push(Node::Multiply);
            continue;
        }
        if let (
            Some(Node::NumericPhrase(l)),
            Some(Node::AddTok),
            Some(Node::NumericPhrase(r)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::NumericPhrase(make_add(l.clone(), r.clone())?));
            stack.swap_remove(stack.len() - 4);
            stack.pop();
            stack.pop();
            continue;
        }
        if token == Some("+") {
            peek.take();
            stack.push(Node::AddTok);
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
        if token == Some("⇅") {
            peek.take();
            stack.push(Node::Match);
            continue;
        }
        if token == Some("⁇") {
            peek.take();
            stack.push(Node::TryProve);
            continue;
        }
        if token == Some("=") {
            peek.take();
            stack.push(Node::EqualsTok);
            continue;
        }
        if token == Some("⇒") {
            peek.take();
            stack.push(Node::ImplyTok);
            continue;
        }
        if token == Some("/") {
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
            Some(Node::QuantifyVar(variable)),
            Some(Node::LogicPhrase(logic_phrase)),
        ) = (back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::LogicPhrase(make_quantify(
                variable.clone(),
                logic_phrase.clone(),
            )?));
            stack.swap_remove(stack.len() - 3);
            stack.pop();
            continue;
        }
        if let (
            Some(Node::List(_)),
            Some(Node::Semicolon),
            Some(Node::LogicPhrase(phrase) | Node::NumericPhrase(phrase)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            let phrase = phrase.clone();
            stack.pop();
            stack.pop();
            let Some(Node::List(mut list)) = stack.pop() else {
                unreachable!()
            };
            list.push(phrase);
            stack.push(Node::List(list));
            continue;
        }
        if let (
            Some(Node::LogicPhrase(l) | Node::NumericPhrase(l)),
            Some(Node::Semicolon),
            Some(Node::LogicPhrase(r) | Node::NumericPhrase(r)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            stack.push(Node::List(vec![l.clone(), r.clone()]));
            stack.swap_remove(stack.len() - 4);
            stack.pop();
            stack.pop();
            continue;
        }
        if token == Some(";") {
            peek.take();
            stack.push(Node::Semicolon);
            continue;
        }
        if token == Some("⇆") {
            peek.take();
            stack.push(Node::DistributeQuantification);
            continue;
        }
        if token == Some("|") {
            peek.take();
            stack.push(Node::Dot);
            continue;
        }
        if let Some(Node::LogicPhrase(phrase) | Node::NumericPhrase(phrase)) =
            back(&stack, 1)
            && token == Some("℻")
        {
            println!("{}\t{:b}", peek.location(), **phrase);
            peek.take();
            continue;
        }
        if let Some(Node::LogicPhrase(phrase) | Node::NumericPhrase(phrase)) =
            back(&stack, 1)
            && token == Some("📜")
        {
            peek.take();
            let proof = phrase.show_proof().unwrap_or_default();
            let mut result = String::new();
            writeln!(result, "Proof of {phrase}:").unwrap();
            for step in proof {
                writeln!(result, " - {} by {}", step.0, step.1).unwrap();
            }
            std::fs::write("proof.txt", result)
                .expect("failed to write proof to proof.txt");
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
            continue;
        }
        if let (
            Some(Node::Identifier(ident)),
            Some(Node::AssignTok),
            Some(Node::List(list)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            namespace.set(Thing::List(ident.clone(), list.clone()));
            stack.pop();
            stack.pop();
            stack.pop();
            continue;
        }
        if let (
            Some(Node::Identifier(ident)),
            Some(Node::AssignTok),
            Some(Node::Lambda(saved, tokens)),
        ) = (back(&stack, 3), back(&stack, 2), back(&stack, 1))
        {
            namespace.set(Thing::Lambda(
                ident.clone(),
                saved.clone(),
                tokens.clone(),
            ));
            stack.pop();
            stack.pop();
            stack.pop();
            continue;
        }
        if let (
            Some(Node::Return),
            Some(Node::LogicPhrase(_) | Node::NumericPhrase(_) | Node::List(_)),
        ) = (back(&stack, 2), back(&stack, 1))
        {
            let Some(ret) = ret else {
                Err("cannot return outside function")?
            };
            *ret = stack.pop();
            stack.pop();
            return Ok(());
        }
        if let (Some(Node::Assertion), Some(Node::LogicPhrase(logic_phrase))) =
            (back(&stack, 2), back(&stack, 1))
        {
            if !logic_phrase.get_is_proven() {
                Err(format!("assertion failed {:b}", **logic_phrase,))?
            }
            stack.pop();
            stack.pop();
            continue;
        }
        if token == Some("]") {
            peek.take();
            stack.push(Node::CloseSquare);
            continue;
        }
        if token == Some(")") {
            peek.take();
            stack.push(Node::CloseRound);
            continue;
        }
        if token == Some("}") {
            peek.take();
            stack.push(Node::CloseCurly);
            continue;
        }
        if let Some(Node::LogicPhrase(_) | Node::NumericPhrase(_)) =
            back(&stack, 1)
        {
            stack.pop();
            continue;
        }
        if token == Some("{") {
            peek.take();
            let arg = namespace.find("●");
            namespace = Namespace {
                parent: Some(namespace.clone()),
                stuff: vec![].into(),
            }
            .into();
            namespace.set(Thing::NumericPhrase(
                make_str("0"),
                make_numeric_constant_zero(),
            ));
            if let Some(arg) = arg {
                namespace.set(arg);
            }
            stack.push(Node::OpenCurly);
            continue;
        }
        if token == Some("⤷") {
            peek.take();
            let Some(ident) = peek.peek() else {
                Err("unexpected eof while importing")?
            };
            if namespace.find(&ident).is_some() {
                Err(format!(
                    "identifier {ident} already exists in namespace, cannot import it"
                ))?
            }
            let Some(parent) = namespace.parent.clone() else {
                Err("cannot import into global namespace")?
            };
            let Some(thing) = parent.find(&ident) else {
                Err(format!(
                    "parent namespace does not contain identifier {ident}, cannot import"
                ))?
            };
            namespace.set(thing);
            peek.take();
            continue;
        }
        if token == Some("⤶") {
            peek.take();
            let Some(ident) = peek.peek() else {
                Err("unexpected eof while exporting")?
            };
            let Some(thing) = namespace.find(&ident) else {
                Err(format!(
                    "namespace does not contain identifier {ident}, cannot export"
                ))?
            };
            let Some(parent) = namespace.parent.clone() else {
                Err("cannot export from global namespace")?
            };
            if parent.find(&ident).is_some() {
                Err(format!(
                    "identifier {ident} already exists in parent namespace, cannot export"
                ))?
            }
            parent.set(thing);
            continue;
        }
        if token == Some("∀") {
            peek.take();
            stack.push(Node::Quantify);
            continue;
        }
        if token == Some("↵") {
            peek.take();
            stack.push(Node::Return);
            continue;
        }
        if token == Some("⊦") {
            peek.take();
            stack.push(Node::Assertion);
            continue;
        }
        if token == Some("(") {
            peek.take();
            stack.push(Node::OpenRound);
            continue;
        }
        if token == Some("𝗦") {
            peek.take();
            stack.push(Node::Successor);
            continue;
        }
        if token == Some("¬") {
            peek.take();
            stack.push(Node::NotTok);
            continue;
        }

        if let Some(top) = back(&stack, 1)
            && !top.is_operator()
        {
            if token.is_none() {
                Err(format!("unexpected eof, top of stack is {top:?}"))?
            }
            Err(format!("syntax error, top of stack is {top:?}"))?
        }
        if token.as_ref().map(|t| t.starts_with('\'')) == Some(true) {
            let token = peek.take();
            stack.push(Node::LogicPhrase(make_logic_variable(
                token.unwrap().text,
            )?));
            continue;
        }
        if token.is_some() {
            let token = peek.take().unwrap();
            match namespace.find(&token.text) {
                Some(Thing::LogicPhrase(_, logic_phrase)) => {
                    stack.push(Node::LogicPhrase(logic_phrase))
                }
                Some(Thing::NumericPhrase(_, numeric_phrase)) => {
                    stack.push(Node::NumericPhrase(numeric_phrase))
                }
                Some(Thing::List(_, list)) => stack.push(Node::List(list)),
                Some(Thing::Lambda(_, saved, tokens)) => {
                    stack.push(Node::Lambda(saved, tokens))
                }
                None => stack.push(Node::Identifier(token.text)),
            }
            continue;
        }
        if !stack.is_empty() {
            Err(format!(
                "unexpected eof, with some things left on stack: {stack:?}"
            ))?
        }
        return Ok(());
    }
}
