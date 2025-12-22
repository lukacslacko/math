ignore ≔ 'A ⇒ 'B ⇒ 'A
⊦ ignore
distr ≔ ('A ⇒ 'B ⇒ 'C) ⇒ ('A ⇒ 'B) ⇒ 'A ⇒ 'C
⊦ distr
contrapose ≔ (¬'A ⇒ ¬'B) ⇒ 'B ⇒ 'A
⊦ contrapose
ignore['A / 'x]['B / 'x ⇒ 'x]
ignore['A / 'x]['B / 'x]
distr['A / 'x]['B / 'x ⇒ 'x]['C / 'x].MP.MP
('x -> 'x)['x / 'X]
|- 'X ⇒ 'X
1 := succ(0)

distr['A / 'x]['B / 'y]['C / 'z]
{
    ⬎ ignore
    ⬎ distr

    goal := ('x -> 'y -> 'z) -> 'y -> 'x -> 'z

    p := 'x -> 'y
    q := 'x -> 'z

    ignore['A / ignore['A / p -> q]['B / 'y]]['B / goal.<].MP
    distr['A / goal.<]['B / p -> q]['C / 'y -> p -> q].MP.MP
    ignore['A / distr['A / 'y]['B / p]['C / q]]['B / goal.<].MP
    distr['A / goal.<]['B / 'y -> p -> q]['C / ('y -> p) -> 'y -> q].MP.MP
    ignore['A / ignore['A / 'y]['B / 'x]]['B / goal.<].MP
    distr['A / goal.<]['B / 'y -> p]['C / goal.>].MP.MP

    |- goal
    commute_antecedents := goal['x / 'X]['y / 'Y]['z / 'Z]
    ⬏ commute_antecedents
}

|- commute_antecedents
|- ('X -> 'Y -> 'Z) -> 'Y -> 'X -> 'Z

ignore['A / 'y -> 'z]['B / 'x]
ignore['A / distr['A / 'x]['B / 'y]['C / 'z]]['B / 'y -> 'z].MP
distr['A / 'y -> 'z]['B / 'x -> ('y -> 'z)]['C / ('x -> 'y) -> ('x -> 'z)].MP.MP
chain := commute_antecedents['X / 'y -> 'z]['Y / 'x -> 'y]['Z / 'x -> 'z].MP
    ['x / 'X]['y / 'Y]['z / 'Z]
|- chain
|- ('X -> 'Y) -> ('Y -> 'Z) -> 'X -> 'Z

ignore['A / ~~'x]['B / ~~~~'x]
contrapose['A / ~~~'x]['B / ~'x]
chain['X / ~~'x]['Y / ~~~~'x -> ~~'x]['Z / ~'x -> ~~~'x].MP.MP
contrapose['A / 'x]['B / ~~'x]
chain['X / ~~'x]['Y / ~'x -> ~~~'x]['Z / ~~'x -> 'x].MP.MP
('X -> 'X)['X / ~~'x]
distr['A / ~~'x]['B / ~~'x]['C / 'x].MP.MP['x / 'X]
|- ~~'X -> 'X

(~~'X -> 'X)['X / ~'x]
contrapose['A / ~~'x]['B / 'x].MP['x / 'X]
|- 'X -> ~~'X
