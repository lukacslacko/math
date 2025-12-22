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
ignore
    ['A / ignore['A / ('x -> 'y) -> 'x -> 'z]['B / 'y]]
    ['B / 'x -> ('y -> 'z)].MP
distr
    ['A / 'x -> ('y -> 'z)]
    ['B / ('x -> 'y) -> 'x -> 'z]
    ['C / 'y -> (('x -> 'y) -> 'x -> 'z)].MP.MP
ignore
    ['A / distr['A / 'y]['B / 'x -> 'y]['C / 'x -> 'z]]
    ['B / 'x -> ('y -> 'z)].MP
distr
    ['A / 'x -> ('y -> 'z)]
    ['B / 'y -> (('x -> 'y) -> 'x -> 'z)]
    ['C / ('y -> ('x -> 'y)) -> ('y -> ('x -> 'z))].MP.MP
ignore
    ['A / ignore['A / 'y]['B / 'x]]
    ['B / 'x -> ('y -> 'z)].MP
distr
    ['A / 'x -> ('y -> 'z)]
    ['B / 'y -> ('x -> 'y)]
    ['C / 'y -> ('x -> 'z)].MP.MP

commute_antecedents := (('x -> ('y -> 'z)) -> ('y -> ('x -> 'z)))
    ['x / 'X]['y / 'Y]['z / 'Z]
|- commute_antecedents

ignore['A / 'y -> 'z]['B / 'x]
ignore['A / distr['A / 'x]['B / 'y]['C / 'z]]['B / 'y -> 'z].MP
distr['A / 'y -> 'z]['B / 'x -> ('y -> 'z)]['C / ('x -> 'y) -> ('x -> 'z)].MP.MP
chain := commute_antecedents['X / 'y -> 'z]['Y / 'x -> 'y]['Z / 'x -> 'z].MP
    ['x / 'X]['y / 'Y]['z / 'Z]
|- chain

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