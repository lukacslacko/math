ignore ≔ 'A ⇒ 'B ⇒ 'A
⊦ ignore
distr ≔ ('A ⇒ 'B ⇒ 'C) ⇒ ('A ⇒ 'B) ⇒ 'A ⇒ 'C
⊦ distr
contrapose ≔ (¬'A ⇒ ¬'B) ⇒ 'B ⇒ 'A
⊦ contrapose
ignore['A / 'x]['B / 'x ⇒ 'x]
ignore['A / 'x]['B / 'x]
distr['A / 'x]['B / 'x ⇒ 'x]['C / 'x].MP.MP
|- 'x ⇒ 'x
1 := succ(0)

distr['A / 'x]['B / 'y]['C / 'z]
helper := ignore['A / ('x -> 'y) -> 'x -> 'z]['B / 'y]
ignore['A / helper]['B / 'x -> ('y -> 'z)].MP
distr
    ['A / 'x -> ('y -> 'z)]
    ['B / ('x -> 'y) -> 'x -> 'z]
    ['C / 'y -> (('x -> 'y) -> 'x -> 'z)].MP.MP
inner := distr['A / 'y]['B / 'x -> 'y]['C / 'x -> 'z]
ignore['A / inner]['B / 'x -> ('y -> 'z)].MP
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
|- ('x -> ('y -> 'z)) -> ('y -> ('x -> 'z))
