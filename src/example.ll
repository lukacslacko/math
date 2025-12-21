ignore ≔ 'A ⇒ 'B ⇒ 'A
⊦ ignore
distr ≔ ('A ⇒ 'B ⇒ 'C) ⇒ ('A ⇒ 'B) ⇒ 'A ⇒ 'C
⊦ distr
contrapose ≔ (¬'A ⇒ ¬'B) ⇒ 'B ⇒ 'A
⊦ contrapose
ignore['A / 'x]['B / 'x ⇒ 'x]
ignore['A / 'x]['B / 'x]
distr['A / 'x]['B / 'x ⇒ 'x]['C / 'x].MP.MP
1 := succ(0)
|- 'x ⇒ 'x
