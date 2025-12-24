ignore ≔ 'A ⇒ 'B ⇒ 'A
⊦ ignore
distr ≔ ('A ⇒ 'B ⇒ 'C) ⇒ ('A ⇒ 'B) ⇒ 'A ⇒ 'C
⊦ distr
contrapose ≔ (¬'A ⇒ ¬'B) ⇒ 'B ⇒ 'A
⊦ contrapose
ignore['A / 'x]['B / 'x ⇒ 'x]
ignore['A / 'x]['B / 'x]
distr['A / 'x]['B / 'x ⇒ 'x]['C / 'x].MP.MP
('x ⇒ 'x)['x / 'X]
⊦ 'X ⇒ 'X
1 ≔ 𝗦(0)
2 ≔ 𝗦(1)

distr['A / 'x]['B / 'y]['C / 'z]
commute_antecedents ≔ {
    ⤷ ignore
    ⤷ distr

    goal ≔ ('x ⇒ 'y ⇒ 'z) ⇒ 'y ⇒ 'x ⇒ 'z

    p ≔ 'x ⇒ 'y
    q ≔ 'x ⇒ 'z

    ignore['A / ignore['A / p ⇒ q]['B / 'y]]['B / goal↙].MP
    distr['A / goal↙]['B / p ⇒ q]['C / 'y ⇒ p ⇒ q].MP.MP
    ignore['A / distr['A / 'y]['B / p]['C / q]]['B / goal↙].MP
    distr['A / goal↙]['B / 'y ⇒ p ⇒ q]['C / ('y ⇒ p) ⇒ 'y ⇒ q].MP.MP
    ignore['A / ignore['A / 'y]['B / 'x]]['B / goal↙].MP
    distr['A / goal↙]['B / 'y ⇒ p]['C / goal↘].MP.MP

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}

⊦ commute_antecedents
⊦ ('X ⇒ 'Y ⇒ 'Z) ⇒ 'Y ⇒ 'X ⇒ 'Z

ignore['A / 'y ⇒ 'z]['B / 'x]
ignore['A / distr['A / 'x]['B / 'y]['C / 'z]]['B / 'y ⇒ 'z].MP
distr['A / 'y ⇒ 'z]['B / 'x ⇒ ('y ⇒ 'z)]['C / ('x ⇒ 'y) ⇒ ('x ⇒ 'z)].MP.MP
chain ≔ commute_antecedents['X / 'y ⇒ 'z]['Y / 'x ⇒ 'y]['Z / 'x ⇒ 'z].MP
['x / 'X]['y / 'Y]['z / 'Z]
⊦ chain
⊦ ('X ⇒ 'Y) ⇒ ('Y ⇒ 'Z) ⇒ 'X ⇒ 'Z

ignore['A / ¬¬'x]['B / ¬¬¬¬'x]
contrapose['A / ¬¬¬'x]['B / ¬'x]
chain['X / ¬¬'x]['Y / ¬¬¬¬'x ⇒ ¬¬'x]['Z / ¬'x ⇒ ¬¬¬'x].MP.MP
contrapose['A / 'x]['B / ¬¬'x]
chain['X / ¬¬'x]['Y / ¬'x ⇒ ¬¬¬'x]['Z / ¬¬'x ⇒ 'x].MP.MP
('X ⇒ 'X)['X / ¬¬'x]
distr['A / ¬¬'x]['B / ¬¬'x]['C / 'x].MP.MP['x / 'X]
⊦ ¬¬'X ⇒ 'X

(¬¬'X ⇒ 'X)['X / ¬'x]
contrapose['A / ¬¬'x]['B / 'x].MP['x / 'X]
⊦ 'X ⇒ ¬¬'X

recontrapose ≔ {
    ⤷ contrapose
    ⤷ chain
    ⤷ commute_antecedents

    goal ≔ ('x ⇒ 'y) ⇒ ¬'y ⇒ ¬'x

    s ≔ chain['X / ¬¬'x]['Y / 'x]['Z / 'y].MP
    ('X ⇒ ¬¬'X)['X / 'y]
    a ≔ chain['X / ¬¬'x]['Y / 'y]['Z / ¬¬'y]
    q ≔ commute_antecedents['X / a↙]['Y / a↘↙]['Z / a↘↘].MP.MP
    r ≔ chain['X / s↙]['Y / s↘]['Z / q↘].MP.MP
    t ≔ contrapose['A / ¬'x]['B / ¬'y]
    chain['X / r↙]['Y / r↘]['Z / t↘].MP.MP

    ⊦ goal
    goal['x / 'A]['y / 'B]
}

reflexivity ≔ X = X

equals_symmetric ≔ {
    ⤷ commute_antecedents
    ⤷ reflexivity

    goal ≔ x = y ⇒ y = x

    a ≔ x = z; x; y | ⪮[z / x]
    reflexivity[X / x]
    commute_antecedents['X / a↙]['Y / a↘↙]['Z / a↘↘].MP.MP

    ⊦ goal
    goal[x / X][y / Y]
}

equals_transitive ≔ {
    ⤷ chain
    ⤷ equals_symmetric

    goal ≔ x = y ⇒ y = z ⇒ x = z

    a ≔ y = z; y; x | ⪮
    chain['X / x = y]['Y / a↙]['Z / a↘].MP.MP

    ⊦ goal
    goal[x / X][y / Y][z / Z]
}

not_equals_symmetric ≔ {
    ⤷ equals_symmetric
    ⤷ recontrapose

    goal ≔ ¬x = y ⇒ ¬y = x

    equals_symmetric[X / y][Y / x]
    recontrapose['A / y = x]['B / x = y].MP

    ⊦ goal
    goal[x / X][y / Y]
}

peano1 ≔ ∀X¬0 = 𝗦(X)
peano2 ≔ ∀X∀Y𝗦(X) = 𝗦(Y) ⇒ X = Y
peano3 ≔ ∀X X + 0 = X
peano4 ≔ ∀X∀Y X + 𝗦(Y) = 𝗦(X + Y)
peano5 ≔ ∀X X * 0 = 0
peano6 ≔ ∀X∀Y X * 𝗦(Y) = (X * Y) + X

⊦ peano1
⊦ peano2
⊦ peano3
⊦ peano4
⊦ peano5
⊦ peano6

zero_plus_x_eq_x ≔ {
    ⤷ 0
    ⤷ peano3
    ⤷ peano4
    ⤷ commute_antecedents

    goal ≔ 0 + x = x

    peano3[0]
    peano4[0].MP[x].MP
    a ≔ (0 + 𝗦(x) = 𝗦(y)); y; z | ⪮[y / 0 + x][z / x]
    ∀x commute_antecedents['X / a↙]['Y / a↘↙]['Z / a↘↘].MP.MP
    goal; x | ↺.MP.MP[x].MP

    this is an example comment here

    ⊦ goal
    ∀x goal
}

this is also a comment

plus_comm ≔ {
    goal ≔ (x + y) = (y + x)

    ⤷ zero_plus_x_eq_x
    ⤷ peano3
    ⤷ equals_symmetric
    ⤷ equals_transitive

    i ≔ goal; y | ↺

    first prove that x + 0 = 0 + x which is the base case
    p ≔ peano3[x].MP
    a ≔ zero_plus_x_eq_x[x].MP
    e ≔ equals_symmetric[X / a↙][Y / a↘].MP TODO eq_flip(a)
    equals_transitive[X / p↙][Y / p↘][Z / e↘].MP.MP TODO eq_trans(p, e)
    i.MP ℻ 

    a
}
