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

this is also a comment

plus_comm ≔ {
    goal ≔ (x + y) = (y + x)

    ⤷ 0
    ⤷ chain
    ⤷ commute_antecedents
    ⤷ peano3
    ⤷ peano4
    ⤷ equals_symmetric
    ⤷ equals_transitive

    i ≔ goal; y | ↺

    first prove that x + 0 = 0 + x which is the base case
    p ≔ peano3[x].MP

    a ≔ {
        ⤷ 0
        ⤷ peano3
        ⤷ peano4
        ⤷ commute_antecedents

        goal ≔ 0 + x = x

        peano3[0]
        peano4[0].MP[x].MP
        a ≔ (0 + 𝗦(x) = 𝗦(y)); y; z | ⪮[y / 0 + x][z / x]

        TODO this should be commute_ante(a)
        ∀x commute_antecedents['X / a↙]['Y / a↘↙]['Z / a↘↘].MP.MP

        goal; x | ↺.MP.MP[x].MP
        ⊦ goal
        goal
    }

    TODO this should be eq_flip(a)
    e ≔ equals_symmetric[X / a↙][Y / a↘].MP

    TODO this should be eq_trans(p, e)
    equals_transitive[X / p↙][Y / p↘][Z / e↘].MP.MP

    peano4[x].MP[y].MP

    b ≔ {
        goal ≔ (𝗦(x) + y) = 𝗦(x + y)

        ⤷ 0
        ⤷ chain
        ⤷ commute_antecedents
        ⤷ equals_symmetric
        ⤷ equals_transitive
        ⤷ peano3
        ⤷ peano4

        peano3[𝗦(x)].MP

        TODO this should be eq_flip(peano3[x].MP)
        p3x ≔ peano3[x].MP
        equals_symmetric[X / p3x↙][Y / p3x↘].MP

        (X = X)[X / 𝗦(x)]
        𝗦(y) = 𝗦(x); y; z | ⪮[y / x][z / x + 0].MP.MP
        equals_symmetric[X / 𝗦(x + 0)][Y / 𝗦(x)].MP
        equals_transitive[X / 𝗦(x) + 0][Y / 𝗦(x)][Z / 𝗦(x + 0)].MP.MP

        i ≔ goal; y | ↺

        peano4[𝗦(x)].MP[y].MP
        a ≔ 𝗦(x) + 𝗦(y) = 𝗦(z); z; w | ⪮[z / 𝗦(x) + y][w / 𝗦(x + y)]
        b ≔ commute_antecedents['X / a↙]['Y / a↘↙]['Z / a↘↘].MP.MP

        equals_transitive[X / 𝗦(𝗦(x) + y)][Y / 𝗦(𝗦(x + y))][Z / 𝗦(x) + 𝗦(y)]

        equals_symmetric[X / x + 𝗦(y)][Y / 𝗦(x + y)].MP

        c ≔ 𝗦(x) + 𝗦(y) = 𝗦(z); z; w | ⪮[z / 𝗦(x + y)][w / x + 𝗦(y)].MP

        ∀y chain['X / b↙]['Y / b↘]['Z / c↘].MP.MP

        i.MP.MP[y].MP

        ⊦ goal
        goal
    }

    b[x / X][y / Y][X / y][Y / x]
    equals_symmetric[X / 𝗦(y) + x][Y / 𝗦(y + x)].MP

    c ≔ 𝗦(x + y) = 𝗦(z); z; w | ⪮[z / x + y][w / y + x]
    (X = X)[X / 𝗦(x + y)]
    d ≔ commute_antecedents['X / c↙]['Y / c↘↙]['Z / c↘↘].MP.MP

    d has the value(((x + y) = (y + x)) ⇒ (𝗦((x + y)) = 𝗦((y + x))))
    TODO split would be helpful here by replacing right left right in d by z
    f ≔ x + y = y + x ⇒ z = 𝗦(y + x); z; w | ⪮[z / 𝗦(x + y)][w / x + 𝗦(y)].MP.MP

    g ≔ x + 𝗦(y) = z; z; w | ⪮[z / 𝗦(y + x)][w / 𝗦(y) + x].MP

    TODO this would also be better as a macro deduct(f, g)
    h ≔ chain['X / f↙]['Y / f↘]['Z / g↘].MP.MP
    ∀y h

    i.MP.MP[y].MP

    ⊦ goal
    goal
}

plus_comm ℻
