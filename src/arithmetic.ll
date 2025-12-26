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
commute_antecedents
commute_ante⟪
    ‼ commute_antecedents
    commute_antecedents['X / ●↙]['Y / ●↘↙]['Z / ●↘↘]
⟫

chain ≔ {
    goal ≔ ('x ⇒ 'y) ⇒ ('y ⇒ 'z) ⇒ 'x ⇒ 'z

    ⤷ ignore
    ⤷ distr

    ignore['A / 'y ⇒ 'z]['B / 'x]
    ignore['A / distr['A / 'x]['B / 'y]['C / 'z]]['B / 'y ⇒ 'z].MP
    commute_ante⟦distr['A / 'y ⇒ 'z]['B / 'x ⇒ ('y ⇒ 'z)]['C / ('x ⇒ 'y) ⇒ ('x ⇒ 'z)].MP.MP⟧.MP

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⊦ chain
⊦ ('X ⇒ 'Y) ⇒ ('Y ⇒ 'Z) ⇒ 'X ⇒ 'Z

deduce⟪
    ‼ chain
    chain['X / ●ⅰ↙]['Y / ●ⅰ↘]['Z / ●ⅱ↘].MP.MP
⟫

deduce⟦
    deduce⟦
        ignore['A / ¬¬'x]['B / ¬¬¬¬'x];
        contrapose['A / ¬¬¬'x]['B / ¬'x]
    ⟧;
    contrapose['A / 'x]['B / ¬¬'x]
⟧
('X ⇒ 'X)['X / ¬¬'x]
distr['A / ¬¬'x]['B / ¬¬'x]['C / 'x].MP.MP['x / 'X]
⊦ ¬¬'X ⇒ 'X

(¬¬'X ⇒ 'X)['X / ¬'x]
contrapose['A / ¬¬'x]['B / 'x].MP['x / 'X]
⊦ 'X ⇒ ¬¬'X

recontrapose ≔ {
    ⤷ chain
    ⤷ contrapose

    goal ≔ ('x ⇒ 'y) ⇒ ¬'y ⇒ ¬'x

    s ≔ chain['X / ¬¬'x]['Y / 'x]['Z / 'y].MP
    ('X ⇒ ¬¬'X)['X / 'y]
    q ≔ commute_ante⟦chain['X / ¬¬'x]['Y / 'y]['Z / ¬¬'y]⟧.MP.MP
    deduce⟦
        deduce⟦s; q⟧;
        contrapose['A / ¬'x]['B / ¬'y]
    ⟧

    ⊦ goal
    goal['x / 'A]['y / 'B]
}

(X = X)[X / x]
equals_symmetric ≔ commute_ante⟦x = z; x; y | ⪮[z / x]⟧.MP.MP[x / X][y / Y]

eq_flip⟪
    ‼ equals_symmetric
    equals_symmetric[X / ●↙][Y / ●↘].MP
⟫

equals_transitive ≔ {
    ⤷ chain
    ⤷ equals_symmetric

    goal ≔ x = y ⇒ y = z ⇒ x = z

    a ≔ y = z; y; x | ⪮
    chain['X / x = y]['Y / a↙]['Z / a↘].MP.MP

    ⊦ goal
    goal[x / X][y / Y][z / Z]
}

eq_trans⟪
    ‼ equals_transitive
    equals_transitive[X / ●ⅰ↙][Y / ●ⅰ↘][Z / ●ⅱ↘].MP.MP
⟫

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

replace⟪
    (X = X)[X / ●ⅰ[●ⅱ / ●ⅲ]]
    commute_ante⟦●ⅰ = ●ⅰ[●ⅱ / A]; A; B | ⪮[A / ●ⅲ][B / ●ⅳ][●ⅱ / ●ⅲ]⟧.MP.MP
⟫

plus_comm ≔ {
    goal ≔ (x + y) = (y + x)

    ⤷ chain
    ⤷ commute_antecedents
    ⤷ peano3
    ⤷ peano4
    ⤷ equals_symmetric
    ⤷ equals_transitive


    a ≔ {
        ⤷ peano3
        ⤷ peano4
        ⤷ commute_antecedents

        goal ≔ 0 + x = x

        peano3[0]
        peano4[0].MP[x].MP
        a ≔ (0 + 𝗦(x) = 𝗦(y)); y; z | ⪮[y / 0 + x][z / x]

        ∀x commute_ante⟦a⟧.MP.MP

        goal; x | ↺.MP.MP[x].MP
        ⊦ goal
        goal
    }
    eq_trans⟦peano3[x].MP; eq_flip⟦a⟧⟧

    peano4[x].MP[y].MP

    b ≔ {
        goal ≔ (𝗦(x) + y) = 𝗦(x + y)

        ⤷ chain
        ⤷ commute_antecedents
        ⤷ equals_symmetric
        ⤷ equals_transitive
        ⤷ peano3
        ⤷ peano4

        eq_flip⟦peano3[x].MP⟧
        (X = X)[X / 𝗦(x)]

        eq_trans⟦
            peano3[𝗦(x)].MP;

            eq_flip⟦𝗦(y) = 𝗦(x); y; z | ⪮[y / x][z / x + 0].MP.MP⟧
        ⟧

        i ≔ goal; y | ↺

        peano4[𝗦(x)].MP[y].MP
        a ≔ 𝗦(x) + 𝗦(y) = 𝗦(z); z; w | ⪮[z / 𝗦(x) + y][w / 𝗦(x + y)]
        b ≔ commute_antecedents['X / a↙]['Y / a↘↙]['Z / a↘↘].MP.MP

        equals_transitive[X / 𝗦(𝗦(x) + y)][Y / 𝗦(𝗦(x + y))][Z / 𝗦(x) + 𝗦(y)]

        equals_symmetric[X / x + 𝗦(y)][Y / 𝗦(x + y)].MP

        c ≔ 𝗦(x) + 𝗦(y) = 𝗦(z); z; w | ⪮[z / 𝗦(x + y)][w / x + 𝗦(y)].MP

        ∀y deduce⟦b; c⟧

        i.MP.MP[y].MP

        ⊦ goal
        goal
    }

    b[x / X][y / Y][X / y][Y / x]
    equals_symmetric[X / 𝗦(y) + x][Y / 𝗦(y + x)].MP

    replace⟦𝗦(z); z; x + y; y + x⟧

    d has the value(((x + y) = (y + x)) ⇒ (𝗦((x + y)) = 𝗦((y + x))))
    TODO split would be helpful here by replacing right left right in d by z
    f ≔ x + y = y + x ⇒ z = 𝗦(y + x); z; w | ⪮[z / 𝗦(x + y)][w / x + 𝗦(y)].MP.MP

    g ≔ x + 𝗦(y) = z; z; w | ⪮[z / 𝗦(y + x)][w / 𝗦(y) + x].MP

    TODO this would also be better as a macro deduct(f, g)
    h ≔ chain['X / f↙]['Y / f↘]['Z / g↘].MP.MP
    ∀y h

    goal; y | ↺.MP.MP[y].MP

    ⊦ goal
    goal
}

{
    goal ≔ X = Y ⇒ 𝗦(X) = 𝗦(Y)

    ⤷ commute_antecedents

    a ≔ 𝗦(X) = 𝗦(Z); Z; Y | ⪮[Z / X]
    (X = X)[X / 𝗦(X)]
    commute_antecedents['X / a↙]['Y / a↘↙]['Z / a↘↘].MP.MP

    ⊦ goal
}

plus_assoc ≔ {
    goal ≔ (x + y) + z = x + (y + z)

    ⤷ peano3
    ⤷ peano4
    ⤷ equals_symmetric
    ⤷ equals_transitive

    peano3[x + y].MP
    peano3[y].MP
    equals_symmetric[X / y + 0][Y / y].MP
    (X = X)[X / x + y]
    x + y = x + z; z; w | ⪮[z / y][w / y + 0].MP.MP
    equals_transitive[X / (x + y) + 0][Y / x + y][Z / x + (y + 0)].MP.MP

    a ≔ peano4[X].MP[Y].MP[X / x + y][Y / z]
    equals_symmetric[X / a↙][Y / a↘].MP
    peano4[X].MP[Y].MP[X / y][Y / z]
    peano4[x].MP[y + z].MP
    (X = Y ⇒ Y = X)[X / y + 𝗦(z)][Y / 𝗦(y + z)].MP
    x + u = 𝗦(x + (y + z)); u; v | ⪮[v / y + 𝗦(z)][u / 𝗦(y + z)].MP.MP
    (X = Y ⇒ Y = X)[X / x + (y + 𝗦(z))][Y / 𝗦(x + (y + z))].MP

    b ≔ (X = Y ⇒ 𝗦(X) = 𝗦(Y))[X / (x + y) + z][Y / x + (y + z)]
    (x + y) + z = x + (y + z) ⇒ u = 𝗦(x + (y + z)); u; v | ⪮
    [u / 𝗦((x + y) + z)][v / (x + y) + 𝗦(z)].MP.MP
    c ≔ (x + y) + z = x + (y + z) ⇒ (x + y) + 𝗦(z) = u; u; v | ⪮
    [u / 𝗦(x + (y + z))][v / x + (y + 𝗦(z))].MP.MP
    ∀y c

    goal; z | ↺.MP.MP[z].MP

    ⊦ goal
    goal
}

plus_assoc ℻
plus_assoc📜
