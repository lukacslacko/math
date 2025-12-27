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

eq_flip ≔ λ{
    ↵equals_symmetric[X / ○↙][Y / ○↘].MP
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

eq_trans ≔ λ{
    ↵equals_transitive[X / ○ⅰ↙][Y / ○ⅰ↘][Z / ○ⅱ↘].MP.MP
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

replace⟪
    /* 
    Arguments: numeric expression, variable, left value, right value
    Result: left value = right value ⇒ expression[var / left] = expression[var / right]
     */
    (X = X)[X / ●ⅰ[●ⅱ / ●ⅲ]]
    commute_ante⟦●ⅰ = ●ⅰ[●ⅱ / A]; A; B | ⪮[A / ●ⅲ][B / ●ⅳ][●ⅱ / ●ⅲ]⟧.MP.MP
⟫

replace⟦𝗦(x); x; X; Y⟧

/* TODO rewrite plus_comm to use the macros */
plus_comm ≔ {
    goal ≔ (x + y) = (y + x)

    ⤷ chain
    ⤷ commute_antecedents
    ⤷ peano3
    ⤷ peano4
    ⤷ equals_symmetric
    ⤷ eq_flip
    ⤷ eq_trans


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
    peano3[x].MP; a.eq_flip | eq_trans

    peano4[x].MP[y].MP

    b ≔ {
        goal ≔ (𝗦(x) + y) = 𝗦(x + y)

        ⤷ chain
        ⤷ commute_antecedents
        ⤷ equals_symmetric
        ⤷ eq_flip
        ⤷ eq_trans
        ⤷ peano3
        ⤷ peano4

        peano3[x].MP.eq_flip
        (X = X)[X / 𝗦(x)]

        peano3[𝗦(x)].MP; 
        (𝗦(y) = 𝗦(x); y; z | ⪮[y / x][z / x + 0].MP.MP | eq_flip)
         | eq_trans

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
    d ≔ replace⟦𝗦(z); z; x + y; y + x⟧
    d_cut ≔ d; z; ↘↙ | ✂
    f ≔ d_cutⅰ; z; w | ⪮[z / d_cutⅱ][w / x + 𝗦(y)].MP.MP

    g ≔ x + 𝗦(y) = z; z; w | ⪮[z / 𝗦(y + x)][w / 𝗦(y) + x].MP

    h ≔ chain['X / f↙]['Y / f↘]['Z / g↘].MP.MP
    ∀y h

    goal; y | ↺.MP.MP[y].MP

    ⊦ goal
    goal
}
plus_comm[x / X][y / Y]

plus_assoc ≔ {
    goal ≔ (x + y) + z = x + (y + z)

    ⤷ peano3
    ⤷ peano4
    ⤷ eq_flip
    ⤷ eq_trans

    peano3[y].MP | eq_flip
    peano3[x + y].MP; 
    replace⟦x + a; a; y; y + 0⟧.MP
     | eq_trans

    step ≔ replace⟦𝗦(a); a; (x + y) + z; x + (y + z)⟧

    peano4[X].MP[Y].MP[X / x + y][Y / z] | eq_flip

    step_cut ≔ step; a; ↘↙ | ✂
    step1 ≔ step_cutⅰ; a; b | ⪮[a / step_cutⅱ][b / (x + y) + 𝗦(z)].MP.MP

    peano4[X].MP[z].MP[X / y] | eq_flip
    peano4[x].MP[y + z].MP | eq_flip; 
    replace⟦x + a; a; 𝗦(y + z); y + 𝗦(z)⟧.MP
     | eq_trans

    step1_cut ≔ step1; a; ↘↘ | ✂
    ∀z(step1_cutⅰ; a; b | ⪮[a / step1_cutⅱ][b / x + (y + 𝗦(z))].MP.MP)

    goal; z | ↺.MP.MP[z].MP
}

plus_assoc[x / X][y / Y][z / Z]

mul_comm ≔ {
    goal ≔ x * y = y * x

    ⤷ 1
    ⤷ peano3
    ⤷ peano4
    ⤷ peano5
    ⤷ peano6
    ⤷ eq_flip
    ⤷ eq_trans

    peano5[0].MP
    peano6[0].MP[x].MP; (peano3[0 * x].MP) | eq_trans
    ∀x commute_ante⟦0 * 𝗦(x) = a; a; b | ⪮[a / 0 * x][b / 0]⟧.MP.MP
    0 * x = 0; x | ↺.MP.MP[x].MP

    peano5[x].MP
    x * 0 = 0; (0 * x = 0 | eq_flip) | eq_trans

    {
        ⤷ 1
        goal ≔ 𝗦(x) = x + 1

        ⤷ peano3
        ⤷ peano4
        ⤷ eq_flip
        ⤷ eq_trans

        (X + Y = Y + X)[X / 0][Y / 1]; (peano3[1].MP) | eq_trans | eq_flip
        (X + Y = Y + X)[X / x][Y / 1]
        replace⟦𝗦(a); a; x + 1; 1 + x⟧.MP; 
        (
        peano4[1].MP[x].MP | eq_flip; 
        (X + Y = Y + X)[X / 1][Y / 𝗦(x)]
         | eq_trans)
         | eq_trans
        b ≔ replace⟦𝗦(a); a; 𝗦(x); x + 1⟧
        b_cut ≔ b; a; ↘↘ | ✂
        ∀x(b_cutⅰ; a; c | ⪮[a / b_cutⅱ][c / 𝗦(x) + 1].MP.MP)

        goal; x | ↺.MP.MP[x].MP
        ⊦ goal
    }
    a ≔ {
        goal ≔ 𝗦(y) * x = (y * x) + x
        ⤷ 1
        ⤷ peano5
        ⤷ peano6
        ⤷ eq_flip
        ⤷ eq_trans

        peano5[y].MP

        peano5[𝗦(y)].MP; 
        ((x + 0 = x)[x / y * 0]; y * 0 = 0 | eq_trans | eq_flip)
         | eq_trans

        b ≔ peano6[X].MP[Y].MP[X / y][Y / x]
        c ≔ 
        replace⟦a + 𝗦(x); a; b↙; b↘⟧.MP; 
        replace⟦((y * x) + y) + a; a; 𝗦(x); x + 1⟧.MP
         | eq_trans
        d ≔ 
        c; 
        ((X + Y) + Z = X + (Y + Z))[X / c↘↙↙][Y / c↘↙↘][Z / c↘↘]
         | eq_trans
        x + y = y + x | eq_flip
        f ≔ 
        ((X + Y) + Z = 
        X + (Y + Z))[X / y][Y / x][Z / 1]
         | eq_flip; 
        replace⟦a + 1; a; y + x; x + y⟧.MP
         | eq_trans; 
        ((x + y) + z = x + (y + z))[z / 1]
         | eq_trans
        g ≔ 
        replace⟦(y * x) + a; a; f↙; f↘⟧.MP; 
        (((X + Y) + Z = X + (Y + Z))[X / y * x][Y / x][Z / y + 1] | eq_flip)
         | eq_trans
        (𝗦(x) = x + 1)[x / y].eq_flip
        m ≔ (
        d; 
        (g; 
        replace⟦((y * x) + x) + a; a; y + 1; 𝗦(y)⟧.MP
         | eq_trans)
         | eq_trans
        ) | eq_flip
        h ≔ replace⟦a + 𝗦(y); a; 𝗦(y) * x; (y * x) + x⟧
        j ≔ peano6[X].MP[Y].MP[X / 𝗦(y)][Y / x] | eq_flip
        h_cut ≔ h; u; ↘↙ | ✂
        /* TODO make macro for substituting equal things in a logic expression at a path */
        k ≔ h_cutⅰ; u; v | ⪮[u / h_cutⅱ][v / j↘].MP.MP
        k_cut ≔ k; u; ↘↘ | ✂
        ∀x(k_cutⅰ; u; v | ⪮[u / k_cutⅱ][v / m↘].MP.MP)

        goal; x | ↺.MP.MP[x].MP
        ⊦ goal
        goal
    }

    a | eq_flip
    peano6[x].MP[y].MP | eq_flip
    n ≔ replace⟦u + x; u; x * y; y * x⟧
    n2 ≔ n↙ ⇒ u = n↘↘; u; v | ⪮[u / n↘↙][v / x * 𝗦(y)].MP.MP
    ∀x(n2↙ ⇒ n2↘↙ = u; u; v | ⪮[u / n2↘↘][v / 𝗦(y) * x].MP.MP)

    goal; y | ↺.MP.MP[y].MP

    ⊦ goal
    goal
}

mul_comm ℻
