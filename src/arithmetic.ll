ignore ≔ 'A ⇒ 'B ⇒ 'A
⊦ ignore
distr ≔ ('A ⇒ 'B ⇒ 'C) ⇒ ('A ⇒ 'B) ⇒ 'A ⇒ 'C
⊦ distr
contrapose ≔ (¬'A ⇒ ¬'B) ⇒ 'B ⇒ 'A
⊦ contrapose
{
    goal ≔ 'x ⇒ 'x

    ⤷ ignore
    ⤷ distr

    ignore['A / 'x]['B / 'x ⇒ 'x]
    ignore['A / 'x]['B / 'x]
    distr['A / 'x]['B / 'x ⇒ 'x]['C / 'x].MP.MP

    ⊦ goal
    goal['x / 'X]
}

1 ≔ 𝗦(0)
2 ≔ 𝗦(1)

commute_antecedents ≔ {
    ⤷ ignore
    ⤷ distr

    goal ≔ ('x ⇒ 'y ⇒ 'z) ⇒ 'y ⇒ 'x ⇒ 'z

    p ≔ 'x ⇒ 'y
    q ≔ 'x ⇒ 'z

    distr['A / 'x]['B / 'y]['C / 'z]
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

commute_ante ≔ λ{
    /*
    Argument: A ⇒ B ⇒ c

    Swaps A ∧ B, assumes the argument is proven.

    Result: B ⇒ A ⇒ C
     */
    ↵ commute_antecedents['X / ●↙]['Y / ●↘↙]['Z / ●↘↘].MP
}

chain ≔ {
    goal ≔ ('x ⇒ 'y) ⇒ ('y ⇒ 'z) ⇒ 'x ⇒ 'z

    ⤷ ignore
    ⤷ distr
    ⤷ commute_ante

    ignore['A / 'y ⇒ 'z]['B / 'x]
    ignore['A / distr['A / 'x]['B / 'y]['C / 'z]]['B / 'y ⇒ 'z].MP
    distr['A / 'y ⇒ 'z]['B / 'x ⇒ ('y ⇒ 'z)]['C / ('x ⇒ 'y) ⇒ ('x ⇒ 'z)].MP.MP | commute_ante

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⊦ chain
⊦ ('X ⇒ 'Y) ⇒ ('Y ⇒ 'Z) ⇒ 'X ⇒ 'Z

chain' ≔ chain['X / 'x]['Y / 'y]['Z / 'z].commute_ante['x / 'X]['y / 'Y]['z / 'Z]

deduce ≔ λ{
    /*
    Argument: P ⇒ Q; Q ⇒ R
    Assumption: both implications are proven
    Returns: P ⇒ R
     */
    ↵ chain['X / ●ⅰ↙]['Y / ●ⅰ↘]['Z / ●ⅱ↘].MP.MP
}

false_implies_anything ≔ {
    goal ≔ ¬'B ⇒ 'B ⇒ 'A

    ⤷ ignore
    ⤷ deduce
    ⤷ contrapose
    ⤷ commute_ante

    ignore['A / 'X]['B / 'Y]['X / ¬'B]['Y / ¬'A];
    contrapose | deduce

    ⊦ goal
    goal.commute_ante
    goal
}

from_false ≔ λ{
    /*
    Argument: P ⇒ Q
    Assumption:¬P is proven
    Result: P ⇒ Q now proven
     */
    ↵ false_implies_anything['B / ●↙]['A / ●↘].MP
}

{
    goal ≔ ¬¬'x ⇒ 'x

    ⤷ ignore
    ⤷ contrapose
    ⤷ deduce
    ⤷ distr

    ignore['A / ¬¬'x]['B / ¬¬¬¬'x];
    contrapose['A / ¬¬¬'x]['B / ¬'x] | deduce;
    contrapose['A / 'x]['B / ¬¬'x] | deduce

    ('X ⇒ 'X)['X / ¬¬'x]
    distr['A / ¬¬'x]['B / ¬¬'x]['C / 'x].MP.MP
    ⊦ goal
    goal
    goal['x / 'X]
}

{
    goal ≔ 'x ⇒ ¬¬'x

    ⤷ contrapose

    (¬¬'X ⇒ 'X)['X / ¬'x]
    contrapose['A / ¬¬'x]['B / 'x].MP
    ⊦ goal
    goal['x / 'X]
}

recontrapose ≔ {
    ⤷ chain
    ⤷ commute_ante
    ⤷ contrapose
    ⤷ deduce

    goal ≔ ('x ⇒ 'y) ⇒ ¬'y ⇒ ¬'x

    s ≔ chain['X / ¬¬'x]['Y / 'x]['Z / 'y].MP
    ('X ⇒ ¬¬'X)['X / 'y]
    q ≔ chain['X / ¬¬'x]['Y / 'y]['Z / ¬¬'y] | commute_ante.MP

    s; q | deduce;
    contrapose['A / ¬'x]['B / ¬'y] | deduce

    ⊦ goal
    goal['x / 'A]['y / 'B]
}

contra ≔ λ{
    /*
    Argument:¬P ⇒ ¬Q
    Returns:(¬P ⇒ ¬Q) ⇒ (Q ⇒ P)
     */
    ↵ contrapose['A / ●↙↓]['B / ●↘↓]
}

recontra ≔ λ{
    /*
    Argument: P ⇒ Q
    Returns:(P ⇒ Q) ⇒ (¬Q ⇒ ¬P)
     */
    ↵ recontrapose['A / ●↙]['B / ●↘]
}

preneg_flip ≔ {
    goal ≔ (¬'x ⇒ 'y) ⇒ (¬'y ⇒ 'x)

    ⤷ chain
    ⤷ commute_ante
    ⤷ contrapose
    ⤷ deduce

    chain['X / ¬'x]['Y / 'y]['Z / ¬¬'y] | commute_ante.MP;
    contrapose['A / 'x]['B / ¬'y] | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
flip_preneg ≔ λ{
    /*
    Argument:¬P ⇒ Q
    Returns:(¬P ⇒ Q) ⇒ (¬Q ⇒ P)
     */
    ↵ preneg_flip['X / ●↙↓]['Y / ●↘]
}
postneg_flip ≔ {
    goal ≔ ('x ⇒ ¬'y) ⇒ 'y ⇒ ¬'x

    ⤷ chain
    ⤷ recontrapose
    ⤷ deduce

    recontrapose['A / 'x]['B / ¬'y];
    chain['X / 'y]['Y / ¬¬'y]['Z / ¬'x].MP | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
flip_postneg ≔ λ{
    /*
    Argument: P ⇒ ¬Q
    Returns:(P ⇒ ¬Q) ⇒ (Q ⇒ ¬P)
     */
    ↵ postneg_flip['X / ●↙]['Y / ●↘↓]
}


y_impl_or ≔ {
    goal ≔ 'y ⇒ 'x ∨ 'y

    ⤷ ignore
    ignore['A / 'y]['B / ¬'x]

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}

x_impl_or ≔ {
    goal ≔ 'x ⇒ 'x ∨ 'y
    goal⁇

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}

and_impl_x ≔ {
    goal ≔ 'x ∧ 'y ⇒ 'x

    ⤷ false_implies_anything
    ⤷ recontra
    ⤷ deduce
    ⤷ commute_ante

    false_implies_anything['A / ¬'y]['B / 'x] | recontra.MP;
    ¬¬'x ⇒ 'x | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}

and_impl_y ≔ {
    goal ≔ 'x ∧ 'y ⇒ 'y

    ⤷ ignore
    ⤷ recontra
    ⤷ deduce

    ignore['A / ¬'y]['B / 'x] | recontra.MP;
    ¬¬'y ⇒ 'y | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}

x_impl_y_impl_and ≔ {
    goal ≔ 'x ⇒ 'y ⇒ 'x ∧ 'y

    ⤷ commute_ante
    ⤷ flip_postneg
    ⤷ deduce

    a ≔ ('X ⇒ 'X)['X / 'x ⇒ ¬'y] | commute_ante
    b ≔ ('x ⇒ ¬'y) ⇒ ¬'y | flip_postneg
    a; b | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}

xyz_impl_and ≔ {
    goal ≔ ('x ⇒ 'y ⇒ 'z) ⇒ 'x ∧ 'y ⇒ 'z

    ⤷ ignore
    ⤷ commute_ante
    ⤷ distr
    ⤷ deduce

    b ≔ 'x ∧ 'y

    ignore['A / goal↙]['B / b];
    distr['A / b]['B / 'x]['C / 'y ⇒ 'z] | deduce | commute_ante.MP;
    distr['A / b]['B / 'y]['C / 'z] | deduce | commute_ante.MP

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}

and_impl_xyz ≔ {
    goal ≔ ('x ∧ 'y ⇒ 'z) ⇒ 'x ⇒ 'y ⇒ 'z

    ⤷ chain
    ⤷ commute_ante

    chain['X / 'x]['Y ⇒ 'Z / chain['X / 'y]['Y / 'x ∧ 'y]['Z / 'z]].MP.MP.commute_ante

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}

and_comm ≔ {
    goal ≔ 'x ∧ 'y ⇒ 'y ∧ 'x

    ⤷ recontrapose

    recontrapose['A / 'y ⇒ ¬'x]['B / 'x ⇒ ¬'y].MP

    ⊦ goal
}

and_assoc ≔ {
    goal ≔ ('x ∧ 'y)∧ 'z ⇒ 'x ∧('y ∧ 'z)

    ⤷ xyz_impl_and
    ⤷ chain
    ⤷ commute_ante
    ⤷ deduce
    ⤷ recontra

    chain['X / 'x]['Y ⇒ 'Z / (¬¬'X ⇒ 'X)['X / 'y ⇒ ¬'z]].commute_ante.MP;
    xyz_impl_and['X / 'x]['Y / 'y]['Z / ¬'z] | deduce | recontra.MP

    ⊦ goal
}

demorgan_or ≔ {
    goal ≔ 'x ∨ 'y ⇒ ¬(¬'x ∧¬'y)

    ⤷ chain'

    a ≔ chain'['X / ¬'x]['Y ⇒ 'Z / 'y ⇒ ¬¬'y].MP
    chain'['X ⇒ 'Y / a]['X ⇒ 'Z / goal].MP.MP

    ⊦ goal
}

reduce ≔ λ{
    /*
    Arguments: P ⇒ Q; Q'
    Assumptions: P ⇒ Q is a proven theorem ∧ Q' has the shape of Q
    Result: P[Q / Q'] ⇒ Q', the backwards application of the theorem to Q'
     */
    ↵ ●ⅰ[●ⅰ↘ / ●ⅱ]
}

apply ≔ λ{
    /*
    Arguments: P ⇒ Q; P'
    Assumptions: P ⇒ Q is a proven theorem ∧ P' has the shape of P
    Result: P' ⇒ Q[P / P'], the application of the theorem to P'
     */
    ↵ ●ⅰ[●ⅰ↙ / ●ⅱ]
}

demorgan_and ≔ {
    goal ≔ 'x ∧ 'y ⇒ ¬(¬'x ∨¬'y)

    ⤷ reduce
    ⤷ chain
    ⤷ recontrapose

    a ≔ recontrapose; goal | reduce
    chain; a↙ | reduce.MP
    a.MP

    ⊦ goal
}

equals_symmetric ≔ {
    goal ≔ x = y ⇒ y = x

    ⤷ commute_ante

    (X = X)[X / x]
    x = z; x; y | ⪮[z / x] | commute_ante.MP
    ⊦ goal
    goal[x / X][y / Y]
}

eq_flip ≔ λ{
    /*
    Argument: a = b
    Returns: b = a
     */
    ↵ equals_symmetric[X / ●↙][Y / ●↘].MP
}

neq_flip ≔ λ{
    /*
    Argument:¬a = b
    Returns:¬b = a
     */
    ↵ equals_symmetric.recontra.MP[X / ●↓↘][Y / ●↓↙].MP
}

equals_transitive ≔ {
    ⤷ chain
    ⤷ equals_symmetric

    goal ≔ x = y ⇒ y = z ⇒ x = z

    a ≔ y = z; y; x | ⪮
    chain['X / x = y]['Y ⇒ 'Z / a].MP.MP

    ⊦ goal
    goal[x / X][y / Y][z / Z]
}

eq_trans ≔ λ{
    ↵ equals_transitive[X = Y / ●ⅰ][Y = Z / ●ⅱ].MP.MP
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

peano1 ≔ ¬0 = 𝗦(X)
peano2 ≔ 𝗦(X) = 𝗦(Y) ⇒ X = Y
peano3 ≔ X + 0 = X
peano4 ≔ X + 𝗦(Y) = 𝗦(X + Y)
peano5 ≔ X * 0 = 0
peano6 ≔ X * 𝗦(Y) = (X * Y) + X

⊦ peano1
⊦ peano2
⊦ peano3
⊦ peano4
⊦ peano5
⊦ peano6

{
    ⤷ peano1
    ⤷ peano3
    ⤷ peano4
    ⤷ peano5
    ⤷ peano6

    ⤷ eq_flip
    ⤷ neq_flip
    peano1[X / x].neq_flip[x / X]
    peano3[X / x].eq_flip[x / X]
    peano4[X / x][Y / y].eq_flip[x / X][y / Y]
    peano5[X / x].eq_flip[x / X]
    peano6[X / x][Y / y].eq_flip[x / X][y / Y]
}
0 = y * 0⁇

replace ≔ λ{
    /*
    Arguments: numeric expression, variable, left value, right value
    Result: left value = right value ⇒ expression[var / left] = expression[var / right]
     */
    (X = X)[X / ●ⅰ[●ⅱ / ●ⅲ]]
    ↵ ●ⅰ = ●ⅰ[●ⅱ / A]; A; B | ⪮[A / ●ⅲ][B / ●ⅳ][●ⅱ / ●ⅲ] | commute_ante.MP
}

𝗦(x); x; X; Y | replace

add_comm ≔ {
    goal ≔ (x + y) = (y + x)

    ⤷ chain
    ⤷ commute_ante
    ⤷ commute_antecedents
    ⤷ equals_transitive
    ⤷ deduce
    ⤷ peano3
    ⤷ peano4
    ⤷ equals_symmetric
    ⤷ eq_flip
    ⤷ eq_trans
    ⤷ replace

    a ≔ {
        ⤷ peano3
        ⤷ peano4
        ⤷ commute_ante

        goal ≔ 0 + x = x

        peano3[X / 0]
        peano4[X / 0][Y / x]
        a ≔ (0 + 𝗦(x) = 𝗦(y)); y; z | ⪮[y / 0 + x][z / x]

        ∀x a.commute_ante.MP

        goal; x | ↺.MP.MP[x].MP
        ⊦ goal
        goal
    }
    peano3[X / x]; a.eq_flip | eq_trans

    peano4[X / x][Y / y]

    b ≔ {
        goal ≔ (𝗦(x) + y) = 𝗦(x + y)

        ⤷ chain
        ⤷ commute_antecedents
        ⤷ deduce
        ⤷ equals_symmetric
        ⤷ equals_transitive
        ⤷ eq_flip
        ⤷ eq_trans
        ⤷ peano3
        ⤷ peano4

        peano3[X / x].eq_flip
        (X = X)[X / 𝗦(x)]

        peano3[X / 𝗦(x)];
        (𝗦(y) = 𝗦(x); y; z | ⪮[y / x][z / x + 0].MP.MP | eq_flip) | eq_trans

        i ≔ goal; y | ↺

        peano4[X / 𝗦(x)][Y / y]
        a ≔ 𝗦(x) + 𝗦(y) = 𝗦(z); z; w | ⪮[z / 𝗦(x) + y][w / 𝗦(x + y)]
        b ≔ commute_antecedents['X / a↙]['Y / a↘↙]['Z / a↘↘].MP.MP

        equals_transitive[X / 𝗦(𝗦(x) + y)][Y / 𝗦(𝗦(x + y))][Z / 𝗦(x) + 𝗦(y)]

        equals_symmetric[X / x + 𝗦(y)][Y / 𝗦(x + y)].MP

        c ≔ 𝗦(x) + 𝗦(y) = 𝗦(z); z; w | ⪮[z / 𝗦(x + y)][w / x + 𝗦(y)].MP

        ∀y(b; c | deduce)

        i.MP.MP[y].MP

        ⊦ goal
        goal
    }

    b[x / X][y / Y][X / y][Y / x]
    equals_symmetric[X / 𝗦(y) + x][Y / 𝗦(y + x)].MP
    d ≔ 𝗦(z); z; x + y; y + x | replace
    d_cut ≔ d; z; ↘↙ | ✂
    f ≔ d_cutⅰ; z; w | ⪮[z / d_cutⅱ][w / x + 𝗦(y)].MP.MP

    g ≔ x + 𝗦(y) = z; z; w | ⪮[z / 𝗦(y + x)][w / 𝗦(y) + x].MP

    h ≔ chain['X / f↙]['Y / f↘]['Z / g↘].MP.MP
    ∀y h

    goal; y | ↺.MP.MP[y].MP

    ⊦ goal
    goal[x / X][y / Y]
}

add_assoc ≔ {
    goal ≔ (x + y) + z = x + (y + z)

    ⤷ peano3
    ⤷ peano4
    ⤷ eq_flip
    ⤷ eq_trans
    ⤷ replace

    peano3[X / y] | eq_flip
    peano3[X / x + y];
    (x + a; a; y; y + 0 | replace.MP)
     | eq_trans

    step ≔ 𝗦(a); a; (x + y) + z; x + (y + z) | replace

    peano4[X / x + y][Y / z] | eq_flip

    step_cut ≔ step; a; ↘↙ | ✂
    step1 ≔ step_cutⅰ; a; b | ⪮[a / step_cutⅱ][b / (x + y) + 𝗦(z)].MP.MP

    peano4[X / y][Y / z] | eq_flip
    peano4[X / x][Y / y + z] | eq_flip;
    (x + a; a; 𝗦(y + z); y + 𝗦(z) | replace.MP)
     | eq_trans

    step1_cut ≔ step1; a; ↘↘ | ✂
    ∀z(step1_cutⅰ; a; b | ⪮[a / step1_cutⅱ][b / x + (y + 𝗦(z))].MP.MP)

    goal; z | ↺.MP.MP[z].MP
    goal.eq_flip[x / X][y / Y][z / Z]
    goal[x / X][y / Y][z / Z]
}

mul_comm ≔ {
    goal ≔ x * y = y * x

    ⤷ peano3
    ⤷ peano4
    ⤷ peano5
    ⤷ peano6
    ⤷ commute_ante
    ⤷ eq_flip
    ⤷ eq_trans
    ⤷ replace

    peano5[X / 0]
    peano6[X / 0][Y / x]; peano3[X / 0 * x] | eq_trans
    ∀x(0 * 𝗦(x) = a; a; b | ⪮[a / 0 * x][b / 0] | commute_ante.MP)
    0 * x = 0; x | ↺.MP.MP[x].MP

    peano5[X / x]
    x * 0 = 0; (0 * x = 0 | eq_flip) | eq_trans

    {
        goal ≔ 𝗦(x) = x + 1

        ⤷ peano3
        ⤷ peano4
        ⤷ eq_flip
        ⤷ eq_trans
        ⤷ replace

        (X + Y = Y + X)[X / 0][Y / 1]; peano3[X / 1] | eq_trans | eq_flip
        (X + Y = Y + X)[X / x][Y / 1]
        𝗦(a); a; x + 1; 1 + x | replace.MP;
        (
            peano4[X / 1][Y / x] | eq_flip;
            (X + Y = Y + X)[X / 1][Y / 𝗦(x)]
             | eq_trans)
         | eq_trans
        b ≔ 𝗦(a); a; 𝗦(x); x + 1 | replace
        b_cut ≔ b; a; ↘↘ | ✂
        ∀x(b_cutⅰ; a; c | ⪮[a / b_cutⅱ][c / 𝗦(x) + 1].MP.MP)

        goal; x | ↺.MP.MP[x].MP
        ⊦ goal
    }
    a ≔ {
        goal ≔ 𝗦(y) * x = (y * x) + x

        ⤷ peano5
        ⤷ peano6
        ⤷ eq_flip
        ⤷ eq_trans
        ⤷ replace

        peano5[X / y]

        peano5[X / 𝗦(y)];
        ((x + 0 = x)[x / y * 0]; y * 0 = 0 | eq_trans | eq_flip)
         | eq_trans

        b ≔ peano6[X / y][Y / x]
        c ≔
        a + 𝗦(x); a; b↙; b↘ | replace.MP;
        (((y * x) + y) + a; a; 𝗦(x); x + 1 | replace.MP) | eq_trans
        d ≔ (
            c;
            ((X + Y) + Z = X + (Y + Z))
            [X / c↘↙↙][Y / c↘↙↘][Z / c↘↘]
        ) | eq_trans

        x + y = y + x | eq_flip
        f ≔ (
            ((X + Y) + Z =
                X + (Y + Z))[X / y][Y / x][Z / 1] | eq_flip;
            (a + 1; a; y + x; x + y | replace.MP) | eq_trans;
            ((x + y) + z = x + (y + z))[z / 1]
        ) | eq_trans
        g ≔ (
            (y * x) + a; a; f↙; f↘ | replace.MP;
            (((X + Y) + Z = X + (Y + Z))
                [X / y * x][Y / x][Z / y + 1] | eq_flip)
        ) | eq_trans
        (𝗦(x) = x + 1)[x / y].eq_flip
        m ≔ (
            d;
            (g;
                (((y * x) + x) + a; a; y + 1; 𝗦(y) |
                    replace.MP)
            ) | eq_trans
        ) | eq_trans | eq_flip
        h ≔ a + 𝗦(y); a; 𝗦(y) * x; (y * x) + x | replace
        j ≔ peano6[X / 𝗦(y)][Y / x] | eq_flip
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
    peano6[X / x][Y / y] | eq_flip
    n ≔ u + x; u; x * y; y * x | replace
    n2 ≔ n↙ ⇒ u = n↘↘; u; v | ⪮[u / n↘↙][v / x * 𝗦(y)].MP.MP
    ∀x(n2↙ ⇒ n2↘↙ = u; u; v | ⪮[u / n2↘↘][v / 𝗦(y) * x].MP.MP)

    goal; y | ↺.MP.MP[y].MP

    ⊦ goal
    goal[x / X][y / Y]
    goal
}

replace_cut ≔ λ{
    /*
    Arguments: cut result; new value

    Assumes that the original phrase which got cut is proven.
    Replaces new value in the cut.

    Result: old value = new value ⇒ new phrase
     */
    ↵ ●ⅰ; ●ⅲ; _new_var | ⪮[●ⅲ / ●ⅱ][_new_var / ●ⅳ] | commute_ante.MP
}

add_equals ≔ λ{
    /*
    Arguments: a = b; c = d
    Result: a + c = b + d
     */
    ↵ ●ⅰ↙ + Y; Y; ●ⅱ↙; ●ⅱ↘ | replace.MP; X; ↘↙ | ✂; ●ⅰ↘ | replace_cut.MP
}

add_XY_ZW_eq_XZ_YW ≔ {
    goal ≔ (X + Y) + (Z + W) = (X + Z) + (Y + W)

    ⤷ add_assoc
    ⤷ add_comm
    ⤷ eq_flip
    ⤷ replace_cut

    add_assoc[X / x][Y / y][Z / z + w]; u; ↘↘ | ✂;
    (y + z) + w | replace_cut.MP; u; ↘↘↙ | ✂;
    z + y | replace_cut.MP; u; ↘↘ | ✂;
    z + (y + w) | replace_cut.MP; u; ↘ | ✂;
    (x + z) + (y + w) | replace_cut.MP[x / X][y / Y][z / Z][w / W]

    ⊦ goal
    goal
}

mul_add_distr ≔ {
    goal ≔ (x + y) * z = (x * z) + (y * z)

    ⤷ peano3
    ⤷ peano5
    ⤷ peano6
    ⤷ add_equals
    ⤷ eq_flip
    ⤷ eq_trans
    ⤷ replace
    ⤷ replace_cut
    ⤷ add_XY_ZW_eq_XZ_YW

    peano3[X / 0].eq_flip;
    (a + 0; a; 0; x * 0 | replace.MP) | eq_trans;
    (x * 0 + a; a; 0; y * 0 | replace.MP) | eq_trans | eq_flip;
    peano5[X / x + y].eq_flip | eq_trans | eq_flip

    peano6[X / x + y][Y / z].eq_flip
    a ≔ u + (x + y); u; (x + y) * z; (x * z) + (y * z) | replace
    b ≔ a; u; ↘↙ | ✂; (x + y) * 𝗦(z) | replace_cut.MP

    peano6[X / x][Y / z];
    peano6[X / y][Y / z] | add_equals;
    add_XY_ZW_eq_XZ_YW[X / x * z][Y / x][Z / y * z][W / y] | eq_trans | eq_flip

    ∀z(b; u; ↘↘ | ✂; (x * 𝗦(z)) + (y * 𝗦(z)) | replace_cut.MP)

    goal; z | ↺.MP.MP[z].MP
    ⊦ goal

    z * (x + y) = (x + y) * z; goal | eq_trans; u; ↘↙ | ✂;
    z * x | replace_cut.MP; u; ↘↘ | ✂;
    z * y | replace_cut.MP[x / X][y / Y][z / Z]
    ⊦ Z * (X + Y) = Z * X + Z * Y

    goal[x / X][y / Y][z / Z]
}

mul_assoc ≔ {
    goal ≔ (x * y) * z = x * (y * z)

    ⤷ eq_flip
    ⤷ eq_trans
    ⤷ replace
    ⤷ replace_cut

    (x * y) * 0 = 0;
    0 = x * 0 | eq_trans;
    (x * a; a; 0; y * 0 | replace.MP) | eq_trans

    x * a; a; y * 𝗦(z); y * z + y | replace.MP; u; ↘ | ✂;
    x * (y * z) + x * y | replace_cut.MP | eq_flip
    a + x * y; a; (x * y) * z; x * (y * z) | replace; u; ↘↙ | ✂;
    (x * y) * 𝗦(z) | replace_cut.MP; u; ↘↘ | ✂;
    x * (y * 𝗦(z)) | replace_cut.MP

    goal; z | ↺.MP.MP[z].MP
    ⊦ goal
    goal.eq_flip[x / X][y / Y][z / Z]
    goal[x / X][y / Y][z / Z]
}

exists_by_example ≔ {
    ⤷ recontrapose

    λ{
        /*
        Arguments: phrase, variable, example_value
        Assumes: phrase[variable / example_value]is proven
        Returns:¬∀variable¬phrase
         */
        phrase ≔ ●ⅰ
        var ≔ ●ⅱ
        example ≔ ●ⅲ
        proof ≔ phrase[var / example]
        ('X ⇒ ¬¬'X)['X / proof].MP
        u ≔ (∀var¬phrase)[example]
        ↵ recontrapose['A / u↙]['B / u↘].MP.MP
    }
}

is_odd ≔ λ{↵ ∀y¬● = y + y}
is_even ≔ λ{↵ ¬●.is_odd}

0 = y + y; y; 0 | exists_by_example
⊦ 0.is_even
2 = y + y; y; 1 | exists_by_example
⊦ 2.is_even

{
    ⤷ eq_flip
    ⤷ eq_trans
    ⤷ replace_cut

    goal ≔ 1 * x = x
    1 * x = x * 1;
    x * 1 = x * 0 + x | eq_trans; u; ↘↙ | ✂;
    0 | replace_cut.MP;
    0 + x = x | eq_trans
    ⊦ goal
    goal[x / X]
    goal.eq_flip[x / X]
}

{
    goal ≔ x * 1 = x
    ⤷ eq_flip
    ⤷ eq_trans
    x * 1 = 1 * x;
    1 * x = x | eq_trans
    ⊦ goal
    goal[x / X]
    goal.eq_flip[x / X]
}

{
    ⤷ eq_flip
    ⤷ eq_trans
    ⤷ replace
    ⤷ replace_cut
    goal ≔ 2 * x = x + x

    a * x; a; 2; 1 + 1 | replace.MP;
    (1 + 1) * x = 1 * x + 1 * x | eq_trans; u; ↘↙ | ✂;
    x | replace_cut.MP; u; ↘↘ | ✂;
    x | replace_cut.MP
    ⊦ goal
    goal[x / X]
    goal.eq_flip[x / X]
}

2 * x = y + y; y; x | exists_by_example
⊦ 2 * x | is_even

{
    ⤷ exists_by_example
    X = X + Z; Z; 0 | exists_by_example
    ⊦ ¬X < X

    X = 0 + Z; Z; X | exists_by_example
    ⊦ ¬X < 0
}

{
    goal ≔ x < y ⇒ x < 𝗦y

    ⤷ contrapose
    ⤷ deduce
    ⤷ eq_flip
    ⤷ eq_trans
    ⤷ exists_by_example
    ⤷ flip_postneg
    ⤷ recontra
    ⤷ replace_cut

    1 + X = X + 1; X + 1 = 𝗦(X) | eq_trans | eq_flip

    a ≔ x = u + Z; u; v | ⪮[u / 𝗦(y)][v / y + 1].MP; u; ↘↘ | ✂;
    y + (1 + Z) | replace_cut.MP; u; ↘↘↘ | ✂;
    𝗦(Z) | replace_cut.MP;
    ((∀Z(¬x = y + Z))[𝗦(z)] | flip_postneg.MP) | deduce | flip_postneg.MP

    b ≔ (∀Z a) ⇆.MP
    b↙↘.∀Z; b | deduce | recontra.MP

    contrapose['B / goal↙]['A / goal↘].MP

    ⊦ goal
    goal[x / X][y / Y]
}

{
    goal ≔ 0 < 𝗦x

    ⤷ peano1
    ⤷ eq_trans
    ⤷ eq_flip
    ⤷ ignore

    ∀Z(¬0 = u; u; v | ⪮[u = v / 𝗦Z = 1 + Z].MP.MP)
    a ≔ 𝗦u + Z = 𝗦(u + Z)⁇[u / 𝗦x].eq_flip
    b ≔ ∀Z(¬0 = u; u; v | ⪮[u = v / a].MP.MP)
    step ≔ goal; x | ↺.MP
    ∀x(ignore['A / b]['B / step↙↘↙].MP)
    step.MP[x].MP
    ⊦ goal
}

{
    ⤷ peano1
    ⤷ peano2
    ⤷ peano4
    ⤷ is_odd
    ⤷ neq_flip
    ⤷ equals_transitive
    ⤷ commute_ante
    ⤷ deduce
    ⤷ recontra
    ⤷ chain
    ⤷ ignore

    goal ≔ 1.is_odd

    peano1[X / 0].neq_flip
    ¬1 = x; x; y | ⪮[x / 0][y / 0 + 0].MP.MP
    peano4[X / 𝗦y][Y / y]

    a ≔ equals_transitive[X / 1][Y / 𝗦y + 𝗦y][Z / 𝗦(𝗦y + y)].commute_ante.MP;
    peano2[X / 0][Y / 𝗦y + y] | deduce

    b ≔ equals_transitive[X / a↘↙][Y / a↘↘][Z / (𝗦x + y = 𝗦(x + y))[x / y]↘].commute_ante.MP

    peano1[X / y + y]
    ∀y ignore['A / chain['X / a↙]['Y / a↘]['Z / b↘].MP.MP.recontra.MP.MP]['B / ¬1 = y + y].MP

    goal↘; y | ↺.MP.MP

    ⊦ goal
}

⊦ 1.is_odd

{
    ⤷ peano1
    ⤷ peano2
    ⤷ recontra

    goal ≔ ¬x = 𝗦x
    ∀x peano2[X / x][Y / 𝗦x].recontra.MP
    goal; x | ↺.MP.MP[x].MP
    ⊦ goal
}

⊦ ¬x = 𝗦x
