ignore ≔ 'A ⇒ 'B ⇒ 'A
⊦ ignore
⤶ ignore
distr ≔ ('A ⇒ 'B ⇒ 'C) ⇒ ('A ⇒ 'B) ⇒ 'A ⇒ 'C
⊦ distr
⤶ distr
contrapose ≔ (¬'A ⇒ ¬'B) ⇒ 'B ⇒ 'A
⊦ contrapose
⤶ contrapose
{
    goal ≔ 'x ⇒ 'x

    ignore['A / 'x]['B / 'x ⇒ 'x]
    ignore['A / 'x]['B / 'x]
    distr['A / 'x]['B / 'x ⇒ 'x]['C / 'x].MP.MP

    ⊦ goal
    goal['x / 'X]
}

1 ≔ 𝗦0
2 ≔ 𝗦1
3 ≔ 𝗦2
4 ≔ 𝗦3

commute_antecedents ≔ {
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
⤶ commute_antecedents
⊦ ('X ⇒ 'Y ⇒ 'Z) ⇒ 'Y ⇒ 'X ⇒ 'Z

commute_ante ≔ λ{
    /*
    Argument: A ⇒ B ⇒ c

    Swaps A ∧ B, assumes the argument is proven.

    Result: B ⇒ A ⇒ C
     */
    ↵ commute_antecedents['X / ●↙]['Y / ●↘↙]['Z / ●↘↘].MP
}
⤶ commute_ante

chain ≔ {
    goal ≔ ('x ⇒ 'y) ⇒ ('y ⇒ 'z) ⇒ 'x ⇒ 'z

    ignore['A / 'y ⇒ 'z]['B / 'x]
    ignore['A / distr['A / 'x]['B / 'y]['C / 'z]]['B / 'y ⇒ 'z].MP
    distr['A / 'y ⇒ 'z]['B / 'x ⇒ ('y ⇒ 'z)]['C / ('x ⇒ 'y) ⇒ ('x ⇒ 'z)].MP.MP | commute_ante

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⊦ chain
⤶ chain
⊦ ('X ⇒ 'Y) ⇒ ('Y ⇒ 'Z) ⇒ 'X ⇒ 'Z

chain' ≔ chain['X / 'x]['Y / 'y]['Z / 'z].commute_ante['x / 'X]['y / 'Y]['z / 'Z]
⤶ chain'

deduce ≔ λ{
    /*
    Argument: P ⇒ Q; Q ⇒ R
    Assumption: both implications are proven
    Returns: P ⇒ R
     */
    ↵ chain['X / ●ⅰ↙]['Y / ●ⅰ↘]['Z / ●ⅱ↘].MP.MP
}
⤶ deduce

prededuce ≔ λ{
    /*
    Argument: Q ⇒ R; P ⇒ Q
    Assumption: both implications are proven
    Returns: P ⇒ R

    This is the unnatural order of deduction, when one has an
    implication ∧ wants to exchange the antecedent in it by
    chaining something in front of it.

    This can be useful for cases when one has a long chain of
    operations ∧ needs to change something in the antecedent
    but one doesn't want to break to flow of the operation chain.
     */
    ↵ ●ⅱ; ●ⅰ | deduce
}
⤶ prededuce

rename_quantify ≔ λ{
    /*
    Argument:∀var1 P; var2
    Assumption: var2 is not free in∀var1 P
    Returns:(∀var1 P) ⇒ (∀var2 P)
     */
    ↵ ●ⅰ.∀●ⅱ; (∀●ⅱ●ⅰ[●ⅱ] ⇆).MP | deduce
}
⤶ rename_quantify

false_implies_anything ≔ {
    goal ≔ ¬'B ⇒ 'B ⇒ 'A

    ignore['A / 'X]['B / 'Y]['X / ¬'B]['Y / ¬'A];
    contrapose | deduce

    ⊦ goal
    goal.commute_ante
    goal
}
⤶ false_implies_anything

from_false ≔ λ{
    /*
    Argument: P ⇒ Q
    Assumption:¬P is proven
    Result: P ⇒ Q now proven
     */
    ↵ false_implies_anything['B / ●↙]['A / ●↘].MP
}
⤶ from_false

{
    goal ≔ ¬¬'x ⇒ 'x

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

    (¬¬'X ⇒ 'X)['X / ¬'x]
    contrapose['A / ¬¬'x]['B / 'x].MP
    ⊦ goal
    goal['x / 'X]
}

recontrapose ≔ {
    goal ≔ ('x ⇒ 'y) ⇒ ¬'y ⇒ ¬'x

    s ≔ chain['X / ¬¬'x]['Y / 'x]['Z / 'y].MP
    ('X ⇒ ¬¬'X)['X / 'y]
    q ≔ chain['X / ¬¬'x]['Y / 'y]['Z / ¬¬'y] | commute_ante.MP

    s; q | deduce;
    contrapose['A / ¬'x]['B / ¬'y] | deduce

    ⊦ goal
    goal['x / 'A]['y / 'B]
}
⤶ recontrapose

contra ≔ λ{
    /*
    Argument:¬P ⇒ ¬Q
    Returns:(¬P ⇒ ¬Q) ⇒ (Q ⇒ P)
     */
    ↵ contrapose['A / ●↙↓]['B / ●↘↓]
}
⤶ contra

recontra ≔ λ{
    /*
    Argument: P ⇒ Q
    Returns:(P ⇒ Q) ⇒ (¬Q ⇒ ¬P)
     */
    ↵ recontrapose['A / ●↙]['B / ●↘]
}
⤶ recontra

{
    goal ≔ 'x ∨ 'x ⇒ 'x
    a ≔ distr['A / ¬'B]['C / 'A].MP['B / 'x]['A / ¬'A];
    contrapose['A / 'x]['B / 'A] | deduce
    ('x ⇒ 'x)['x / a↙]
    distr['B / a↘↙]['C / a↘↘]['A / a↙].MP.MP
    ⊦ goal
}

preneg_flip ≔ {
    goal ≔ (¬'x ⇒ 'y) ⇒ (¬'y ⇒ 'x)

    chain['X / ¬'x]['Y / 'y]['Z / ¬¬'y] | commute_ante.MP;
    contrapose['A / 'x]['B / ¬'y] | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ preneg_flip
flip_preneg ≔ λ{
    /*
    Argument:¬P ⇒ Q
    Returns:(¬P ⇒ Q) ⇒ (¬Q ⇒ P)
     */
    ↵ preneg_flip['X / ●↙↓]['Y / ●↘]
}
⤶ flip_preneg
postneg_flip ≔ {
    goal ≔ ('x ⇒ ¬'y) ⇒ 'y ⇒ ¬'x

    recontrapose['A / 'x]['B / ¬'y];
    chain['X / 'y]['Y / ¬¬'y]['Z / ¬'x].MP | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ postneg_flip
flip_postneg ≔ λ{
    /*
    Argument: P ⇒ ¬Q
    Returns:(P ⇒ ¬Q) ⇒ (Q ⇒ ¬P)
     */
    ↵ postneg_flip['X / ●↙]['Y / ●↘↓]
}
⤶ flip_postneg

y_impl_or ≔ {
    goal ≔ 'y ⇒ 'x ∨ 'y

    ignore['A / 'y]['B / ¬'x]

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ y_impl_or

x_impl_or ≔ {
    goal ≔ 'x ⇒ 'x ∨ 'y
    goal⁇

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ x_impl_or

and_impl_x ≔ {
    goal ≔ 'x ∧ 'y ⇒ 'x

    false_implies_anything['A / ¬'y]['B / 'x] | recontra.MP;
    ¬¬'x ⇒ 'x | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ and_impl_x

and_impl_y ≔ {
    goal ≔ 'x ∧ 'y ⇒ 'y

    ignore['A / ¬'y]['B / 'x] | recontra.MP;
    ¬¬'y ⇒ 'y | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ and_impl_y

x_impl_y_impl_and ≔ {
    goal ≔ 'x ⇒ 'y ⇒ 'x ∧ 'y

    a ≔ ('X ⇒ 'X)['X / 'x ⇒ ¬'y] | commute_ante
    b ≔ ('x ⇒ ¬'y) ⇒ ¬'y | flip_postneg
    a; b | deduce

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ x_impl_y_impl_and

xyz_impl_and ≔ {
    goal ≔ ('x ⇒ 'y ⇒ 'z) ⇒ 'x ∧ 'y ⇒ 'z

    b ≔ 'x ∧ 'y

    ignore['A / goal↙]['B / b];
    distr['A / b]['B / 'x]['C / 'y ⇒ 'z] | deduce | commute_ante.MP;
    distr['A / b]['B / 'y]['C / 'z] | deduce | commute_ante.MP

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⤶ xyz_impl_and

and_impl_xyz ≔ {
    goal ≔ ('x ∧ 'y ⇒ 'z) ⇒ 'x ⇒ 'y ⇒ 'z

    chain['X / 'x]['Y ⇒ 'Z / chain['X / 'y]['Y / 'x ∧ 'y]['Z / 'z]].MP.MP.commute_ante

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⤶ and_impl_xyz

and_comm ≔ {
    goal ≔ 'x ∧ 'y ⇒ 'y ∧ 'x

    recontrapose['A / 'y ⇒ ¬'x]['B / 'x ⇒ ¬'y].MP

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ and_comm

and_assoc ≔ {
    goal ≔ ('x ∧ 'y)∧ 'z ⇒ 'x ∧('y ∧ 'z)

    chain['X / 'x]['Y ⇒ 'Z / (¬¬'X ⇒ 'X)['X / 'y ⇒ ¬'z]].commute_ante.MP;
    xyz_impl_and['X / 'x]['Y / 'y]['Z / ¬'z] | deduce | recontra.MP

    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⤶ and_assoc

demorgan_or ≔ {
    goal ≔ 'x ∨ 'y ⇒ ¬(¬'x ∧¬'y)

    a ≔ chain'['X / ¬'x]['Y ⇒ 'Z / 'y ⇒ ¬¬'y].MP
    chain'['X ⇒ 'Y / a]['X ⇒ 'Z / goal].MP.MP

    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ demorgan_or

reduce ≔ λ{
    /*
    Arguments: P ⇒ Q; Q'
    Assumptions: P ⇒ Q is a proven theorem ∧ Q' has the shape of Q
    Result: P[Q / Q'] ⇒ Q', the backwards application of the theorem to Q'
     */
    ↵ ●ⅰ[●ⅰ↘ / ●ⅱ]
}
⤶ reduce

apply ≔ λ{
    /*
    Arguments: P'; P ⇒ Q
    Assumptions: P ⇒ Q is a proven theorem ∧ P' has the shape of P
    Result: P' ⇒ Q[P / P'], the application of the theorem to P'
     */
    ↵ ●ⅱ[●ⅱ↙ / ●ⅰ]
}
⤶ apply

apply2 ≔ λ{
    /*
    Arguments: P'; Q'; P ⇒ Q ⇒ R
    Assumptions: P' has the shape of P, ∧ Q' has the shape of Q
    Result: P' ⇒ Q' ⇒ R[P / P'][Q / Q']
     */
    ↵ ●ⅲ[●ⅲⅰ / ●ⅰ][●ⅲⅱ / ●ⅱ]
}
⤶ apply2

demorgan_and ≔ {
    goal ≔ 'x ∧ 'y ⇒ ¬(¬'x ∨¬'y)

    a ≔ recontrapose; goal | reduce
    chain; a↙ | reduce.MP
    a.MP

    ⊦ goal
    goal
}
⤶ demorgan_and

or_comm ≔ {
    goal ≔ 'x ∨ 'y ⇒ 'y ∨ 'x
    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⊦ 'X ∨ 'Y ⇒ 'Y ∨ 'X
⤶ or_comm

or_comm_iff ≔ {
    goal ≔ 'x ∨ 'y ⇔ 'y ∨ 'x
    or_comm['X / 'x]['Y / 'y];
    or_comm['X / 'y]['Y / 'x];
    x_impl_y_impl_and | apply2.MP.MP
    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ or_comm_iff

conditional_and ≔ {
    goal ≔ ('x ⇒ 'y) ⇒ ('x ⇒ 'z) ⇒ ('x ⇒ 'y ∧ 'z)
    a ≔ x_impl_y_impl_and['X / 'y]['Y / 'z]
    b ≔ ignore['A / a]['B / 'x].MP; distr | apply.MP
    c ≔ b↘; distr | apply
    b; c | deduce
    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⤶ conditional_and

quadchain ≔ {
    goal ≔ ('x ⇒ 'y) ⇒ ('y ⇒ 'z) ⇒ ('z ⇒ 'w) ⇒ ('x ⇒ 'w)
    a ≔ chain['X / 'x]['Y / 'z]['Z / 'w]
    b ≔ chain['X / 'x]['Y / 'y]['Z / 'z]; xyz_impl_and | apply.MP
    b; a | deduce; and_impl_xyz | apply.MP
    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]['w / 'W]
}
⤶ quadchain

or_impl_distr ≔ {
    goal ≔ ('x ⇒ 'y) ⇒ ('z ⇒ 'w) ⇒ ('x ∨ 'z ⇒ 'y ∨ 'w)
    a ≔ quadchain['X / ¬'y]['Y / ¬'x]['Z / 'z]['W / 'w]
    b ≔ recontrapose['A / 'x]['B / 'y]
    c ≔ b; a | deduce
    c; (c↘; commute_antecedents | apply) | deduce
    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]['w / 'W]
}
⊦ ('X ⇒ 'Y) ⇒ ('Z ⇒ 'W) ⇒ ('X ∨ 'Z ⇒ 'Y ∨ 'W)
⤶ or_impl_distr

conditional_or ≔ {
    goal ≔ ('x ⇒ 'z) ⇒ ('y ⇒ 'z) ⇒ 'x ∨ 'y ⇒ 'z
    or_impl_distr['X / 'x]['Y / 'z]['Z / 'y]['W / 'z];
    xyz_impl_and | apply.MP;
    xyz_impl_and | apply.MP;
    'z ∨ 'z ⇒ 'z | deduce;
    and_impl_xyz | apply.MP;
    and_impl_xyz | apply.MP
    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⊦ ('X ⇒ 'Z) ⇒ ('Y ⇒ 'Z) ⇒ 'X ∨ 'Y ⇒ 'Z
⤶ conditional_or

iff_then_xy ≔ {
    goal ≔ 'X ⇔ 'Y ⇒ 'X ⇒ 'Y
    ⊦ goal
    goal
}
⤶ iff_then_xy

iff_then_yx ≔ {
    goal ≔ 'X ⇔ 'Y ⇒ 'Y ⇒ 'X
    ⊦ goal
    goal
}
⤶ iff_then_yx

iff ≔ {
    goal ≔ ('X ⇒ 'Y) ⇒ ('Y ⇒ 'X) ⇒ ('X ⇔ 'Y)
    ⊦ goal
    goal
}
⤶ iff

iff_comm ≔ {
    goal ≔ 'X ⇔ 'Y ⇒ 'Y ⇔ 'X
    ⊦ goal
    goal
}
⤶ iff_comm

iff_neg ≔ λ{
    /*
    Argument: P ⇔ Q
    Returns: P ⇔ Q ⇒ ¬P ⇔ ¬Q
     */
    P ≔ ●↓↙↙
    Q ≔ ●↓↙↘
    goal ≔ P ⇔ Q ⇒ ¬P ⇔ ¬Q

    x ≔ '_new_var1
    y ≔ '_new_var2

    iff_then_xy['X / x]['Y / y]; recontrapose['A / x]['B / y] | deduce;
    (iff_then_yx['X / x]['Y / y]; recontrapose['A / y]['B / x] | deduce);
    conditional_and | apply2.MP.MP;
    iff_comm['X / ¬y]['Y / ¬x] | deduce[x / P][y / Q]
    ⊦ goal
    ↵ goal
}
⊦ 'A ⇔ 'B | iff_neg
⤶ iff_neg

iff_ante ≔ λ{
    /*
    Argument: P ⇔ Q; Z
    Returns: P ⇔ Q ⇒ (P ⇒ Z) ⇔ (Q ⇒ Z)
     */
    P ≔ ●ⅰ↓↙↙
    Q ≔ ●ⅰ↓↙↘
    Z ≔ ●ⅱ
    goal ≔ P ⇔ Q ⇒ (P ⇒ Z) ⇔ (Q ⇒ Z)

    x ≔ '_new_var1
    y ≔ '_new_var2
    z ≔ '_new_var3

    iff_then_xy['X / x]['Y / y]; chain['X / x]['Y / y]['Z / z] | deduce;
    (iff_then_yx['X / x]['Y / y]; chain['X / y]['Y / x]['Z / z] | deduce);
    conditional_and | apply2.MP.MP;
    iff_comm['X / y ⇒ z]['Y / x ⇒ z] | deduce[x / P][y / Q][z / Z]

    ⊦ goal
    ↵ goal
}
⊦ 'A ⇔ 'B; 'C | iff_ante
⤶ iff_ante

iff_conseq ≔ λ{
    /*
    Argument: P ⇔ Q; A
    Returns: P ⇔ Q ⇒ (A ⇒ P) ⇔ (A ⇒ Q)
     */
    P ≔ ●ⅰ↓↙↙
    Q ≔ ●ⅰ↓↙↘
    A ≔ ●ⅱ
    goal ≔ P ⇔ Q ⇒ (A ⇒ P) ⇔ (A ⇒ Q)

    x ≔ '_new_var1
    y ≔ '_new_var2
    z ≔ '_new_var3

    iff_then_xy['X / x]['Y / y]; chain'['X / z]['Y / x]['Z / y] | deduce;
    (iff_then_yx['X / x]['Y / y]; chain'['X / z]['Y / y]['Z / x] | deduce);
    conditional_and | apply2.MP.MP[x / P][y / Q][z / A]

    ⊦ goal
    ↵ goal
}
⊦ 'A ⇔ 'B; 'C | iff_conseq
⤶ iff_conseq

iff_forall ≔ λ{
    /*
    Argument: P ⇔ Q; var
    Returns: P ⇔ Q ⇒ (∀var P) ⇔ (∀var Q)
     */
    P ≔ ●ⅰ↓↙↙
    Q ≔ ●ⅰ↓↙↘
    var ≔ ●ⅱ
    goal ≔ P ⇔ Q ⇒ (∀var P) ⇔ (∀var Q)

    iff_then_xy['X / P]['Y / Q]; (P ⇒ Q).∀var | deduce; (∀var(P ⇒ Q) ⇆) | deduce;
    (iff_then_yx['X / P]['Y / Q]; (Q ⇒ P).∀var | deduce; (∀var(Q ⇒ P) ⇆) | deduce);
    conditional_and | apply2.MP.MP
    ⊦ goal
    ↵ goal
}
⊦ 'a ⇔ 'b; u | iff_forall
⤶ iff_forall

{
    goal ≔ 'x ⇔ 'x
    x_impl_y_impl_and['X / 'x ⇒ 'x]['Y / 'x ⇒ 'x].MP.MP
    ⊦ goal
    goal['x / 'X]
}
⊦ 'X ⇔ 'X

{
    goal ≔ 'x ⇔ ¬¬'x
    x_impl_y_impl_and['X / 'x ⇒ ¬¬'x]['Y / ¬¬'x ⇒ 'x].MP.MP
    ⊦ goal
    goal['x / 'X]
}
⊦ 'X ⇔ ¬¬'X

{
    goal ≔ ¬¬'x ⇔ 'x
    iff_comm; goal | reduce.MP
    ⊦ goal
    goal['x / 'X]
}
⊦ ¬¬'X ⇔ 'X

demorgan_or' ≔ {
    goal ≔ ¬(¬'x ∧¬'y) ⇒ 'x ∨ 'y
    (¬¬'y ⇔ 'y); ¬'x | iff_conseq.MP; iff_then_xy | apply.MP
    (¬¬'X ⇒ 'X)['X / ¬'x ⇒ ¬¬'y]; (¬'x ⇒ ¬¬'y) ⇒ (¬'x ⇒ 'y) | deduce
    ⊦ goal
    goal['x / 'X]['y / 'Y]
}
⤶ demorgan_or'

or_assoc ≔ {
    goal ≔ 'x ∨('y ∨ 'z) ⇒ ('x ∨ 'y)∨ 'z
    a ≔ and_assoc['X / ¬'x]['Y / ¬'y]['Z / ¬'z]; contrapose | apply.MP
    b ≔ 'x ⇒ 'x; demorgan_or['X / 'y]['Y / 'z]; or_impl_distr | apply2.MP.MP
    c ≔ b; a | deduce
    d ≔ ¬¬'z ⇔ 'z; ¬(¬'x ⇒ ¬¬'y) | iff_conseq.MP; iff_then_xy | apply.MP
    e ≔ c; d | deduce
    f ≔ ¬¬'y ⇔ 'y; ¬'x | iff_conseq.MP | iff_neg.MP; 'z | iff_ante.MP; iff_then_xy | apply.MP
    e; f | deduce
    ⊦ goal
    goal['x / 'X]['y / 'Y]['z / 'Z]
}
⊦ 'X ∨('Y ∨ 'Z) ⇒ ('X ∨ 'Y)∨ 'Z
⤶ or_assoc

or_permute ≔ {
    or_comm['X / 'x ∨ 'y]['Y / 'z];
    or_assoc['X / 'z]['Y / 'x]['Z / 'y] | deduce['x / 'X]['y / 'Y]['z / 'Z]
}
⤶ or_permute

conditional_or' ≔ {
    goal ≔ ('a ⇒ 'x)∨('a ⇒ 'y) ⇒ 'a ⇒ 'x ∨ 'y
    'a ⇔ ¬¬'a; 'x | iff_ante.MP; and_impl_x | apply.MP
    a ≔ ('a ⇒ 'x) ⇒ ¬'a ∨ 'x;
    ('a ⇒ 'y) ⇒ ¬'a ∨ 'y;
    or_impl_distr | apply2.MP.MP
    b ≔ a↘; or_permute | apply
    c ≔ a; b | deduce
    d ≔ c; c↘.flip_preneg | deduce
    e ≔ d; ((¬(¬¬'a ⇒ 'y) ⇒ ¬'a).contra; chain' | apply.MP['X / ¬'x]) | deduce
    f ≔ (¬¬'a ⇔ 'a); 'y | iff_ante.MP; 'a | iff_conseq.MP; iff_then_xy | apply.MP;
    distr['B / 'A]['C / 'B].commute_ante.MP['A / 'a]['B / 'y] | deduce;
    chain' | apply.MP['X / ¬'x]
    g ≔ e; f | deduce
    g; (g↘; commute_antecedents | apply) | deduce
    ⊦ goal
    goal['a / 'A]['x / 'X]['y / 'Y]
}
⊦ ('A ⇒ 'X)∨('A ⇒ 'Y) ⇒ 'A ⇒ 'X ∨ 'Y
⤶ conditional_or'

equals_symmetric ≔ {
    goal ≔ x = y ⇒ y = x

    (X = X)[X / x]
    x = z; x; y | ⪮[z / x] | commute_ante.MP
    ⊦ goal
    goal[x / X][y / Y]
}
⤶ equals_symmetric

eq_flip ≔ λ{
    /*
    Argument: a = b
    Returns: b = a
     */
    ↵ equals_symmetric[X / ●↙][Y / ●↘].MP
}
⤶ eq_flip

neq_flip ≔ λ{
    /*
    Argument:¬a = b
    Returns:¬b = a
     */
    ↵ equals_symmetric.recontra.MP[X / ●↓↘][Y / ●↓↙].MP
}
⤶ neq_flip

equals_transitive ≔ {
    goal ≔ x = y ⇒ y = z ⇒ x = z

    a ≔ y = z; y; x | ⪮
    chain['X / x = y]['Y ⇒ 'Z / a].MP.MP

    ⊦ goal
    goal[x / X][y / Y][z / Z]
}
⤶ equals_transitive

equals_transitive' ≔ equals_transitive.commute_ante
⤶ equals_transitive'

eq_trans ≔ λ{
    ↵ equals_transitive[X = Y / ●ⅰ][Y = Z / ●ⅱ].MP.MP
}
⤶ eq_trans

not_equals_symmetric ≔ {
    goal ≔ ¬x = y ⇒ ¬y = x

    equals_symmetric[X / y][Y / x]
    recontrapose['A / y = x]['B / x = y].MP

    ⊦ goal
    goal[x / X][y / Y]
}
⤶ not_equals_symmetric

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

⤶ peano1
⤶ peano2
⤶ peano3
⤶ peano4
⤶ peano5
⤶ peano6

{
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
⤶ replace

𝗦(x); x; X; Y | replace

add_comm ≔ {
    goal ≔ (x + y) = (y + x)

    a ≔ {
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
⤶ add_comm

add_assoc ≔ {
    goal ≔ (x + y) + z = x + (y + z)

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
⤶ add_assoc

mul_comm ≔ {
    goal ≔ x * y = y * x

    peano5[X / 0]
    peano6[X / 0][Y / x]; peano3[X / 0 * x] | eq_trans
    ∀x(0 * 𝗦(x) = a; a; b | ⪮[a / 0 * x][b / 0] | commute_ante.MP)
    0 * x = 0; x | ↺.MP.MP[x].MP

    peano5[X / x]
    x * 0 = 0; (0 * x = 0 | eq_flip) | eq_trans

    {
        goal ≔ 𝗦(x) = x + 1

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
⤶ mul_comm

replace_cut ≔ λ{
    /*
    Arguments: cut result; new value

    Assumes that the original phrase which got cut is proven.
    Replaces new value in the cut.

    Result: old value = new value ⇒ new phrase
     */
    ↵ ●ⅰ; ●ⅲ; _new_var | ⪮[●ⅲ / ●ⅱ][_new_var / ●ⅳ] | commute_ante.MP
}
⤶ replace_cut

add_equals ≔ λ{
    /*
    Arguments: a = b; c = d
    Result: a + c = b + d
     */
    ↵ ●ⅰ↙ + Y; Y; ●ⅱ↙; ●ⅱ↘ | replace.MP; X; ↘↙ | ✂; ●ⅰ↘ | replace_cut.MP
}
⤶ add_equals

add_XY_ZW_eq_XZ_YW ≔ {
    goal ≔ (X + Y) + (Z + W) = (X + Z) + (Y + W)

    add_assoc[X / x][Y / y][Z / z + w]; u; ↘↘ | ✂;
    (y + z) + w | replace_cut.MP; u; ↘↘↙ | ✂;
    z + y | replace_cut.MP; u; ↘↘ | ✂;
    z + (y + w) | replace_cut.MP; u; ↘ | ✂;
    (x + z) + (y + w) | replace_cut.MP[x / X][y / Y][z / Z][w / W]

    ⊦ goal
    goal
}
⤶ add_XY_ZW_eq_XZ_YW

mul_add_distr ≔ {
    goal ≔ (x + y) * z = (x * z) + (y * z)

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
⤶ mul_add_distr

mul_assoc ≔ {
    goal ≔ (x * y) * z = x * (y * z)

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
⤶ mul_assoc

mul_XY_ZW_eq_XZ_YW ≔ {
    goal ≔ (x * x') * (a * a') = (x * a) * (x' * a')
    (x * x') * (a * a') = x * (x' * (a * a'));
    (x * (x' * u); u; a * a'; a' * a | replace.MP) | eq_trans;
    (x * u; u; x' * (a' * a); (x' * a') * a | replace.MP) | eq_trans;
    (x * u; u; (x' * a') * a; a * (x' * a') | replace.MP) | eq_trans;
    x * (a * (x' * a')) = (x * a) * (x' * a') | eq_trans
    ⊦ goal
    goal[x / X][x' / Y][a / Z][a' / W]
}
⤶ mul_XY_ZW_eq_XZ_YW
⊦ (X * Y) * (Z * W) = (X * Z) * (Y * W)

exists_by_example ≔ λ{
    /*
    Arguments: phrase, example_value, variable(that is, a cut result)
    Assumes: phrase[variable / example_value]is proven
    Returns:∃variable phrase
     */
    phrase ≔ ●ⅰ
    var ≔ ●ⅲ
    example ≔ ●ⅱ
    proof ≔ phrase[var / example]
    ('X ⇒ ¬¬'X)['X / proof].MP
    u ≔ (∀var¬phrase)[example]
    ↵ recontrapose['A / u↙]['B / u↘].MP.MP
}
⤶ exists_by_example

conditional_exists_by_example ≔ λ{
    /*
    Argument: P ⇒ Q; example; var(that is, a cut result)
    Returns: P ⇒ ∃var Q

    Creates a conditional existential statement.A typical way to
    use this is by proving a statement of the shape of
    P ⇒ Q[var / example], then pass in P ⇒ R; example; var to get
    P ⇒ ∃var Q.Typically var is present in both P ∧ Q ∧
    example is an appropriate expression depending on var, satisfying
    Q based on P.
     */

    phrase ≔ ●ⅰ
    P ≔ phrase↙
    Q ≔ phrase↘
    example ≔ ●ⅱ
    var ≔ ●ⅲ

    Q' ≔ Q[var / example]
    phrase' ≔ P ⇒ Q'

    u ≔ (∀var¬Q)[example]; recontrapose | apply.MP
    ↵ phrase'; Q' ⇒ ¬¬Q' | deduce; u | deduce
}
⤶ conditional_exists_by_example

exists_ante ≔ λ{
    /*
    Argument: P ⇒ Q; var
    Assumes: P ⇒ Q is proven, var is not free in Q
    Returns:(∃var P) ⇒ Q

    Introduces an exists quantifier on the antecedent of a proven
    implication.

    The idea is that if P implies Q, then it must imply it for some
    concrete value of the variable, it cannot be the it does not imply
    it for all values, because then it would simply not imply Q.
     */

    P ≔ ●ⅰ↙
    Q ≔ ●ⅰ↘
    var ≔ ●ⅱ

    u ≔ ∀var(●ⅰ; recontrapose | apply.MP) ⇆.MP
    v ≔ (¬Q).∀var
    w ≔ chain['X ⇒ 'Y / v]['Y ⇒ 'Z / u].MP.MP; recontrapose | apply.MP
    ↵ chain['X ⇒ 'Y / w]['Z / Q].MP.MP
}
⤶ exists_ante

is_odd ≔ λ{↵ ∀y¬● = y + y}
is_even ≔ λ{↵ ¬●.is_odd}
⤶ is_odd
⤶ is_even

0 = y + y; 0; y | exists_by_example
⊦ 0.is_even
2 = y + y; 1; y | exists_by_example
⊦ 2.is_even

{
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
    x * 1 = 1 * x;
    1 * x = x | eq_trans
    ⊦ goal
    goal[x / X]
    goal.eq_flip[x / X]
}

{
    goal ≔ 2 * x = x + x

    a * x; a; 2; 1 + 1 | replace.MP;
    (1 + 1) * x = 1 * x + 1 * x | eq_trans; u; ↘↙ | ✂;
    x | replace_cut.MP; u; ↘↘ | ✂;
    x | replace_cut.MP
    ⊦ goal
    goal[x / X]
    goal.eq_flip[x / X]
}

2 * x = y + y; x; y | exists_by_example
⊦ 2 * x | is_even

{
    X = X + Z; 0; Z | exists_by_example
    ⊦ ¬X < X
    ⊦ X ≤ X

    X = 0 + Z; X; Z | exists_by_example
    ⊦ ¬X < 0
    ⊦ 0 ≤ X

    ⊦ X < Y ⇒ ¬Y ≤ X
    ⊦ X ≤ Y ⇒ ¬Y < X
}

{
    goal ≔ x ≤ y ⇒ x ≤ 𝗦y

    step ≔ {
        goal ≔ y = x + z ⇒ 𝗦y = x + 𝗦z
        y = x + z ⇒ 𝗦y = 𝗦(x + z); u; ↘↘ | ✂; x + 𝗦z | replace_cut.MP
        ⊦ goal
        goal
    }

    h ≔ step; Z; ↘↘↘ | ✂ | conditional_exists_by_example
    /*
    h is now y = x + z ⇒ x ≤ 𝗦y
    by applying exists_ante, we turn the antecedent into x ≤ y.
     */
    h[z / Z]; Z | exists_ante

    ⊦ goal
}

{
    goal ≔ x0 ≤ y0 ⇒ x1 ≤ y1 ⇒ x0 + x1 ≤ y0 + y1
    step ≔ {
        goal ≔ y0 = x0 + a0 ⇒ x1 ≤ y1 ⇒ x0 + x1 ≤ y0 + y1
        step ≔ {
            goal ≔ y0 = x0 + a0 ⇒ y1 = x1 + a1 ⇒ y0 + y1 = (x0 + x1) + (a0 + a1)
            h ≔ y0 + u; u; y1; x1 + a1 | replace
            g ≔ h; u; ↘↘↙ | ✂; x0 + a0 | replace_cut
            k ≔ g; u; ↘↘↘ | ✂; (x0 + x1) + (a0 + a1) | replace_cut.MP
            ⊦ goal
            goal
        }
        step; xyz_impl_and | apply.MP;
        Z; ↘↘↘ | ✂.conditional_exists_by_example;
        and_impl_xyz | apply.MP | commute_ante[a1 / Z];
        Z | exists_ante.commute_ante
        ⊦ goal
        goal
    }
    step[a0 / Z]; Z | exists_ante
    ⊦ goal
    goal[x0 / X0][y0 / Y0][x1 / X1][y1 / Y1]
}
⊦ A = B + C ⇒ A' = B' + C' ⇒ A + A' = (B + B') + (C + C')
⊦ X ≤ Y ⇒ X' ≤ Y' ⇒ X + X' ≤ Y + Y'

{
    goal ≔ x ≤ x + a
    x + a = x + Z; a; Z | exists_by_example
    ⊦ goal
}

leq_trans ≔ {
    goal ≔ x ≤ y ⇒ y ≤ z ⇒ x ≤ z
    step ≔ {
        goal ≔ y = x + w ⇒ y ≤ z ⇒ x ≤ z
        h ≔ commute_antecedents; goal | reduce
        step ≔ {
            goal ≔ z = y + u ⇒ y = x + w ⇒ z = x + (w + u)
            h ≔ commute_antecedents; goal | reduce
            g ≔ z = a + u; a; b | ⪮[a = b / y = x + w]
            g; a; ↘↘↘ | ✂; x + (w + u) | replace_cut.MP
            h.MP
            ⊦ goal
            goal
        }
        g ≔ step; xyz_impl_and | apply.MP;
        Z; ↘↘↘ | ✂ | conditional_exists_by_example;
        and_impl_xyz | apply.MP
        g[u / Z]; Z | exists_ante
        h.MP
        ⊦ goal
        goal
    }

    g ≔ step[w / Z]; Z | exists_ante

    ⊦ goal
    goal
}

{
    goal ≔ x = x + y ⇒ y = 0

    0 = 0 + y ⇒ 0 + y = 0;
    equals_transitive[X = Y / y = 0 + y][Z / 0].MP | deduce

    h ≔ equals_transitive'[X / 𝗦x][Y / 𝗦x + y][Z / 𝗦(x + y)].MP;
    𝗦x = 𝗦(x + y) ⇒ x = x + y | deduce
    chain['X ⇒ 'Y / h]['Z / y = 0].MP

    goal; x | ↺.MP.MP[x].MP
    ⊦ goal
    goal[x / X][y / Y]
}

{
    goal ≔ x + y = 0 ⇒ y = 0

    X = Y ⇒ Y = X; 𝗦(x + y) = 𝗦x + y | reduce.MP
    g ≔ equals_transitive; 𝗦x + y = 0 ⇒ 𝗦(x + y) = 0 | reduce.MP
    ignore['A / ¬𝗦(x + y) = 0]['B / ¬y = 0].MP
    h ≔ contrapose; 𝗦(x + y) = 0 ⇒ y = 0 | reduce.MP
    g; h | deduce
    i ≔ goal; x | ↺.MP
    ∀x(ignore; i↙↘ | reduce.MP)
    i.MP[x].MP
    ⊦ goal
    goal[x / X][y / Y]
}

{
    goal ≔ x + y = 0 ⇒ x = 0
    equals_transitive; x + y = 0 ⇒ y + x = 0 | reduce.MP;
    y + x = 0 ⇒ x = 0 | deduce
    ⊦ goal
    goal
}

{
    goal ≔ x ≤ y ⇒ y ≤ x ⇒ x = y
    step ≔ {
        goal ≔ y = x + a ⇒ y ≤ x ⇒ x = y
        h ≔ commute_antecedents; goal | reduce
        step ≔ {
            goal ≔ x = y + b ⇒ y = x + a ⇒ x = y
            h ≔ y = u + a; u; v | ⪮[u = v / x = y + b]; xyz_impl_and | apply.MP
            g ≔ y = u; u; v | ⪮[u = v / (y + b) + a = y + (b + a)].MP
            j ≔ y = y + (b + a) ⇒ b + a = 0
            k ≔ h; g | deduce; j | deduce; b + a = 0 ⇒ b = 0 | deduce
            m ≔ k↙; and_impl_x | apply
            n1 ≔ (k ⇒ m ⇒ k↙ ⇒ (k↘∧ m↘))⁇.MP.MP
            n2 ≔ x = y + b; b; u | ⪮[u / 0]; u; ↘↘↘ | ✂; y | replace_cut.MP; xyz_impl_and | apply.MP
            n1; n2 | deduce; and_impl_xyz | apply.MP
            ⊦ goal
            goal
        }

        step[b / Z]; Z | exists_ante

        h.MP
        ⊦ goal
        goal
    }
    step[a / Z]; Z | exists_ante
    ⊦ goal
}

X ≤ W; W; Y | ⪮[W / X].commute_ante.MP
⊦ X = Y ⇒ X ≤ Y

{
    goal ≔ x < y ⇒ ¬x = y

    ('x ⇒ ¬¬'x)['x / Y < X];
    (X = Y ⇒ X ≤ Y).recontra.MP | deduce
    (x < y ⇒ ¬y = x); not_equals_symmetric[X / y][Y / x] | deduce

    ⊦ goal
}

{
    goal ≔ x ≤ y ⇒ x + x ≤ y + y

    a ≔ add_XY_ZW_eq_XZ_YW[X / x][Z / x][Y / Z][W / Z]
    X + X; X; y; x + Z | replace; X; ↘↘ | ✂; a↘ | replace_cut.MP; Z; ↘↘↘ | ✂.conditional_exists_by_example; Z | exists_ante

    ⊦ goal
}

leq_mul ≔ {
    goal ≔ x ≤ y ⇒ a * x ≤ a * y
    mul_add_distr[X / x][Y / z][Z / a];
    w; ↙ | ✂; a * (x + z) | replace_cut.MP;
    w; ↘↙ | ✂; a * x | replace_cut.MP;
    w; ↘↘ | ✂; a * z | replace_cut.MP;
    w; ↙↘ | ✂; y | replace_cut;
    y = x + z ⇒ x + z = y | prededuce;
    Z; ↘↘↘ | ✂.conditional_exists_by_example[z / Z];
    Z | exists_ante
    ⊦ goal
    goal[x / X][y / Y][a / A]
}
⊦ X ≤ Y ⇒ A * X ≤ A * Y

{
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
    goal ≔ ¬x = 𝗦x
    ∀x peano2[X / x][Y / 𝗦x].recontra.MP
    goal; x | ↺.MP.MP[x].MP
    ⊦ goal
}

⊦ ¬x = 𝗦x

{
    goal ≔ 𝗦X + 𝗦Y = 𝗦𝗦(X + Y)
    peano4[X / 𝗦X]; Z; ↘↓ | ✂; goal↘↓ | replace_cut.MP
    (x = y ⇒ y = x)[x / goal↙][y / goal↘].MP
    ⊦ goal
}

succ_is_not_leq ≔ {
    goal ≔ x ≤ y ⇒ ¬x = 𝗦y
    goal4 ≔ ¬y = 𝗦y + x
    peano4[X / x][Y / 0]
    peano1[X / x + 0]
    1 + x = x + 1 ⇅add_comm; y; ↘ | ✂; 𝗦(x + 0) | replace_cut.MP
    0 = x; x; y | ⪮[x / 1 + x][y / 𝗦(x + 0)].MP.recontra.MP.MP
    e ≔ add_comm[X / 𝗦𝗦y][Y / x];
    peano4[X / x][Y / 𝗦y] | eq_trans; z; ↘↓ | ✂; add_comm[X / x][Y / 𝗦y]↘ | replace_cut.MP.eq_flip
    ∀y(peano2[X / y][Y / 𝗦y + x].recontra.MP; z; ↘↓↘ | ✂; e↘ | replace_cut.MP)
    goal4; y | ↺.MP.MP[y].MP
    ⊦ goal4
    peano3[X / 𝗦y]
    (¬x = 𝗦x)[x / y]
    a ≔ y = x + 0; x; z | ⪮[z / 𝗦y]; z; ↘↘↘ | ✂; 𝗦y | replace_cut.MP
    b ≔ a; a↘.recontra | deduce.commute_ante.MP;
    (¬y = x + Z; Z).↺ | deduce
    goal4[x / 𝗦Z]
    c ≔ y = x + 𝗦Z; x; z | ⪮[z / 𝗦y]
    d ≔ c; c↘.recontra | deduce.commute_ante.MP
    (x = 𝗦y).∀Z;
    (∀Z ignore['A / d]['B / b↘↙↘↙].MP.commute_ante ⇆.MP) | deduce
    distr['A / b↙]['B / b↘↙]['C / b↘↘].MP.MP.recontra.MP
    ⊦ goal
    goal[x / X][y / Y]
}
⤶ succ_is_not_leq

⊦ 𝗦X + 𝗦Y = 𝗦𝗦(X + Y)
⊦ 𝗦𝗦(X + Y) = 𝗦X + 𝗦Y
⊦ ¬y = 𝗦y + x
⊦ x ≤ y ⇒ ¬x = 𝗦y

x_less_succ ≔ {
    goal ≔ x < 𝗦x

    succ_is_not_leq[X / 𝗦x][Y / x].flip_postneg.MP.MP;
    ¬¬'X ⇒ 'X | apply.MP
    ⊦ goal
    goal[x / X]
}
⤶ x_less_succ
{
    goal ≔ x < x + 1
    x_less_succ[X / x]; u; ↘↓↘↙ | ✂; x + 1 | replace_cut.MP
    ⊦ goal
    goal[x / X]
}
⊦ X < 𝗦X
⊦ X < X + 1

{
    goal ≔ x ≤ y ⇒ 𝗦x ≤ 𝗦y
    step ≔ {
        goal ≔ y = x + a ⇒ 𝗦y = 𝗦x + a
        𝗦u; u; y; x + a | replace; u; ↘↘ | ✂; 𝗦x + a | replace_cut.MP
        ⊦ goal
        goal
    }

    step; Z; ↘↘↘ | ✂.conditional_exists_by_example[a / Z]; Z | exists_ante

    ⊦ goal
    goal[x / X][y / Y]
}

{
    goal ≔ 𝗦x ≤ 𝗦y ⇒ x ≤ y
    step ≔ {
        goal ≔ 𝗦y = 𝗦x + a ⇒ y = x + a
        𝗦y = u; u; v | ⪮[u = v / 𝗦x + a = 𝗦(x + a)].MP;
        peano2[X = Y / y = x + a] | deduce
        ⊦ goal
        goal
    }

    step; Z; ↘↘↘ | ✂.conditional_exists_by_example[a / Z]; Z | exists_ante

    ⊦ goal
    goal[x / X][y / Y]
}

⊦ X ≤ Y ⇒ 𝗦X ≤ 𝗦Y
⊦ 𝗦X ≤ 𝗦Y ⇒ X ≤ Y

{
    goal ≔ x = 0 ∨∃y x = 𝗦y
    i ≔ goal; x | ↺
    x_impl_or; i↙ | reduce.MP
    j ≔ i.MP
    a ≔ 𝗦x = 𝗦y; x; y | exists_by_example
    y_impl_or; j↙↘↘ | reduce.MP
    ∀x(ignore; j↙↘ | reduce.MP)
    j.MP[x].MP
    ⊦ goal
    goal[x / X]
}
⊦ X = 0 ∨∃y X = 𝗦y

{
    goal ≔ ∀x(x ≤ y ∨ y ≤ x)

    ∀x(y_impl_or; x ≤ 0 ∨ 0 ≤ x | reduce.MP)
    i ≔ goal; y | ↺.MP

    /*
    We still need to prove that
    ∀y(∀x((x ≤ y)∨(y ≤ x)) ⇒ ∀x((x ≤ 𝗦(y))∨(𝗦(y) ≤ x)))
     */

    /*
    We will prove the expression below, then(∀y h)will prove i.
     */
    h ≔ (∀x((x ≤ y)∨(y ≤ x))) ⇒ ∀x((x ≤ 𝗦(y))∨(𝗦(y) ≤ x))

    /*
    Now we'll prove the expression below instead, from which
    we'll somehow get h, probably with.∀x ⇆something
    like that.
     */
    h' ≔ (∀x((x ≤ y)∨(y ≤ x))) ⇒ (x ≤ 𝗦(y))∨(𝗦(y) ≤ x)

    /*
    We want to prove h' in two parts, once for x = 0,
    once for x = 𝗦a.
     */

    /*
    This is the part for x = 0.
     */
    h'0 ≔ {
        goal ≔ (∀x((x ≤ y)∨(y ≤ x))) ⇒ (0 ≤ 𝗦(y))∨(𝗦(y) ≤ 0)

        x_impl_or; goal↘ | reduce.MP
        ignore; goal | reduce.MP

        ⊦ goal
        goal
    }

    /*
    This is the part for x = 𝗦a.
     */
    h'S ≔ {
        goal ≔ (∀x((x ≤ y)∨(y ≤ x))) ⇒ (𝗦(a) ≤ 𝗦(y))∨(𝗦(y) ≤ 𝗦(a))

        m ≔ X ≤ Y ⇒ 𝗦X ≤ 𝗦Y
        b ≔ or_impl_distr['X ⇒ 'Y / m[X / x][Y / y]]['Z ⇒ 'W / m[X / y][Y / x]].MP.MP
        c ≔ (∀x b) ⇆.MP
        c; c↘[a] | deduce
        ⊦ goal
        goal
    }

    /*
    TODO from h'0 ∧ h'S prove h' using X = 0 ∨∃y X = 𝗦y
     */
    two_cases ≔ (X = 0 ∨∃y X = 𝗦y)[X / x]

    /* Prove h' for x = 0 */
    ignore['A / h'0]['B / x = 0].MP; 0 = x ⇒ x = 0 | prededuce
    h'0a ≔ h'[x / x0]; x0; x | ⪮[x0 / 0]; distr | apply.MP.MP;
    x = 0 ⇒ 0 = x | prededuce

    /* Prove h' for x = 𝗦a */
    ignore['A / h'S]['B / x = 𝗦a].MP; 𝗦a = x ⇒ x = 𝗦a | prededuce
    h'Sa ≔ h'[x / xS]; xS; x | ⪮[xS / 𝗦a]; distr | apply.MP.MP;
    x = 𝗦a ⇒ 𝗦a = x | prededuce

    /* Reshape the proof of h' for x = 𝗦a to have an exists at
    the beginning, since that's how the split in two_cases is
    proven */
    h'Sb ≔ h'Sa[y / Y][a / y]; y | exists_ante[Y / y]

    conditional_or['X ⇒ 'Z / h'0a]['Y ⇒ 'Z / h'Sb].MP.MP.MP

    /* This concludes the proof of h', now back to h */
    h_almost ≔ ∀x h' ⇆.MP
    h_almost↙↘.∀x; h_almost | deduce

    /* Now that h is ready, finish the induction */
    ∀y h
    result ≔ i.MP[y].MP[x].MP
    result[x / X][y / Y]
}

⊦ X ≤ Y ∨ Y ≤ X

{
    goal ≔ x ∣ x * a
    x * a = x * M; a; M | exists_by_example
    ⊦ goal
    goal[x / X][a / A]
}
⊦ X ∣ X * A

{
    goal ≔ x ∣ a * x
    x ∣ u; u; v | ⪮[u = v / x * a = a * x].MP.MP
    ⊦ goal
    goal[x / X][a / A]
}
⊦ X ∣ A * X

mul_div ≔ {
    goal ≔ x ∣ y ⇒ x' ∣ y' ⇒ x * x' ∣ y * y'
    (x * x') * (a * a') = (x * a) * (x' * a') | eq_flip
    y * u; u; y'; x' * a' | replace; u; ↘↘↙ | ✂; x * a | replace_cut;
    u; ↘↘↘ | ✂; (x * x') * (a * a') | replace_cut.MP;
    xyz_impl_and | apply.MP;
    M; ↘↘↘ | ✂ | conditional_exists_by_example;
    and_impl_xyz | apply.MP[a / M];
    M | exists_ante | commute_ante[a' / M];
    M | exists_ante | commute_ante

    ⊦ goal
    goal[x / X][x' / X'][y / Y][y' / Y']
}
⊦ X ∣ Y ⇒ X' ∣ Y' ⇒ X * X' ∣ Y * Y'
⤶ mul_div

{
    goal ≔ 1 ∣ x
    x = 1 * M; x; M | exists_by_example
    ⊦ goal
    goal[x / X]
}
⊦ 1 ∣ X

{
    goal ≔ x ∣ y ⇒ x ∣ a * y

    1 ∣ a; x ∣ y; mul_div | apply2.MP;
    u; ↘↓↘↓↘↙ | ✂; x | replace_cut.MP

    ⊦ goal
    goal[x / X][y / Y][a / A]
}
⊦ X ∣ Y ⇒ X ∣ A * Y

remainder ≔ λ{
    /*
    Argument: n; m; k
    Returns: Whether k is the remainder of n divided by m
     */
    n ≔ ●ⅰ
    m ≔ ●ⅱ
    k ≔ ●ⅲ
    ↵ k < m ∧∃d n = d * m + k
}
⤶ remainder

element ≔ λ{
    /*
    Argument: b; c; i; x
    Returns: Whether x is the i'th element(0-based)in the sequence
    encoded by b; c

    See https: /  / en.wikipedia.org / wiki / G%C3%B6del%27s_%CE%B2_function,
    that is, Gödel's β function
     */
    b ≔ ●ⅰ
    c ≔ ●ⅱ
    i ≔ ●ⅲ
    x ≔ ●ⅳ
    ↵ b; i * c + c + 1; x | remainder
}
⤶ element

singleton ≔ λ{
    /*
    Argument: value
    Returns: the encoding of a sequence starting with the value
     */
    ↵ ●; ●
}
⤶ singleton

{
    goal ≔ n.singleton; 0; n | element

    0 = 0 * n
    n = 0 + n; (u + n; u; 0; 0 * n | replace.MP) | eq_trans
    a ≔ u + 1; u; n; (0 * n) + n | replace.MP | eq_flip
    goal1 ≔ n < u; u; v | ⪮[v = u / a].MP.MP
    X = u + X; u; v | ⪮[u = v / 0 = 0 * Y].MP.MP
    goal2 ≔ n = d * (((0 * n) + n) + 1) + n; 0; d | exists_by_example
    x_impl_y_impl_and['X / goal1]['Y / goal2].MP.MP
    ⊦ goal
    goal[n / X]
}
⊦ X.singleton; 0; X | element
⊦ 3.singleton; 0; 3 | element

/*
gcd ≔ λ{
    /*
    Argument: x; y; d
    Returns: whether d is the greatest common divisor of x ∧ y
     */
    x ≔ ●ⅰ
    y ≔ ●ⅱ
    d ≔ ●ⅲ
    ↵ d ∣ x ∧ d ∣ y ∧∀d' d' ∣ x ∧ d' ∣ y ⇒ d' ≤ d
}

gcd_commutes ≔ {
    ⤷ gcd
    goal ≔ x; y; d | gcd ⇒ y; x; d | gcd
    goal
    ⊦ goal
}

gcd_divides_x ≔ {
    ⤷ gcd
    goal ≔ x; y; d | gcd ⇒ d ∣ x
    goal
    ⊦ goal
}

gcd_divides_y ≔ {
    ⤷ gcd
    goal ≔ x; y; d | gcd ⇒ d ∣ y
    goal
    ⊦ goal
}

gcd_exists ≔ {
    ⤷ gcd
    goal ≔ 1 ≤ x ∨ 1 ≤ y ⇒ ∃d x; y; d | gcd
    goal
    ⊦ goal
}

gcd_unique ≔ {
    ⤷ gcd
    goal ≔ x; y; d | gcd ⇒ x; y; d' | gcd ⇒ d = d'
    goal
    ⊦ goal
}

max ≔ λ{
    /*
    Argument: x; y; m
    Returns: whether m equals the max of x; y
     */
    ↵ (m = x ∧ y ≤ x)∨(m = y ∧ x ≤ y)
}

max_exists ≔ {
    ⤷ max
    goal ≔ ∀x∀y∃m x; y; m | max
    ⊦ goal
}

max_unique ≔ {
    ⤷ max
    goal ≔ x; y; m | max ∧ x; y; m' | max ⇒ m = m'
    ⊦ goal
}

max_is_x_or_y ≔ {
    ⤷ max
    goal ≔ x; y; m | max ⇒ m = x ∨ m = y ℻
    ⊦ goal
}

x_leq_max ≔ {
    ⤷ max
    goal ≔ x; y; m | max ⇒ x ≤ m
    ⊦ goal
}

y_leq_max ≔ {
    ⤷ max
    goal ≔ x; y; m | max ⇒ y ≤ m
    ⊦ goal
}

max_commutes ≔ {
    ⤷ max
    goal ≔ x; y; m | max ⇒ y; x; m | max
    ⊦ goal
}
 */

{
    goal ≔ (∃x 'x) ⇒ 'x
    ((¬'x).∀x).flip_preneg.MP
    ⊦ goal
}

{
    q ≔ peano4↙[X / x][Y / y]; add_comm | apply
    (𝗦X + 𝗦Y = 𝗦𝗦(X + Y))[X / z][Y / z]
    w ≔ add_XY_ZW_eq_XZ_YW[X / Z][Z / x][Y / W][W / 𝗦z]; Z; ↘↘ | ✂; 𝗦𝗦(z + z) | replace_cut.MP
    e ≔ 𝗦(x + y) = x + 𝗦y; q | eq_trans
    r ≔ {
        goal ≔ a = b + 𝗦c ⇒ ¬a = b
        ¬y = 𝗦y + x; z; ↓↘ | ✂; 𝗦(y + x) | replace_cut.MP; z; ↓↘ | ✂; y + 𝗦x | replace_cut.MP[x / c][y / a];
        b; ↓↘↙ | ✂; b | replace_cut.flip_postneg.MP
        ⊦ goal
        goal
    }
    t ≔ w; peano4[X / w↘↙][Y / w↘↘↓] | eq_trans;
    (e; z; ↙↓ | ✂; y + x | replace_cut.MP[x / 𝗦(z + z)][y / x + x]) | eq_trans
    u ≔ X + X; X; y; x + 𝗦z | replace; X; ↘↘ | ✂; t↘ | replace_cut.MP; r[a / y + y][b / 𝗦(x + x)][c / z + z] | deduce.flip_postneg.MP
    (y + y = 𝗦(x + x)).∀z; (∀z ignore['A / u]['B / ¬y = x + z].MP.commute_ante ⇆.MP) | deduce
    o ≔ (x ≤ y ⇒ x + x ≤ y + y)[y / z][x / y][z / x]; (x ≤ y ⇒ ¬x = 𝗦y)[y / z][x / y + y][z / x + x] | deduce
    i ≔ (x = y ⇒ x ≤ y)[y / z][x / y][z / x]; z; ↙↘ | ✂; x + 0 | replace_cut.MP;
    o | deduce.flip_postneg.MP; (¬y = x + z; z).↺ | deduce; distr | apply.MP.MP
    p ≔ ∀y(i; (i↘; Z).rename_quantify | deduce.recontra.MP.recontra.MP; x ≤ y ∨ y ≤ x | deduce; o | deduce; 'x ∨ 'x ⇒ 'x | apply.MP.neq_flip)
    (∃y𝗦x = y + y).∀y; (∀y((x = y ⇒ y = x)[x / z][y / x + x]; (p; z; ↘↓↙↓ | ✂;
                z | replace_cut) | deduce[x / y][z / x].recontra.MP) ⇆.MP) | deduce.flip_preneg.MP
}

⊦ 𝗦(x + x) | is_odd
⊦ (x + 𝗦y) + (x + 𝗦y) = (x + x) + 𝗦𝗦(y + y)
⊦ (x + 𝗦y) + (x + 𝗦y) = 𝗦(x + x) + 𝗦(y + y)
⊦ 𝗦(x + y) = 𝗦x + y
⊦ a = b + 𝗦c ⇒ a ≠ b
⊦ (∃x 'x) ⇒ 'x
⊦ x.is_even ⇒ (𝗦x).is_odd
⊦ x.is_odd ∨ x.is_even
⊦ x.is_even ⇒ ¬x.is_odd
⊦ x.is_odd ⇒ ¬x.is_even

{
    goal ≔ x.is_odd ⇒ (𝗦x).is_even

    proof ≔ contrapose; goal | reduce
    i ≔ proof↙; x | ↺
    ignore; i↙ | reduce.MP
    j ≔ i.MP
    𝗦𝗦u = 𝗦y + 𝗦y; u; v | ⪮[u = v / y + y = x].commute_ante.MP;
    x = y + y ⇒ y + y = x | prededuce[y / Y]
    a ≔ x = Y + Y ⇒ 𝗦𝗦x = y + y;
    𝗦Y; y | conditional_exists_by_example[Y / y]; y | exists_ante
    b ≔ ('X ⇒ 'X)['X / ∃y𝗦x = y + y]
    c ≔ or_impl_distr['X ⇒ 'Y / a]['Z ⇒ 'W / b].MP.MP
    ∀x(('X ∨ 'Y ⇒ 'Y ∨ 'X)['Y ∨ 'X / c↙]; c | deduce)
    j.MP[x].MP
    proof.MP
    ⊦ goal
    goal[x / X]
}
⊦ X.is_odd ⇒ (𝗦X).is_even
⊦ (𝗦X).is_even ∨ X.is_even

distr['B / 'A]['C / 'B].commute_ante.MP
⊦ ('A ⇒ 'A ⇒ 'B) ⇒ 'A ⇒ 'B

{
    goal ≔ x ≤ 𝗦w ⇒ x ≤ w ∨𝗦w = x
    {
        goal ≔ 𝗦w = x + z ⇒ x ≤ w ∨𝗦w = x
        ⊦ (x = 0 ∨∃y x = 𝗦y)[x / z]
        z0 ≔ 𝗦w = x + u; u; v | ⪮[u = v / z = 0]; u; ↘↘↘ | ✂; x | replace_cut.MP
        zS ≔ {
            𝗦w = x + u; u; v | ⪮[u = v / z = 𝗦t]
            𝗦w = x + 𝗦t; x + 𝗦t = 𝗦(x + t); equals_transitive | apply2.commute_ante.MP;
            peano2[X / w][Y / x + t] | deduce; Z; ↘↘↘ | ✂.conditional_exists_by_example;
            u; ↙↘↘ | ✂; z | replace_cut; z = 𝗦t ⇒ 𝗦t = z | prededuce[t / y]; y | exists_ante
        }
        a ≔ z0; zS; or_impl_distr | apply2.MP.MP.MP; conditional_or' | apply.MP
        a; (a↘; or_comm | apply) | deduce
        ⊦ goal
        goal
    }[z / Z]; Z | exists_ante
    ⊦ goal
    goal[x / X][w / Y]
}
⊦ X ≤ 𝗦Y ⇒ X ≤ Y ∨𝗦Y = X

{
    goal ≔ ∃m∀d d ≤ n ⇒ d ∣ m
    i ≔ goal; n | ↺
    0 = d * M; 0; M | exists_by_example
    ∀d(ignore['A / d ∣ 0]['B / d ≤ 0].MP); m; ↘↘↓↘↓↙ | ✂.exists_by_example
    j ≔ i.MP
    step ≔ {
        goal ≔ (∀d d ≤ n ⇒ d ∣ m) ⇒ ∀d d ≤ 𝗦n ⇒ d ∣ 𝗦n * m
        a ≔ goal↙
        a_small ≔ a[d]; xyz_impl_and | apply.MP;
        d ∣ m ⇒ d ∣ 𝗦n * m | deduce;
        and_impl_xyz | apply.MP.commute_ante
        a_sn ≔ ignore
        ['A / u ∣ 𝗦n * m; u; v | ⪮[u = v / 𝗦n = d].commute_ante.MP]
        ['B / ∀d d ≤ n ⇒ d ∣ m].MP.commute_ante
        b ≔ ∀d(d ≤ 𝗦n ⇒ d ≤ n ∨𝗦n = d;
            (a_small; a_sn; conditional_or | apply2.MP.MP)
             | deduce.commute_ante) ⇆.MP
        b↙↘.∀d; b | deduce
        ⊦ goal
        goal
    }
    ∀n(step[m / m']; m; ↘↘↘↓↘↓↙ |
        ✂.conditional_exists_by_example[m' / m];
        m | exists_ante)
    j.MP[n].MP
    ⊦ goal
}
⊦ ∀n∃m∀d d ≤ n ⇒ d ∣ m
