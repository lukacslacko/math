from dataclasses import dataclass
from enum import Enum


class Kind(Enum):
    VAR = "var"
    IMPL = "->"
    NEG = "~"
    EQ = "="
    ZERO = "0"
    SUCC = "S"
    PLUS = "+"
    MUL = "*"
    FORALL = "∀"


ARITY_1 = {Kind.NEG, Kind.SUCC}
ARITY_2 = {Kind.IMPL, Kind.EQ, Kind.PLUS, Kind.MUL, Kind.FORALL}
EXPRESSION = {Kind.VAR, Kind.ZERO, Kind.SUCC, Kind.PLUS, Kind.MUL}


@dataclass
class Phrase:
    free: set[str]
    kind: Kind
    children: list["Phrase"]
    is_known_truth: bool = False

    def __str__(self) -> str:
        if self.kind == Kind.VAR:
            return self.varname()
        elif self.kind == Kind.IMPL:
            return f"({self.children[0]} -> {self.children[1]})"
        elif self.kind == Kind.NEG:
            return f"~{self.children[0]}"
        elif self.kind == Kind.EQ:
            return f"({self.children[0]} = {self.children[1]})"
        elif self.kind == Kind.ZERO:
            return "0"
        elif self.kind == Kind.SUCC:
            return f"S({self.children[0]})"
        elif self.kind == Kind.PLUS:
            return f"({self.children[0]} + {self.children[1]})"
        elif self.kind == Kind.MUL:
            return f"({self.children[0]} * {self.children[1]})"
        elif self.kind == Kind.FORALL:
            return f"(∀{self.children[0]} {self.children[1]})"
        else:
            raise ValueError(f"Unknown kind {self.kind}")

    def varname(self) -> str:
        if self.kind != Kind.VAR:
            raise ValueError(f"varname: expected variable, got {self}")
        return next(iter(self.free))

    def axiom(self) -> "Phrase":
        self.is_known_truth = True
        return self

    def subs(self, x: "Phrase", q: "Phrase") -> "Phrase":
        result = subs(self, x, q)
        return result

    # Make phrase[x, q] syntax work
    def __getitem__(self, item):
        if not isinstance(item, tuple) or len(item) != 2:
            raise ValueError("Expected two arguments for substitution")
        x, q = item
        return self.subs(x, q)

    # Make self >> q create implication
    def __rshift__(self, q: "Phrase") -> "Phrase":
        return impl(self, q)

    def __call__(self, arg: "Phrase") -> "Phrase":
        if self.kind == Kind.IMPL:
            return mp(self, arg)
        raise ValueError(f"Cannot call phrase of kind {self.kind}")

    def mp(self) -> "Phrase":
        if self.kind != Kind.IMPL:
            raise ValueError(f"mp: expected implication, got {self}")
        return mp(self, self.left())

    def __invert__(self) -> "Phrase":
        return neg(self)

    def __add__(self, q: "Phrase") -> "Phrase":
        return plus(self, q)

    def __mul__(self, q: "Phrase") -> "Phrase":
        return mul(self, q)

    def S(self) -> "Phrase":
        return succ(self)

    def __eq__(self, q: "Phrase") -> "Phrase":
        return eq(self, q)

    def forall(self, v: "Phrase") -> "Phrase":
        if v.kind != Kind.VAR:
            raise ValueError(f"forall: v must be a variable, got {v}")
        if self.kind in EXPRESSION - {Kind.VAR}:
            raise ValueError(f"forall: self must be a proposition, got {self}")
        phrase = make_phrase(Kind.FORALL, [v, self], is_known_truth=self.is_known_truth)
        phrase.free.discard(v.varname())
        return phrase

    def right(self) -> "Phrase":
        if self.kind not in ARITY_2:
            raise ValueError(
                f"right() can only be called on {ARITY_2}, got {self.kind}"
            )
        return self.children[1]

    def left(self) -> "Phrase":
        if self.kind not in ARITY_2:
            raise ValueError(f"left() can only be called on {ARITY_2}, got {self.kind}")
        return self.children[0]

    def child(self) -> "Phrase":
        if self.kind not in ARITY_1:
            raise ValueError(
                f"child() can only be called on {ARITY_1}, got {self.kind}"
            )
        return self.children[0]


phrases = {}


def make_phrase(
    kind: Kind, children: list[Phrase], is_known_truth: bool = False
) -> Phrase:
    free = set()
    for child in children:
        free.update(child.free)
    phrase = Phrase(
        free=free, kind=kind, children=children, is_known_truth=is_known_truth
    )
    s = str(phrase)
    if s not in phrases:
        phrases[s] = phrase
    phrases[s].is_known_truth |= is_known_truth
    return phrases[s]


def impl(p: Phrase, q: Phrase) -> Phrase:
    if p.kind in EXPRESSION - {Kind.VAR} or q.kind in EXPRESSION - {Kind.VAR}:
        raise ValueError(f"impl: both p and q must be propositions, got {p}, {q}")
    return make_phrase(Kind.IMPL, [p, q])


def eq(p: Phrase, q: Phrase) -> Phrase:
    if p.kind not in EXPRESSION or q.kind not in EXPRESSION:
        raise ValueError(f"eq: both p and q must be expressions, got {p}, {q}")
    return make_phrase(Kind.EQ, [p, q])


def zero() -> Phrase:
    return make_phrase(Kind.ZERO, [])


def succ(p: Phrase) -> Phrase:
    if p.kind not in EXPRESSION:
        raise ValueError(f"succ: p must be an expression, got {p}")
    return make_phrase(Kind.SUCC, [p])


def plus(p: Phrase, q: Phrase) -> Phrase:
    if p.kind not in EXPRESSION or q.kind not in EXPRESSION:
        raise ValueError(f"plus: both p and q must be expressions, got {p}, {q}")
    return make_phrase(Kind.PLUS, [p, q])


def mul(p: Phrase, q: Phrase) -> Phrase:
    if p.kind not in EXPRESSION or q.kind not in EXPRESSION:
        raise ValueError(f"mul: both p and q must be expressions, got {p}, {q}")
    return make_phrase(Kind.MUL, [p, q])


def neg(p: Phrase) -> Phrase:
    if p.kind in EXPRESSION - {Kind.VAR}:
        raise ValueError(f"neg: p must be a proposition, got {p}")
    return make_phrase(Kind.NEG, [p])


def var(name: str) -> Phrase:
    if name not in phrases:
        phrases[name] = Phrase(free={name}, kind=Kind.VAR, children=[])
    return phrases[name]


def subs(p: Phrase, x: Phrase, q: Phrase) -> Phrase:
    if x.kind != Kind.VAR:
        raise ValueError(f"subs: x must be a variable, got {x}")
    if p.kind == Kind.VAR:
        if p is x:
            return q
        else:
            return p
    if p.kind == Kind.FORALL:
        if p.left() is x:
            return p
        if p.left().varname() in q.free:
            #
            # Why this is needed:
            #
            # Consider P = ∀x ((∀y (y = 0 -> x = 0)) -> x = 0).
            # P is true, but substituting x with y would yield
            # ∀y ((∀y (y = 0 -> y = 0)) -> y = 0), which is not true.
            #
            raise ValueError(
                f"subs: cannot substitute {x} with {q} in {p} due to variable capture"
            )
    new_children = [subs(child, x, q) for child in p.children]
    new_free = set()
    for child in new_children:
        new_free.update(child.free)
    return make_phrase(p.kind, new_children, is_known_truth=p.is_known_truth)


def mp(impl_phrase: Phrase, p_phrase: Phrase) -> Phrase:
    if not impl_phrase.is_known_truth:
        raise ValueError(f"mp: first argument must be a known truth {impl_phrase}")
    if not p_phrase.is_known_truth:
        raise ValueError(f"mp: second argument must be a known truth {p_phrase}")
    if impl_phrase.kind != Kind.IMPL:
        raise ValueError(f"mp: first argument must be an implication {impl_phrase}")
    if str(impl_phrase.left()) != str(p_phrase):
        raise ValueError(
            f"mp: antecedent does not match {impl_phrase.left()} != {p_phrase}"
        )
    q_phrase = impl_phrase.right()
    q_phrase.is_known_truth = True
    return q_phrase


def forall_elim(forall_phrase: Phrase, term: Phrase) -> Phrase:
    if forall_phrase.kind != Kind.FORALL:
        raise ValueError(
            f"forall_elim: first argument must be a universal quantification {forall_phrase}"
        )
    var_phrase = forall_phrase.left()
    body_phrase = forall_phrase.right()
    return (forall_phrase >> subs(body_phrase, var_phrase, term)).axiom()


def forall_distribute(forall_phrase: Phrase) -> Phrase:
    if forall_phrase.kind != Kind.FORALL:
        raise ValueError(
            f"forall_distribute: argument must be a universal quantification {forall_phrase}"
        )
    var = forall_phrase.left()
    inner = forall_phrase.right()
    if inner.kind != Kind.IMPL:
        raise ValueError(f"forall_distribute: inner must be an implication {inner}")
    A = inner.left()
    B = inner.right()
    return (forall_phrase >> (A.forall(var) >> B.forall(var))).axiom()


A = var("A")
B = var("B")
C = var("C")
x = var("x")
y = var("y")
z = var("z")
w = var("w")
X = var("X")
Y = var("Y")
Z = var("Z")
W = var("W")

ignore = (A >> (B >> A)).axiom()
distr = ((A >> (B >> C)) >> ((A >> B) >> (A >> C))).axiom()
contra = ((neg(A) >> neg(B)) >> (B >> A)).axiom()

impl_refl = distr[A, x][B, x >> x][C, x](ignore[A, x][B, x >> x])(ignore[A, x][B, x])

eq_refl = (A == A).axiom()


def eq_subs(x: Phrase, y: Phrase, A: Phrase) -> Phrase:
    return ((x == y) >> (A >> A[x, y])).axiom()


def _commute_antecedents() -> Phrase:
    xyz = x >> (y >> z)

    # Define helper aliases for clarity
    H = xyz  # x -> (y -> z)
    Q = x >> y  # x -> y
    R = x >> z  # x -> z
    D1 = Q >> R  # (x -> y) -> (x -> z)

    # Derivation using the Deduction Theorem algorithm:
    # We want to transform the derivation H |- y -> R into a proof of H -> (y -> R).

    # 1. H -> D1
    # From Axiom S: (x -> (y -> z)) -> ((x -> y) -> (x -> z))
    step1 = distr[A, x][B, y][C, z]

    # 2. H -> (D1 -> (y -> D1))
    # Lift Axiom K: D1 -> (y -> D1) over H
    k_d1_y = ignore[A, D1][B, y]
    step2 = ignore[A, k_d1_y][B, H](k_d1_y)

    # 3. H -> (y -> D1)
    # Combine step1 and step2 using Axiom S
    # S: (H -> (D1 -> (y -> D1))) -> ((H -> D1) -> (H -> (y -> D1)))
    s_lift1 = distr[A, H][B, D1][C, y >> D1]
    step3 = s_lift1(step2)(step1)

    # 4. H -> ((y -> D1) -> ((y -> Q) -> (y -> R)))
    # Lift Axiom S (inner): (y -> (Q -> R)) -> ((y -> Q) -> (y -> R)) over H
    s_inner = distr[A, y][B, Q][C, R]
    step4 = ignore[A, s_inner][B, H](s_inner)

    # 5. H -> ((y -> Q) -> (y -> R))
    # Combine step3 and step4 using Axiom S
    # S: (H -> ((y->D1) -> Target)) -> ((H -> (y->D1)) -> (H -> Target))
    target_inner = (y >> Q) >> (y >> R)
    s_lift2 = distr[A, H][B, y >> D1][C, target_inner]
    step5 = s_lift2(step4)(step3)

    # 6. H -> (y -> Q)
    # Lift Axiom K: y -> (x -> y) over H
    # Note: y -> Q is y -> (x -> y)
    k_y_x = ignore[A, y][B, x]
    step6 = ignore[A, k_y_x][B, H](k_y_x)

    # 7. H -> (y -> R)
    # Combine step5 and step6 using Axiom S
    # S: (H -> ((y->Q) -> (y->R))) -> ((H -> (y->Q)) -> (H -> (y->R)))
    s_lift3 = distr[A, H][B, y >> Q][C, y >> R]
    return s_lift3(step5)(step6)


commute_antecedents = _commute_antecedents()


def commute_ante(s: Phrase) -> Phrase:
    if s.kind != Kind.IMPL:
        raise ValueError(f"commute_ante: expected implication, got {s}")
    if s.right().kind != Kind.IMPL:
        raise ValueError(f"commute_ante: expected implication as consequent, got {s}")
    return commute_antecedents[x, X][y, Y][z, Z][X, s.left()][Y, s.right().left()][
        Z, s.right().right()
    ](s)


def _chain() -> Phrase:
    Q = x >> y
    P = y >> z
    R = x >> z
    s1 = distr[A, x][B, y][C, z]
    s2 = ignore[A, P][B, x]
    s3 = ignore[A, s1][B, P](s1)
    s5 = distr[A, P][B, x >> P][C, Q >> R](s3)
    almost = s5(s2)
    return commute_antecedents[x, X][y, Y][z, Z][X, P][Y, Q][Z, R](almost)


chain = _chain()


def deduce(a_impl_b: Phrase, b_impl_c: Phrase) -> Phrase:
    if a_impl_b.kind != Kind.IMPL:
        raise ValueError(f"deduce: expected implication, got {a_impl_b}")
    if b_impl_c.kind != Kind.IMPL:
        raise ValueError(f"deduce: expected implication, got {b_impl_c}")
    if str(a_impl_b.right()) != str(b_impl_c.left()):
        raise ValueError(
            f"deduce: consequents/antecedents do not match {a_impl_b.right()} != {b_impl_c.left()}"
        )
    return chain[x, X][y, Y][z, Z][X, a_impl_b.left()][Y, a_impl_b.right()][
        Z, b_impl_c.right()
    ](a_impl_b)(b_impl_c)


def _double_neg() -> Phrase:
    # 1. Start with K: ~~x -> (~~~~x -> ~~x)
    # A = ~~x, B = ~~~~x
    step1 = ignore[A, ~~x][B, ~~~~x]

    # 2. Use Contraposition: (~~~~x -> ~~x) -> (~x -> ~~~x)
    # Contra: (~A -> ~B) -> (B -> A)
    # Let A = ~~~x, B = ~x.
    # Then ~A = ~~~~x, ~B = ~~x.
    step2 = contra[A, ~~~x][B, ~x]

    # 3. Chain step1 and step2: ~~x -> (~x -> ~~~x)
    # chain implies (x -> y) -> ((y -> z) -> (x -> z))
    # x = ~~x
    # y = ~~~~x -> ~~x (consequent of step1)
    # z = ~x -> ~~~x (consequent of step2)
    step3 = chain[x, ~~x][y, step1.right()][z, step2.right()](step1)(step2)

    # 4. Prepare Contraposition for the final result: (~x -> ~~~x) -> (~~x -> x)
    # Contra: (~A -> ~B) -> (B -> A)
    # Let A = x, B = ~~x.
    # Then ~A = ~x, ~B = ~~~x.
    target_contra = contra[A, x][B, ~~x]

    # 5. Chain step3 and target_contra: ~~x -> (~~x -> x)
    # x = ~~x
    # y = ~x -> ~~~x (consequent of step3)
    # z = ~~x -> x (consequent of target_contra)
    step5 = chain[x, ~~x][y, step3.right()][z, target_contra.right()](step3)(
        target_contra
    )

    # 6. Contraction: Reduce (~~x -> (~~x -> x)) to (~~x -> x)
    # Use S: (A -> (B -> C)) -> ((A -> B) -> (A -> C))
    # A = ~~x, B = ~~x, C = x
    s_dist = distr[A, ~~x][B, ~~x][C, x]

    # Apply S to step5 to get: (~~x -> ~~x) -> (~~x -> x)
    step6 = s_dist(step5)

    # 7. Eliminate the antecedent (~~x -> ~~x) using Identity
    id_phrase = impl_refl[x, ~~x]

    return step6(id_phrase)


double_neg = _double_neg()
add_double_neg = contra[A, ~~x][B, x](double_neg[x, ~x])

eq_symm = commute_ante(eq_subs(x, y, x == z)[z, x])(eq_refl[A, x])
eq_trans = deduce(eq_symm, eq_subs(y, x, y == z))


def eq_flip(p: Phrase) -> Phrase:
    if p.kind != Kind.EQ:
        raise ValueError(f"eq_flip: expected equality, got {p}")
    return eq_symm[x, X][y, Y][X, p.left()][Y, p.right()](p)


def eq_chain(p: Phrase, q: Phrase) -> Phrase:
    if p.kind != Kind.EQ:
        raise ValueError(f"eq_chain: expected equality for p, got {p}")
    if q.kind != Kind.EQ:
        raise ValueError(f"eq_chain: expected equality for q, got {q}")
    if str(p.right()) != str(q.left()):
        raise ValueError(
            f"eq_chain: consequents/antecedents do not match {p.right()} != {q.left()}"
        )
    return eq_trans[x, X][y, Y][z, Z][X, p.left()][Y, p.right()][Z, q.right()](p)(q)


peano1 = (~(zero() == x.S())).axiom()
peano2 = ((x.S() == y.S()) >> (x == y)).axiom()
peano3 = ((x + zero()) == x).axiom()
peano4 = ((x + y.S()) == (x + y).S()).axiom()
peano5 = ((x * zero()) == zero()).axiom()
peano6 = ((x * y.S()) == ((x * y) + x)).axiom()


def induction(P: Phrase, v: Phrase) -> Phrase:
    if v.kind != Kind.VAR:
        raise ValueError(f"induction: v must be a variable, got {v}")
    return (P[v, zero()] >> ((P >> P[v, v.S()]) >> P)).axiom()


x_eq_y_impl_Sx_eq_Sy = commute_ante(eq_subs(x, y, x.S() == z.S())[z, x])(
    eq_refl[A, x.S()]
)


def _zero_plus_x_eq_x() -> Phrase:
    P = (zero() + x) == x
    i = induction(P, x)
    step = i(peano3[x, zero()])
    a = peano4[x, zero()][y, x]
    aa = eq_trans[x, zero() + x.S()][y, (zero() + x).S()][z, x.S()](a)
    b = x_eq_y_impl_Sx_eq_Sy[y, zero() + x]
    c = eq_symm[x, zero() + x][y, x]
    d = deduce(c, b)
    e = deduce(d, aa)
    f = step(e)
    return f


zero_plus_x_eq_x = _zero_plus_x_eq_x()


def _Sx_plus_y_eq_Sx_plus_y() -> Phrase:
    P = (x.S() + y) == (x + y).S()
    i = induction(P, y)
    a = peano3[x, x.S()]
    b = eq_subs(x, x + zero(), x.S() == z.S())[z, x](eq_flip(peano3))(eq_refl[A, x.S()])
    c = eq_chain(a, eq_flip(b))
    step = i(c)
    d = peano4[x, x.S()][y, y]
    e = x_eq_y_impl_Sx_eq_Sy[x, X][y, Y][X, peano4.left()][Y, peano4.right()](peano4)
    f = x_eq_y_impl_Sx_eq_Sy[x, X][y, Y][X, x.S() + y][Y, (x + y).S()]
    g = eq_trans[x, X][y, Y][z, Z][X, (x + y).S().S()][Y, (x.S() + y).S()][
        Z, x.S() + y.S()
    ]
    h = commute_ante(deduce(f, g))(eq_flip(d))
    j = deduce(h, eq_symm[x, X][y, Y][X, h.right().left()][Y, h.right().right()])
    k = eq_trans[x, X][y, Y][z, Z][X, x.S() + y.S()][Y, (x + y).S().S()][
        Z, (x + y.S()).S()
    ]
    m = deduce(j, k)
    n = commute_ante(m)(e)
    return step(n)


Sx_plus_y_eq_Sx_plus_y = _Sx_plus_y_eq_Sx_plus_y()


def _plus_comm() -> Phrase:
    P = (x + y) == (y + x)
    i = induction(P, y)(eq_chain(peano3, eq_flip(zero_plus_x_eq_x)))
    a = peano4
    c = x_eq_y_impl_Sx_eq_Sy[x, X][y, Y][X, x + y][Y, y + x]
    d = eq_trans[x, X][y, Y][z, Z][X, (y + x).S()][Y, (x + y).S()][Z, x + y.S()]
    e = deduce(c, d)
    f = commute_ante(e)(eq_flip(a))
    h = eq_symm[x, X][y, Y][X, f.right().left()][Y, f.right().right()]
    j = deduce(f, h)
    g = eq_flip(Sx_plus_y_eq_Sx_plus_y[x, X][y, Y][X, y][Y, x])
    k = eq_trans[x, X][y, Y][z, Z][X, x + y.S()][Y, (y + x).S()][Z, y.S() + x]
    m = commute_ante(deduce(j, k))(g)
    return i(m)


plus_comm = _plus_comm()


def plus_comm_left(p: Phrase) -> Phrase:
    if p.kind != Kind.EQ:
        raise ValueError(f"plus_comm_left: expected equality, got {p}")
    left = p.left()
    if left.kind != Kind.PLUS:
        raise ValueError(f"plus_comm_left: expected plus on left side, got {left}")
    a = plus_comm[x, X][y, Y][X, left.left()][Y, left.right()]
    b = eq_chain(eq_flip(a), p)
    return b


def plus_comm_right(p: Phrase) -> Phrase:
    return eq_flip(plus_comm_left(eq_flip(p)))


def _x_eq_y_impl_x_plus_z_eq_y_plus_z() -> Phrase:
    a = eq_subs(y, x, y + z == X + z)[X, y]
    b = commute_ante(a)(eq_refl[A, y + z])
    c = deduce(eq_symm, b)
    return c


x_eq_y_impl_x_plus_z_eq_y_plus_z = _x_eq_y_impl_x_plus_z_eq_y_plus_z()


def _x_impl_y_eq_z_impl_x_impl_z_eq_y() -> Phrase:
    a = ignore[A, eq_symm[x, X][y, Y][X, y][Y, z]][B, x](
        eq_symm[x, X][y, Y][X, y][Y, z]
    )
    b = distr[A, x][B, y == z][C, z == y](a)
    return b


x_impl_y_eq_z_impl_x_impl_z_eq_y = _x_impl_y_eq_z_impl_x_impl_z_eq_y()


def _plus_assoc() -> Phrase:
    P = ((x + y) + z) == (x + (y + z))
    i = induction(P, z)
    a = peano3[x, x + y]
    b = plus_comm_left(
        x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, y][Y, y + zero()][Z, x](
            eq_flip(peano3[x, y])
        )
    )
    c = plus_comm_right(eq_chain(a, b))
    step = i(c)

    d = peano4[x, X][y, Y][X, x + y][Y, z]
    e = commute_ante(
        eq_subs(X, Y, X.S() == Z.S())[Z, X][X, (x + y) + z][Y, x + (y + z)]
    )(eq_refl[A, ((x + y) + z).S()])
    f = x_impl_y_eq_z_impl_x_impl_z_eq_y[x, X][y, Y][z, Z][X, e.left()][
        Y, e.right().left()
    ][Z, e.right().right()](e)
    g = eq_trans[x, X][y, Y][z, Z][X, d.left()][Y, d.right()][Z, f.right().right()](d)
    h = deduce(f, g)
    j = eq_flip(peano4[y, y + z])
    k = peano4[x, X][y, Y][X, y][Y, z]
    m = plus_comm_right(
        plus_comm_left(
            x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, (y + z).S()][
                Y, y + z.S()
            ][Z, x](eq_flip(k))
        )
    )
    n = eq_chain(j, m)
    p = eq_trans[x, X][y, Y][z, Z][X, h.right().left()][Y, h.right().right()][
        Z, n.right()
    ]
    q = commute_ante(deduce(h, p))(n)
    return step(q)


plus_assoc = _plus_assoc()
plus_assoc[x, X][y, Y][z, Z]
eq_flip(plus_assoc)[x, X][y, Y][z, Z]


def _zero_mul_x_eq_zero() -> Phrase:
    P = (zero() * x) == zero()
    i = induction(P, x)
    step = i(peano5[x, zero()])
    a = peano6[x, X][y, Y][X, zero()][Y, x]
    b = peano3[x, X][X, zero() * x]
    c = eq_chain(a, b)
    d = eq_subs(x, y, x == zero())[x, X][y, Y][Y, zero() * x.S()][X, zero() * x](
        eq_flip(c)
    )
    return step(d)


zero_mul_x_eq_zero = _zero_mul_x_eq_zero()

one = zero().S()


def _x_plus_one_eq_Sx() -> Phrase:
    P = (x + one) == x.S()
    i = induction(P, x)(zero_plus_x_eq_x[x, one])
    c = plus_comm_left(peano4[x, X][y, Y][X, one][Y, x])
    a = plus_comm[y, one]
    b = x_eq_y_impl_Sx_eq_Sy[x, X][y, Y][X, x + one][Y, one + x](a)
    d = eq_chain(c, b)
    e = eq_subs(X, Y, x.S() + one == X.S())[X, x + one][Y, x.S()]
    f = commute_ante(e)(d)
    return i(f)


x_plus_one_eq_Sx = _x_plus_one_eq_Sx()


def _one_mul_x_eq_x() -> Phrase:
    P = (one * x) == x
    step = induction(P, x)(peano5[x, one])
    a = peano6[x, X][y, Y][X, one][Y, x]
    b = x_plus_one_eq_Sx[x, one * x]
    c = eq_chain(a, b)
    d = eq_subs(X, Y, one * x.S() == X.S())[X, one * x][Y, x]
    e = commute_ante(d)(c)
    return step(e)


one_mul_x_eq_x = _one_mul_x_eq_x()


def _Sx_mul_y_eq_x_mul_y_plus_y() -> Phrase:
    P = (x.S() * y) == ((x * y) + y)
    i = induction(P, y)
    a = peano5[x, x.S()]
    b = peano5
    c = peano3[x, x * zero()]
    d = eq_chain(c, b)
    e = eq_chain(a, eq_flip(d))
    f = i(e)
    g = eq_flip(peano6[x, x.S()])
    h = peano6
    j = x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, x.S() * y][
        Y, (x * y) + y
    ][Z, x.S()]
    k = x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, x * y.S()][
        Y, (x * y) + x
    ][Z, y.S()](h)
    m = deduce(j, eq_symm[x, X][y, Y][X, j.right().left()][Y, j.right().right()])
    n = commute_ante(
        deduce(
            m,
            eq_trans[x, X][y, Y][z, Z][X, m.right().left()][Y, m.right().right()][
                Z, g.right()
            ],
        )
    )(g)
    p = x_impl_y_eq_z_impl_x_impl_z_eq_y[x, X][y, Y][z, Z][X, n.left()][
        Y, n.right().left()
    ][Z, n.right().right()](n)

    k2 = plus_comm_left(
        x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, y.S()][Y, y + one][
            Z, (x * y) + x
        ](eq_flip(x_plus_one_eq_Sx[x, y]))
    )
    k3 = plus_comm_right(eq_chain(k, k2))
    k4 = plus_assoc[x, X][y, Y][z, Z][X, x * y][Y, x][Z, y + one]
    k5 = eq_chain(k3, k4)

    ka = plus_assoc[y, one][z, y]
    kb = eq_subs(X, Y, (x + one) + y == x + X)[X, one + y][Y, y + one](
        plus_comm[x, one]
    )(ka)
    kc = plus_comm_left(
        plus_comm_right(
            x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][Z, x * y][X, kb.left()][
                Y, kb.right()
            ](kb)
        )
    )
    k6 = eq_chain(kc, eq_flip(k5))

    k7 = plus_comm_left(plus_assoc[x, X][y, Y][z, Z][X, x * y][Y, y][Z, x + one])

    m = plus_comm[x, X][y, Y][X, y][Y, x + one]
    n = plus_comm_right(
        plus_comm_left(
            x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, m.left()][
                Y, m.right()
            ][Z, x * y](m)
        )
    )
    n1 = eq_chain(n, k6)
    n2 = eq_chain(k7, n1)

    q = plus_comm_left(
        x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, x.S()][Y, x + one][
            Z, (x * y) + y
        ](eq_flip(x_plus_one_eq_Sx))
    )
    r = eq_trans[x, X][y, Y][z, Z][X, p.right().left()][Y, p.right().right()][
        Z, q.right()
    ]
    s = commute_ante(deduce(p, r))(q)
    t = eq_trans[x, X][y, Y][z, Z][X, s.right().left()][Y, s.right().right()][
        Z, n2.right()
    ]
    u = commute_ante(deduce(s, t))(n2)
    return f(u)


Sx_mul_y_eq_x_mul_y_plus_y = _Sx_mul_y_eq_x_mul_y_plus_y()


def _mul_comm() -> Phrase:
    P = (x * y) == (y * x)
    i = induction(P, y)(eq_chain(peano5, eq_flip(zero_mul_x_eq_zero)))
    a = peano6
    b = Sx_mul_y_eq_x_mul_y_plus_y[x, X][y, Y][X, y][Y, x]
    c = x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, x * y][Y, y * x][Z, x]
    c1 = x_impl_y_eq_z_impl_x_impl_z_eq_y[x, X][y, Y][z, Z][X, c.left()][
        Y, c.right().left()
    ][Z, c.right().right()](c)
    d = commute_ante(
        eq_trans[x, X][y, Y][z, Z][X, c.right().right()][Y, c.right().left()][
            Z, a.left()
        ]
    )(eq_flip(a))
    e = deduce(c1, d)
    e1 = x_impl_y_eq_z_impl_x_impl_z_eq_y[x, X][y, Y][z, Z][X, e.left()][
        Y, e.right().left()
    ][Z, e.right().right()](e)
    f = commute_ante(
        eq_trans[x, X][y, Y][z, Z][X, e1.right().left()][Y, e1.right().right()][
            Z, b.left()
        ]
    )(eq_flip(b))
    g = deduce(e1, f)
    return i(g)


mul_comm = _mul_comm()
mul_comm[x, X][y, Y]


def sum_of_eq_eq(eq1: Phrase, eq2: Phrase) -> Phrase:
    if eq1.kind != Kind.EQ:
        raise ValueError(f"sum_of_eq_eq: expected equality for eq1, got {eq1}")
    if eq2.kind != Kind.EQ:
        raise ValueError(f"sum_of_eq_eq: expected equality for eq2, got {eq2}")
    a = eq1.left()
    b = eq1.right()
    c = eq2.left()
    d = eq2.right()
    e = x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, a][Y, b][Z, c](eq1)
    f = plus_comm_left(
        plus_comm_right(
            x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, c][Y, d][Z, b](eq2)
        )
    )
    return eq_chain(e, f)


def plus_four_terms() -> Phrase:
    a = plus_assoc[x, X][y, Y][z, Z]
    b = plus_comm_right(a[X, x][Y, y][Z, z + w])
    c = plus_comm_right(a[X, x][Y, z][Z, y + w])
    d = a[X, y][Y, z][Z, w]
    e = a[X, z][Y, y][Z, w]
    eq_flip(plus_comm[x, z])
    g = x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, y + z][Y, z + y][
        Z, w
    ].mp()
    eq_chain(eq_chain(eq_flip(d), g), e)
    h = ((X == Y) >> (X + Z == Y + Z))[X, y + (z + w)][Y, z + (y + w)][Z, x].mp()
    return eq_chain(eq_chain(b, h), eq_flip(c))[x, X][y, Y][z, Z][w, W]


plus_four_terms()


def _mul_distr() -> Phrase:
    P = (x + y) * z == (x * z) + (y * z)
    i = induction(P, z)
    a = peano5[x, x + y]
    b = eq_subs(X, Y, (x * zero()) + X == zero())[X, zero()][Y, y * zero()](
        eq_flip(peano5[x, y])
    )(eq_chain(peano3[x, x * zero()], peano5))
    step = i(eq_chain(a, eq_flip(b)))

    c = peano6[x, X][y, Y][X, x + y][Y, z]
    d1 = peano6[y, z]
    d2 = peano6[y, z][x, y]
    e = sum_of_eq_eq(d1, d2)

    start = step.left().left()
    s1 = eq_symm[x, X][y, Y][X, start.left()][Y, start.right()]
    s2 = x_eq_y_impl_x_plus_z_eq_y_plus_z[x, X][y, Y][z, Z][X, s1.right().left()][
        Y, s1.right().right()
    ][Z, x + y]
    s3 = deduce(s1, s2)
    s4 = deduce(
        s3,
        eq_trans[x, X][y, Y][z, Z][X, s3.right().left()][Y, s3.right().right()][
            Z, c.left()
        ],
    )
    s5 = commute_ante(s4)(eq_flip(c))
    s6 = ((X + Y) + (Z + W) == (X + Z) + (Y + W))[X, x * z][Y, y * z][Z, x][W, y]
    s7 = eq_chain(s6, eq_flip(e))
    s8 = ((x == y) >> ((x == z) >> (y == z)))[x, X][y, Y][z, Z][X, s5.right().left()][
        Y, s5.right().right()
    ][Z, s7.right()]
    s9 = deduce(s5, s8)
    s10 = commute_ante(s9)(s7)

    return step(s10)


mul_distr = _mul_distr()
mul_distr[x, X][y, Y][z, Z]

two = one.S()
eq_refl[A, two]
peano3[x, zero()]
eq_flip(peano3[x, one])
eq_chain(
    peano4[x, one][y, zero()],
    eq_subs(X, Y, X.S() == two)[Y, one + zero()][X, one].mp().mp(),
)
assert (one + one == two).is_known_truth


def _mul_distr_left() -> Phrase:
    a = (X * Y == Y * X)[X, x + y][Y, z]
    b = (X * Y == Y * X)[X, x][Y, z]
    c = (X * Y == Y * X)[X, y][Y, z]
    d = sum_of_eq_eq(b, c)
    e = eq_chain(eq_chain(eq_flip(a), mul_distr), d)
    return e[x, X][y, Y][z, Z]


mul_distr_left = _mul_distr_left()

mul_eq_eq = commute_ante(eq_subs(z, y, x * z == x * w)[w, z])(eq_refl[A, x * z])[x, X][
    y, Y
][z, Z]


def mul_assoc() -> Phrase:
    P = (x * (y * z)) == ((x * y) * z)
    i = induction(P, z)
    a = peano5[x, x * y]
    c = eq_subs(X, Y, x * X == zero())[X, zero()][Y, y * zero()].mp().mp()
    eq_chain(c, eq_flip(a))
    i = i.mp()

    d = ((X * Y.S()) == ((X * Y) + X))[X, x * y][Y, z]
    eq_flip(((X * Y.S()) == ((X * Y) + X))[X, y][Y, z])
    f = mul_eq_eq[X, x][Y, y * z.S()][Z, (y * z) + y].mp()
    g = (Z * (X + Y) == (Z * X) + (Z * Y))[Z, x][X, y * z][Y, y]
    h = eq_chain(f, g)
    j = ((X == Y) >> (X + Z == Y + Z))[X, x * (y * z)][Y, (x * y) * z][Z, x * y]
    k = (X == Y) >> ((Y == Z) >> (X == Z))
    k1 = k[X, ((x * (y * z)) + (x * y))][Y, ((x * y) * z) + (x * y)][Z, (x * y) * z.S()]
    k2 = commute_ante(deduce(j, k1))(eq_flip(d))
    k4 = k[X, x * (y * z.S())][Y, (x * (y * z)) + (x * y)][Z, (x * y) * z.S()](h)
    k5 = deduce(k2, k4)
    return i(k5)


mul_assoc = mul_assoc()


class Direction(Enum):
    LEFT = -1
    CHILD = 0
    RIGHT = 1


LEFT = Direction.LEFT
RIGHT = Direction.RIGHT
CHILD = Direction.CHILD


def split(p: Phrase, var: Phrase, path: list[Direction]) -> tuple[Phrase, Phrase]:
    if not path:
        return var, p
    direction = path[0]
    if direction == Direction.CHILD:
        if p.kind not in ARITY_1:
            raise ValueError(f"split: expected unary operator at {p}, got {p.kind}")
        child = p.child()
        new_phrase, removed = split(child, var, path[1:])
        new_phrase = make_phrase(p.kind, [new_phrase])
        return new_phrase, removed
    if p.kind not in ARITY_2:
        raise ValueError(f"split: expected binary operator at {p}, got {p.kind}")
    left = p.left()
    right = p.right()
    if direction == Direction.LEFT:
        new_p, removed = split(left, var, path[1:])
        new_phrase = make_phrase(p.kind, [new_p, right])
        return new_phrase, removed
    if direction == Direction.RIGHT:
        new_p, removed = split(right, var, path[1:])
        new_phrase = make_phrase(p.kind, [left, new_p])
        return new_phrase, removed
    raise ValueError(f"split: unknown direction {direction}")


def replace(p: Phrase, term: Phrase, path: list[Direction]) -> Phrase:
    v1 = var("REPLACE_VAR_1")
    v2 = var("REPLACE_VAR_2")
    new_phrase, old_term = split(p, v1, path)
    return eq_subs(v1, v2, new_phrase)[v1, old_term][v2, term].mp().mp()


def twice_x() -> Phrase:
    a = ((X + Y) * Z == (X * Z) + (Y * Z))[X, one][Y, one][Z, x]
    b, c = split(a, X, [LEFT, LEFT])
    d = eq_subs(X, Y, b)[X, one + one][Y, two].mp().mp()
    e, _ = split(d, X, [RIGHT, LEFT])
    f = eq_subs(X, Y, e)[X, one * x][Y, x].mp().mp()
    g, _ = split(f, X, [RIGHT, RIGHT])
    h = eq_subs(X, Y, g)[X, one * x][Y, x].mp().mp()
    return h[x, X]


twice_x()
assert (two * x == x + x).is_known_truth


def x_plus_y_squared() -> Phrase:
    a = ((X + Y) * Z == (X * Z) + (Y * Z))[X, x][Y, y][Z, x + y]
    b = (Z * (X + Y) == (Z * X) + (Z * Y))[X, x][Y, y][Z, x]
    c = (Z * (X + Y) == (Z * X) + (Z * Y))[X, x][Y, y][Z, y]
    (X * Y == Y * X)[X, y][Y, x]
    c2 = replace(c, x * y, [RIGHT, LEFT])
    a2 = replace(a, c2.right(), [RIGHT, RIGHT])
    a3 = replace(a2, b.right(), [RIGHT, LEFT])
    a4 = ((X + Y) + Z == X + (Y + Z))[X, x * x][Y, x * y][Z, x * y + y * y]
    a5 = eq_chain(a3, a4)
    a6 = (X + (Y + Z) == (X + Y) + Z)[X, x * y][Y, x * y][Z, y * y]
    a7 = replace(a5, a6.right(), [RIGHT, RIGHT])
    eq_flip(two * X == X + X)[X, x * y]
    a8 = replace(a7, two * (x * y), [RIGHT, RIGHT, LEFT])
    return a8[x, X][y, Y]


x_plus_y_squared()
assert ((X + Y) * (X + Y) == (X * X) + ((two * (X * Y)) + (Y * Y))).is_known_truth


def _recontrapose() -> Phrase:
    s = chain[x, X][y, Y][z, Z][X, ~~x][Y, x][Z, y].mp()
    (x >> ~~x)[x, y]
    a = chain[x, X][y, Y][z, Z][X, ~~x][Y, y][Z, ~~y]
    q = commute_ante(a).mp()
    r = chain[x, X][y, Y][z, Z][X, s.left()][Y, s.right()][Z, q.right()].mp().mp()
    t = contra[A, ~x][B, ~y]
    g = deduce(r, t)
    return g[x, X][y, Y]


recontrapose = _recontrapose()
assert ((X >> Y) >> (~Y >> ~X)).is_known_truth

x_is_odd = (~(x == y + y)).forall(y)
x_is_even = ~x_is_odd


def _one_is_odd():
    P = ~(one == y + y)
    i = induction(P, y)
    a = peano1[x, zero()]
    print("a", a, a.is_known_truth)
    b = eq_flip(peano3[x, zero()])
    print("b", b, b.is_known_truth)
    d = replace(a, zero() + zero(), [CHILD, LEFT])
    print("d", d, d.is_known_truth)
    e = eq_symm[y, zero() + zero()][x, one]
    print("e", e, e.is_known_truth)
    f = recontrapose[Y, zero() + zero() == one][X, one == zero() + zero()].mp().mp()
    print("f", f, f.is_known_truth)
    step = i.mp()

    g = eq_flip(peano4[x, X][X, y.S()])
    print("g", g, g.is_known_truth)
    h = peano2[x, X][y, Y][X, zero()][Y, y.S() + y]
    print("h", h, h.is_known_truth)
    h1 = replace(h, y.S() + y.S(), [LEFT, RIGHT])
    print("h1", h1, h1.is_known_truth)
    hh = (X + Y == Y + X)[X, y.S()][Y, y]
    print("hh", hh, hh.is_known_truth)
    h2 = replace(h1, y + y.S(), [RIGHT, RIGHT])
    print("h2", h2, h2.is_known_truth)
    peano4[x, y]
    h3 = replace(h2, (y + y).S(), [RIGHT, RIGHT])
    print("h3", h3, h3.is_known_truth)
    peano1[x, y + y]
    j = recontrapose[X, h3.left()][Y, h3.right()].mp().mp()
    print("j", j, j.is_known_truth)
    k = ignore[A, j][B, step.left().left()].mp()
    print("k", k, k.is_known_truth)

    print()
    print(step.mp().forall(y))

    return x_is_odd[x, one]


one_is_odd = _one_is_odd()
assert x_is_odd[x, one].is_known_truth

print(commute_antecedents)
print(impl_refl)
print(chain)
print(double_neg)
print(add_double_neg)
print(eq_symm)
print(eq_trans)
print(peano1)
print(peano2)
print(peano3)
print(peano4)
print(peano5)
print(peano6)
print(x_eq_y_impl_Sx_eq_Sy)
print(zero_plus_x_eq_x)
print(Sx_plus_y_eq_Sx_plus_y)
print(plus_comm)
print(zero_mul_x_eq_zero)
print(x_plus_one_eq_Sx)
print(one_mul_x_eq_x)
print(x_eq_y_impl_x_plus_z_eq_y_plus_z)
print(x_impl_y_eq_z_impl_x_impl_z_eq_y)
print(plus_assoc)
print(Sx_mul_y_eq_x_mul_y_plus_y)
print(mul_comm)
print(mul_distr)
print(mul_distr_left)
print(mul_assoc)
print(one_is_odd)

print("Total unique phrases created:", len(phrases))
print("Known truths among them:", sum(1 for p in phrases.values() if p.is_known_truth))
