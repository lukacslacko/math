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


def forall_permute(forall_phrase: Phrase) -> Phrase:
    if forall_phrase.kind != Kind.FORALL:
        raise ValueError(
            f"forall_permute: argument must be a universal quantification {forall_phrase}"
        )
    inner = forall_phrase.right()
    if inner.kind != Kind.IMPL:
        raise ValueError(f"forall_permute: inner must be an implication {inner}")
    var = forall_phrase.left()
    A = inner.left()
    B = inner.right()
    if var.varname() in A.free:
        raise ValueError(
            f"forall_permute: variable {var} occurs free in antecedent {A}"
        )
    return (forall_phrase >> (A >> forall_phrase.right().forall(var))).axiom()


A = var("A")
B = var("B")
C = var("C")
x = var("x")
y = var("y")
z = var("z")
X = var("X")
Y = var("Y")
Z = var("Z")

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

print("Total unique phrases created:", len(phrases))
print("Known truths among them:", sum(1 for p in phrases.values() if p.is_known_truth))
