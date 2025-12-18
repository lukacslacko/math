from dataclasses import dataclass
from enum import Enum


class Kind(Enum):
    VAR = "var"
    IMPL = "->"
    NEG = "~"


@dataclass
class Phrase:
    free: set[str]
    kind: Kind
    children: list["Phrase"]
    is_known_truth: bool = False

    def __str__(self) -> str:
        if self.kind == Kind.VAR:
            return next(iter(self.free))
        elif self.kind == Kind.IMPL:
            return f"({self.children[0]} -> {self.children[1]})"
        elif self.kind == Kind.NEG:
            return f"~{self.children[0]}"
        else:
            raise ValueError(f"Unknown kind {self.kind}")

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

    def __call__(self, p_phrase: "Phrase") -> "Phrase":
        return mp(self, p_phrase)

    def __invert__(self) -> "Phrase":
        return neg(self)

    def right(self) -> "Phrase":
        if self.kind != Kind.IMPL:
            raise ValueError("right() can only be called on implications")
        return self.children[1]

    def left(self) -> "Phrase":
        if self.kind != Kind.IMPL:
            raise ValueError("left() can only be called on implications")
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
    return make_phrase(Kind.IMPL, [p, q])


def neg(p: Phrase) -> Phrase:
    return make_phrase(Kind.NEG, [p])


def var(name: str) -> Phrase:
    if name not in phrases:
        phrases[name] = Phrase(free={name}, kind=Kind.VAR, children=[])
    return phrases[name]


def subs(p: Phrase, x: Phrase, q: Phrase) -> Phrase:
    if x.kind != Kind.VAR:
        raise ValueError(f"subs: x must be a variable, got {x}")
    if p.kind == Kind.VAR:
        if p == x:
            return q
        else:
            return p
    else:
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

print(commute_antecedents)
print(impl_refl)
print(chain)
print(double_neg)
