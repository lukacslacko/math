# Mathematics

A language for describing the truth.

## Language

The programs are executed top to bottom. There is a global list of *proven phrases*, to which each proven phrase gets appended as the program goes. Any proven phrase can be used anywhere later to prove new phrases.

There are [inference rules](#inference-rules) which can add *proven phrases* from already proven phrases.

There is a set of [axioms](#axioms) added to the *proven phrases* list by the runtime before starting the program.

There are also [axiom schemas](#axiom-schemas) which can be instantiated to add an instance to the *proven phrases*.

Also, `0` is added as an identifier to the global namespace.

| Expression | Syntax | ASCII | Remarks |
| -- | -- | -- | -- |
| Logical variable | `'name` | | Identifiers starting with `'` are logical variables |
| Numeric variable | `name` | | Must not start with `'` |
| Assignment | `identifier ≔ value` | `:=` | Anything can be an identifier |
| Universal quantification | `∀x P` | `!` | Variable must be numeric |
| Parentheses | `(phrase)` | | Any numeric or logical phrase can be parenthesized to express order of operations. Note: multiple phrases can be parenthesized, in which case the value of the parentheses is the last one. |
| Empty parentheses | `()` | | These are ignored |
| Namespaces | `{ ... }` | | Forget all identifiers within the namespace. The value of a namespace is its last phrase. |

## Inference rules
| Rule | Syntax | ASCII | Remarks |
| -- | -- | -- | -- |
| Substitution | `phrase[var / term]` | | `var` must be a numeric or logical variable and `term` must be a phrase of the same kind. **TODO** condition on free variables of `term`. |
| Instantiation | `quantified_phrase[term]` | | `quantified_phrase` must be of the shape `∀x P` and the result is `P[x / term]` |

## Axioms

## Axiom schemas

| Axiom schema | Syntax | ASCII | Remarks |
| -- | -- | -- | -- |
| Indiscernibility of identicals | `P; x; y \| substitute_equals` | |  `x = y ⇒ P ⇒ P[x / y]` |