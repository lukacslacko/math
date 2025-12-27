# Mathematics

A language for describing the truth.

## Language

The programs are executed top to bottom. There is a global list of *proven phrases*, to which each proven phrase gets appended as the program goes. Any proven phrase can be used anywhere later to prove new phrases.

There are [inference rules](#inference-rules) which can add *proven phrases* from already proven phrases.

There is a set of [axioms](#axioms) added to the *proven phrases* list by the runtime before starting the program.

There are also [axiom schemas](#axiom-schemas) which can be instantiated to add an instance to the *proven phrases*.

Also, `0` is added as an identifier to the global namespace.

[Functions](#functions) can be used to conveniently apply repeated steps.

Comments can be added between `/* ... */`.

### Formatting

To format a file, run `cargo run --bin formatter filename.ll`, or press `Ctrl+Shift+B` in VSCode and select "Format Logic Language" when editing a program.

To convert to the ASCII representation, run `cargo run --bin asciify filename.ll` or run the "ASCIIfy Logic Language" in VSCode.

## Expressions

| Expression | Syntax | ASCII | Remarks |
| -- | -- | -- | -- |
| Logical variable | `'name` | | Identifiers starting with `'` are logical variables |
| Numeric variable | `name` | | Must not start with `'` |
| Assignment | `identifier ≔ value` | `:=` | Anything can be an identifier |
| Substitution | `P[x / term]` | | Substitutes `x` with `term` in `P`. **TODO** condition on free variables of `term`. Note: if `P` is proven, this is the "Substitution" inference rule below. |
| Universal quantification | `∀x P` | `!x P` | Variable must be numeric. Note if `P` is a *proven phrase* then this is the "Universal generalization" inference rule below. |
| Parentheses | `(phrase)` | | Any numeric or logical phrase can be parenthesized to express order of operations. Note: multiple phrases can be parenthesized, in which case the value of the parentheses is the last one. |
| Empty parentheses | `()` | | These are ignored |
| Namespaces | `{ ... }` | | Forget all identifiers (except `0`) within the namespace. The value of a namespace is its last phrase. |
| Function definition | `name ≔ λ{ ... }` | `name := lambda { ... }` | Assigns a function to a name. The current contents of the namespace are saved with the function |
| Function argument | `●` | `<arg>` | The value of the argument of the function, can be a list or a phrase |
| Function call | `argument.name` or `argument\|name` | | The function is called on the argument. `\|` binds weakly, `.` binds strongly |
| Function return | `↵ result` | `return result` | If present, the function results with the given value, otherwise it does not return anything |
| Left part | `a↙` | `a.<` | The left part of a degree-two node in the syntax tree, eg `(A ⇒ B)↙` is `A` or `(∀x A)↙` is `x`. For lists, it returns the head of the list. |
| Right part | `a↘` | `a.>` | The right part of a degree-two node in the syntax tree, eg `(A ⇒ B)↘` is `B` or `(∀x A)↘` is `A`. For lists, it returns the tail of the list. |
| Child | `a↓` | `a.v` | The child of a degree-one node in the syntax tree, eg `(¬A)↓` is `A` |
| Cut | `phrase; var; path \| ✂` | `phrase; var; path \| <cut>` | The path must be a sequence of `↙`, `↘`, `↓`. The operation follows the `path` in the `phrase`'s syntax tree, removes the subtree there and replaces it with `var`. It returns a list with `new_phrase; removed_subtree` |
| List element | `aⅰ`, `aⅱ`, `aⅲ`, ... | `a<1>`, `a<2>`, `a<3>`, ... | Abbreviation for `a↙`, `a↘↙`, `a↘↘↙`, ... for the *n*th element of a list |
| Negation | `¬A` | `~A` | `A` must be a logic phrase |
| Equality | `x = y` | | `x` and `y` must be numeric phrases |
| Implication | `A ⇒ B` | `A -> B` `A => B` | `A` and `B` must be logic phrases |
| List | `x; y` | | Lists contain a finite number of elements. They can be used for providing arguments to [axiom schemas](#axiom-schemas) or be assigned to identifiers and used with ↙ and ↘ |
| Assertion | `⊦ P` | `\|- P` | Asserts that `P` is a *proven phrase*. Panics if not. `P` must be a logic phrase |
| Print | `P ℻` | `P FAX` | Prints out the phrase `P` |
| Stop | `⛔` | `<stop>` | Stops the program |
| Import identifier | `⤷ name` | `import name` | Imports the name and value of `name` from the surrounding namespace into the current one |
| Export identifier | `⤶ name` | `export name` | Exports the name and value of `name` into the surrounding namespace. For namespaces with a single result, `result ≔ { ... result }` is an alternative to this |
| Successor | `𝗦(x)` | `<S>(x)` | The successor of `x`. `x` must be a numeric phrase |
| Addition | `x + y` | | The sum of `x` and `y`. `x` and `y` must be numeric phrases |
| Multiplication | `x * y` | | The product of `x` and `y`. `x` and `y` must be numeric phrases |

## Inference rules
| Rule | Syntax | ASCII | Remarks |
| -- | -- | -- | -- |
| Substitution | `phrase[var / term]` | | `phrase` must be a *proven phrase*, `var` must be a numeric or logical variable and `term` must be a phrase of the same kind. **TODO** condition on free variables of `term`. Note: if `phrase` is not proven, this is still a valid expression. |
| Modus ponens | `phrase.MP` | | `phrase` must be of the shape `A ⇒ B` and `A` must be a *proven phrase*, the result is `B` |
| Universal generalization | `∀x P` | `!x P` | If `P` is a *proven phrase*, this becomes a *proven phrase* as well. Note: if `P` is not proven, this is still a valid expression |

## Axioms

`X` and `Y` are numeric variables, `0` is a numeric constant.

| Name | Axiom |
| -- | -- |
| Peano 1 | `¬0 = 𝗦(X)` |
| Peano 2 | `𝗦(X) = 𝗦(Y) ⇒ X = Y` |
| Peano 3 | `X + 0 = X` |
| Peano 4 | `X + 𝗦(Y) = 𝗦(X + Y)` |
| Peano 5 | `X * 0 = 0` |
| Peano 6 | `X * 𝗦(Y) = (X * Y) + X` |
| Reflexivity of equality | `X = X` |

## Axiom schemas

| Axiom schema | Syntax | ASCII | Remarks |
| -- | -- | -- | -- |
| Indiscernibility of identicals | `P; x; y \| ⪮` | `P; x; y \| <eq_subs>` |  `x = y ⇒ P ⇒ P[x / y]` |
| Distribution of quantification | `P ⇆` | `P <distribute>` | `P` must be of the shape `∀x A ⇒ B`, the resulting axiom is `(∀x A ⇒ B) ⇒ (∀x A) ⇒ ∀x B` |
| Instantiation | `phrase[term]` | | `phrase` must be of the shape `∀x P`, the resulting axiom is `(∀x P) ⇒ P[x / term]` |
| Induction | `P; x \| ↺` | `P; x \| <induction>` | `P` must be a logic phrase and `x` must be a numeric variable, the resulting axiom is `P[x / 0] ⇒ (∀x P ⇒ P[x / 𝗦(x)]) ⇒ ∀x P` |

## Functions

Functions are stored in the current namespace as a token stream assigned to a name, along with a saved namespace, containing a snapshot of the current namespace. This means function bodies don't need to bother with importing identifiers.

Functions receive one argument, either a phrase or a list and may return zero or one results.

Function calls are written as `argument.function` or `argument|function`. `.` binds strongly while `|` binds weakly.
