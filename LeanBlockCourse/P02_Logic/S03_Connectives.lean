/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.TFAE
import Mathlib.Logic.Basic

/-
# Logical Connectives
=====================

This module introduces how to work with compound propositions:
- Conjunction (`AND`, `∧`)
- Disjunction (`OR`, `∨`)
- Equivalence (`↔`)

Key tactics:
- `constructor` for splitting compound goals
- `cases` and `rcases` for basic pattern matching
- `obtain` for destructuring hypotheses
- `trans` for chaining equivalences
- `tfae` for working with lists of equivalences
-/

/-
## Working with AND (∧) in the goal

To prove `P ∧ Q`, we need to prove both `P` and `Q`. We can:
- Use `apply And.intro` explicitly
- Use `constructor` as shorthand
- Use angle bracket notation `⟨p, q⟩`

`constructor` is used around 1000 times in mathlib while
`exact` followed by an `⟨⬝⟩` term is used around 5000 times.
-/


-- Most explicit way using apply
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by sorry
