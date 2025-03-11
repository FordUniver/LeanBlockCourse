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

#check And.intro -- arguments are `(a : Prop)` and `(b : Prop)` and output is `(a ∧ b : Prop)`
-- this has two arguments so using `apply` on it will open up two goals (one for `a` and `b`)

-- Most explicit way using apply
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  apply And.intro
  · exact p
  · exact q

-- Using constructor
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  · exact p
  · exact q

-- Using angle bracket notation, i.e., `⟨p, q⟩` is notation for `And.intro p q`
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact ⟨p, q⟩

-- We can again stack proofs inside proofs 
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact ⟨by assumption, by assumption⟩ 

-- Or just use term mode
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

-- Though even there we can stack proofs 
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, by assumption⟩


/-
## Working with AND in a hypothesis

To use a hypothesis `h : P ∧ Q`, we can:

- Access components with `h.1` / `h.2` or `h.left` / `h.right`
- Use `obtain` for destructuring
- Use `cases` and `rcases` for basic pattern matching

`obtain` is used around 11,000 times in mathlib, `cases` 4000 times,
and `rcases` 7000 times.
-/

-- Using `.1` / `.2` notation
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1

-- Using `.right` / `.left` notation
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.right
  · exact h.left

  -- Term mode proof
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := And.intro h.2 h.1

-- Using `obtain` for destructuring
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨p, q⟩ := h   -- have would also work but would keep the `h` around
  exact ⟨q, p⟩

-- Splitting h up using `cases`
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor
  · assumption
  · assumption

-- Using pattern matching with `cases`
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro p q => exact ⟨q, p⟩

-- Though `rcases` provides a more pleasant syntax for this pattern
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨p, q⟩
  exact ⟨q, p⟩

-- `cases'` provides yet another syntax for destructuring
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases' h with p q
  exact ⟨q, p⟩

-- Note that introduction can be combined with pattern matching
example (P Q : Prop) : (P ∧ Q) → P := by
  intro h
  obtain ⟨p, _⟩ := h
  exact p

example (P Q : Prop) : (P ∧ Q) → P := by
  intro ⟨p, _⟩
  exact p

example (P Q : Prop) : (P ∧ Q) → P := fun ⟨p, _⟩ => p


/-
# Exercises
-/

-- Prove that if `P → Q` and `P → R`, then `P → (Q ∧ R)`.
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) := by
  sorry

-- Also give a term mode version of this
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) := sorry
