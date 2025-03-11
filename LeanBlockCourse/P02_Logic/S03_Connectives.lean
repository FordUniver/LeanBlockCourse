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
  intro p
  constructor
  · exact h₁ p
  · exact h₂ p

-- The dots and indentation are not necessary but structure the proof for readability
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) := by
  intro p
  constructor
  exact h₁ p
  exact h₂ p

-- Also give a term mode version of this
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) := fun p => ⟨h₁ p, h₂ p⟩

/-
## Intermezzo: The `repeat`, `all_goals`, `try`, and `<;>` tactics

- `repeat tac` repeatedly applies `tac` to the main goal until it fails.
- `all_goals tac` runs `tac` on each goal, concatenating the resulting goals, if any.
- `try tac` attempts to run `tac` without causing failure if it does not apply.
- `tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal.

They are respectively used around 150, 500, 400, and 7000 times in mathlib.
-/

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor
  repeat assumption

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor
  all_goals assumption

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor <;> assumption

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h; constructor <;> assumption -- you can in fact replace any line break with a semicolon

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  all_goals
  try exact h.1
  try exact h.2

/-
## Working with OR (∨) in the goal

To prove P ∨ Q, we need to prove either P or Q. We can:

- Use `apply Or.inl`/`Or.inr` explicitly
- Use `left`/`right` as shorthand
-/

-- Most explicit way using apply
example (P Q : Prop) (p : P) : P ∨ Q := by
  apply Or.inl
  exact p

-- Term mode for Or.inl
example (P Q : Prop) (p : P) : P ∨ Q := Or.inl p

-- Using left/right
example (P Q : Prop) (p : P) : P ∨ Q := by
  left
  exact p

/-
## Working with OR in a hypothesis

To use `h : P ∨ Q`, we can:
- Use `apply Or.elim` explicitly
- Use `cases` and `rcases`
- Use `obtain` with pattern matching
-/

-- Using `Or.elim` directly
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  apply Or.elim h
  · exact p_to_r
  · exact q_to_r

example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := 
  Or.elim h p_to_r q_to_r

example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  apply @Or.elim P Q R
  · exact h
  · exact p_to_r
  · exact q_to_r

-- Basic pattern matching with cases
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  cases h
  · exact p_to_r (by assumption)
  · exact q_to_r (by assumption)

-- Using cases with pattern matching notation
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  cases h with
  | inl p => exact p_to_r p
  | inr q => exact q_to_r q

-- Using `rcases` for OR
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  rcases h with p | q
  · exact p_to_r p
  · exact q_to_r q
  
-- Using `cases'` for OR
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  cases' h with p q
  · exact p_to_r p
  · exact q_to_r q

-- Using obtain for OR
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  obtain p | q := h
  · exact p_to_r p
  · exact q_to_r q

/-
## Working with nested structures

For more complex structures, we can:
- Use `rcases` for deep pattern matching
- Use `obtain` with nested patterns
-/

-- Nested cases
example (P Q R : Prop) (h : P ∧ (Q ∧ R)) : Q := by
  cases h with
  | intro p qr => 
    cases qr with
    | intro q r => exact q

example (P Q R : Prop) (h : P ∧ (Q ∧ R)) : Q := h.right.left

-- Using obtain with nested patterns
example (P Q R : Prop) (h : P ∧ Q ∧ R) : Q := by
  obtain ⟨p, ⟨q, r⟩⟩ := h  -- ⟨p, q, r⟩ would also work here
  exact q

example (P Q R : Prop) (h : (P ∧ Q) ∧ R) : Q := by
  obtain ⟨⟨p, q⟩, r⟩ := h  -- ⟨p, q, r⟩ would NOT work here
  exact q

-- Using rcases
example (P Q R : Prop) (h : (P ∧ Q) ∧ R) : Q := by
  rcases h with ⟨⟨_, q⟩, _⟩
  exact q




/-
## The `rintro` tactic

`rintro` allows for more complex pattern matching and is
used around 7500 times in mathlib.
-/

example (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R := by
  intro h
  rcases h with ⟨p, _⟩ | r
  · left; exact p
  · right; exact r

example (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R := by
  rintro (⟨p, _⟩ | r)
  · left; exact p
  · right; exact r

example (P Q R : Prop) : (P ∧ (Q ∨ R)) → (P ∧ Q) ∨ (P ∧ R) := by
  rintro ⟨p, q | r⟩
  · left; exact ⟨p, q⟩
  · right; exact ⟨p, r⟩

/-
# Exercise

Hint: try `rintro` with nested structures
-/

example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  intro pqrs
  obtain ⟨pq, rs⟩ := pqrs
  cases' pq with p q
  · cases' rs with r s
    · left; exact ⟨p, r⟩ 
    · right; left; exact ⟨p, s⟩
  · cases' rs with r s
    · right; right; left; exact ⟨q, r⟩
    · right; right; right; exact ⟨q, s⟩

example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  intro ⟨pq, rs⟩
  cases' pq with p q
  all_goals cases' rs with r s
  · left; exact ⟨p, r⟩ 
  · right; left; exact ⟨p, s⟩
  · right; right; left; exact ⟨q, r⟩
  · right; right; right; exact ⟨q, s⟩

example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  rintro ⟨p | q, r | s⟩
  · exact Or.inl ⟨p, r⟩
  · exact Or.inr <| Or.inl ⟨p, s⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨q, r⟩
  · exact Or.inr <| Or.inr <| Or.inr ⟨q, s⟩

example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  rintro ⟨p | q, r | s⟩
  all_goals simp_all -- we will learn about this technique later 

example (P Q R S : Prop) : ((P ∧ Q) ∨ R) ∧ S → (P ∨ R) ∧ (Q ∨ R) ∧ S := by
  rintro ⟨⟨p, q⟩ | r, s⟩
  · constructor
    · left; exact p
    · constructor
      · left; exact q
      · exact s
  · exact ⟨Or.inr r, Or.inr r, s⟩ 

/-
## Working with Equivalence (↔) in the goal

To prove `P ↔ Q`, we need to prove both `P → Q` and `Q → P`. We can:

- Use `apply Iff.intro` explicitly
- Use `constructor` as shorthand
- Use angle bracket notation with two lambda expressions
-/

-- Explicit proof using Iff.intro
example (P Q : Prop) (p_to_q : P → Q) (q_to_p : Q → P) : P ↔ Q := by
  apply Iff.intro
  · exact p_to_q
  · exact q_to_p

-- Using constructor
example (P Q : Prop) (p_to_q : P → Q) (q_to_p : Q → P) : P ↔ Q := by
  constructor
  · exact p_to_q
  · exact q_to_p

-- Angle bracket notation for term mode
example (P Q : Prop) (p_to_q : P → Q) (q_to_p : Q → P) : P ↔ Q :=
  Iff.intro p_to_q q_to_p

example (P Q : Prop) (p_to_q : P → Q) (q_to_p : Q → P) : P ↔ Q :=
  ⟨p_to_q, q_to_p⟩


/-
## Using Equivalence in hypotheses

To use `h : P ↔ Q`, we can:
- Access forward/backward directions with `h.mp` / `h.mpr`
- Use `rw` to rewrite equivalents
- Destructure with `obtain` or `cases`
-/

-- Using `.mp` (modus ponens) and `.mpr` (reverse)
example (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by
  exact h.mp p

example (P Q : Prop) (h : P ↔ Q) (q : Q) : P := by
  exact h.mpr q

-- In term mode this just looks like
example (P Q : Prop) (h : P ↔ Q) (p : P) : Q := h.mp p
example (P Q : Prop) (h : P ↔ Q) (q : Q) : P := h.mpr q

-- Alternatively we can use `1` and `2` to access the components
example (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by
  exact h.1 p

example (P Q : Prop) (h : P ↔ Q) (q : Q) : P := by
  exact h.2 q

-- As already noted previously, we can rewrite with equivalences
example (P Q R : Prop) (h : P ↔ Q) (q_to_r : Q → R) : P → R := by
  rw [h]
  exact q_to_r

-- We can also destructure equivalences using `obtain`
example (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by
  obtain ⟨p_to_q, _⟩ := h
  exact p_to_q p

-- `cases` and `rcases` can also destructure equivalences
example (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by
  rcases h with ⟨p_to_q, _⟩
  exact p_to_q p

example (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by
  cases h with
  | intro mp mpr => exact mp p

/-
## The `trans` tactic

The `trans` tactic allows us to chain together equivalences (or equalities) by introducing an intermediate statement.
In the following example, we prove that `B ↔ C` by chaining three equivalences:

- From `A ↔ B` we get `B ↔ A` by symmetry,
- Then we use `A ↔ D`,
- And finally, from `C ↔ D` we get `D ↔ C` by symmetry.

This lets us conclude `B ↔ C`. It is used around 400 times in mathlib.
-/

example (A B C D : Prop)
  (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  trans A
  · exact h₂.symm
  · clear h₂
    trans D
    · exact h₃
    · exact h₁.symm 

example (A B C D : Prop)
  (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  rw [h₁, h₃.symm, h₂]

/-
## The Following Are Equivalent (TFAE)

The `TFAE` tactic is used to state that all propositions in a list are equivalent.
This is useful when you have multiple propositions that are logically equivalent
and you want to prove their equivalence in a structured way.

Key tactics:
- `tfae_have` to introduce equivalences between propositions
- `tfae_finish` to conclude the proof of equivalence

It is used around 300 times in mathlib.
-/

example (P₁ P₂ P₃ : Prop) (h₁ : P₁ → P₂) (h₂ : P₂ → P₃) (h₃ : P₃ → P₁) : [P₁, P₂, P₃].TFAE := by
  tfae_have 1 → 2 := by
    intro h
    exact h₁ h
  tfae_have 2 → 3 := fun h => h₂ h
  tfae_have 3 → 1 := fun h => h₃ h
  tfae_finish


/-
# Exercises
-/

-- Prove the associativity of disjunction: `(P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R)`.
example (P Q R : Prop) : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by sorry

-- Prove that `OR` distributes over `AND` in both directions.
example (P Q R : Prop) : (P ∧ Q) ∨ R ↔ (P ∨ R) ∧ (Q ∨ R) := by sorry
