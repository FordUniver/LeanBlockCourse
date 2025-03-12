/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Linarith

/-
# Quantifiers in Lean
=====================

This module introduces Lean's quantifiers:

- The **universal quantifier** (`∀`) appears naturally as function arguments.
- The **existential quantifier** (`∃`) asserts that some witness exists, and we can also express unique existence.
- The **order of quantifiers** is significant.
- We also introduce tactics for handling quantifiers:
  - `choose` to extract witness functions from existential hypotheses,
  - `use` to supply a witness for an existential goal,
  - `ext` for function (and set) extensionality.
-/


/- 
## Universal Quantification

We have already seen universal quantification (`∀`) as arguments to functions.
We can now make them explicit and use them in nested proofs.
-/

-- This is how we did it previously
example (P : Prop) : P → P := by
  intro p
  exact p

example (P : Prop) : P → P :=
  fun p => p

-- We also know this is (essentially) the same as
example : (P : Prop) → P → P := by
  intro P p
  exact p

example : (P : Prop) → P → P :=
  fun P p => p

-- We can express the same using the `∀` quantifier
example : ∀ (P : Prop), P → P := by
  intro P p
  exact p

example : ∀ (P : Prop), P → P :=
   fun P p => p



/- 
## Existential Quantifier and Unique Existence

The existential quantifier (`∃`) asserts the existence of a witness.
We also show how to extract such a witness using the `choose` tactic,
and how to supply one with the `use` tactic. `choose` is used around
800 times in mathlib and `use` around 4500 times.
-/

-- If the goal wants us to show the existence we can `use` a particular instance
example : ∃ n, n = 2 := by
  use 2

example (m : ℕ) (h : m = 2) : ∃ n, n = m := by
  use 2
  exact h.symm

-- From unique existence (`∃!`) we can deduce existence (`∃`):
example : ∀ (X : Type) (P : X → Prop),
  (∃! (x : X), P x) → ∃ (x : X), P x := by
  intro X P -- this takes care of the ∀ quantified statements
  intro h -- this takes care of the implication in the goal
  -- rcases h with ⟨x, h_existence, h_uniqueness⟩
  obtain ⟨x, h_existence, h_uniqueness⟩ := h
  use x 

-- Using the `choose` and `use` tactics:
example : ∀ (X : Type) (P : X → X → Prop),
  (∀ x : X, ∃ y : X, P x y) → ∃ (f : X → X), ∀ x : X, P x (f x) := by
  intro X P h
  choose f hf using h
  use f 


/- 
## Function and Set Extensionality

Two functions are equal if they return the same output for every input.
The `ext` tactic proves function extensionality, reducing a goal `f = g`
to proving `f x = g x` for arbitrary `x`. It is used around 7500 times in mathlib.
-/

-- Function extensionality: `f = g` if `∀ x, f x = g x`.
example (X Y : Type) (f g : X → Y) (h : ∀ x : X, f x = g x) : f = g := by
  ext x
  exact h x


/- 
## Exercises
-/

-- Prove that `∀ x, (p x ∧ q x) ↔ ((∀ x, p x) ∧ (∀ x, q x))`.
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) ↔ ((∀ x : α, p x) ∧ (∀ x : α, q x)) := by
  sorry

-- Prove that `∃ x, (p x ∨ q x) ↔ ((∃ x, p x) ∨ (∃ x, q x))`.
example (α : Type) (p q : α → Prop) : (∃ x : α, p x ∨ q x) ↔ ((∃ x : α, p x) ∨ (∃ x : α, q x)) := by
  sorry

-- Prove that `((∀ x, p x) ∨ (∀ x, q x)) → (∀ x, p x ∨ q x)`.
example (α : Type) (p q : α → Prop) : ((∀ x : α, p x) ∨ (∀ x : α, q x)) → (∀ x : α, p x ∨ q x) := by
  sorry

-- Use the `ext` tactic to prove the following:
example (X : Type) (A B : Set X) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := by
  sorry

-- Use the `use` tactic to prove the following:
example (X Y : Type) (P : X → Prop) (Q : Y → Prop)
  (h₁ : ∃ x, P x) (h₂ : ∃ y, Q y) : ∃ z : X × Y, P z.1 ∧ Q z.2 := by
  sorry

-- Use the `choose` tactic to prove the following:
example (X : Type) (R : X → X → Prop) (h : ∀ x, ∃ y, R x y) :
    ∃ f : X → X, ∀ x, R x (f x) := by
  sorry

-- Prove that `(∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)`.
example (α : Type) (P Q : α → Prop) : (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  sorry
