/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.NthRewrite

/-
# Fundamentals of Lean Proofs
=====================

This module introduces the most basic building blocks for constructing proofs in Lean:
- Proving equalities with `rfl`
- Using hypotheses with `assumption`
- Precise matching with `exact`
- Basic implications (`→`) and the `intro` tactic
- Rewriting with `rw`


## Proofs by reflexivity - the `rfl` tactic

The `rfl` tactic proves goals that are true by definition
and is (explicitely) used around 4000 times in mathlib and many
times more implicitly through `rw`, `exact`, `simp`, ...
-/

-- Simple equality: proves that 42 equals itself
example : 42 = 42 := by
  rfl

example : (42 = 42 : Prop) := by
  rfl

-- Works with variables: proves that any proposition equals itself
example (P : Prop) : P = P := by
  rfl

-- Works with logical equivalence: proves that any proposition is equivalent to itself
example (P : Prop) : P ↔ P := by
  rfl

-- Works with definitional equality: proves that 2 + 2 is 4 *by definition*
-- Why is this true? Because 4 = 0.succ.succ.succ.succ, 2 = 0.succ.succ
-- and a + b.succ = (a + b).succ, so unrevaling everything, both sides reduce to
-- 0.succ.succ.succ.succ, which is four!
example : 2 + 2 = 4 := by
  rfl
  
-- Even works with type-level equality.
-- We will explore types in more detail later.
example (α : Type) : α = α := by
  rfl


/-
## Using hypotheses - the `assumption` tactic

The `assumption` tactic looks through the available hypotheses and tries to find one
that exactly matches the goal. This is useful when you already have exactly what you
need to prove in your context. This tactic is essentially unused in mathlib.
We will learn in a bit why.
-/

-- Given a natural number `n` where `10 > n` and `1 < n`, prove that `1 < n`
example (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) : 1 < n := by
  assumption

-- Given proposition `P` and its proof, prove `P`
example (P : Prop) (p : P) : P := by
  assumption

-- Given propositions `P` and `Q`, and proofs of both, prove `P`
example (P Q : Prop) (p : P) (q : Q) : P := by
  assumption


/-
## Precise matching - the `exact` tactic

The `exact` tactic allows us to provide a term that precisely matches the goal type.
Unlike assumption, which searches for matches, exact requires us to specify exactly
which term we want to use, but otherwise has the same effect. The `rfl` tactic in fact
was just syntax sugar for `exact rfl`. The tactic `exact?` looks for any term that can be
used to close the goal. This tactic is used over 40,000 times in mathlib.
-/

-- Given a natural number `n` where `10 > n` and `1 < n`, prove that `1 < n`
example (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) : 1 < n := by
  exact h₂ -- suggested by exact?

-- Given proposition `P` and its proof, prove `P`
example (P : Prop) (p : P) : P := by
  exact p

-- Given propositions `P` and `Q`, and proofs of both, prove `P`
example (P Q : Prop) (p : P) (q : Q) : P := by
  exact p


/-
## Exercises
-/

example : 3 + 2 = 5 := by
  rfl

example (M : Prop) (m : M) : M := by
  exact m


/-
## Basic implications

An implication `P → Q` can be proved by assuming `P` and proving `Q`.
-/

-- `P → Q` means that `P` implies `Q`
example (P Q : Prop) (h : P → Q) : P → Q := by
  exact h 

example (P Q : Prop) (h : P → Q) : P → Q := by
  assumption

-- this is called term mode (more on this later)
example (P Q : Prop) (h : P → Q) : P → Q := h

-- Given a function `h : P → Q` and a proof of `P`, we get a proof of `Q`
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  exact h p 

-- We can compose `P → Q` and `Q → R` to get from `P` to `R`  
example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : R := by
  exact h₂ (h₁ p)

-- bit unusual ..
example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : R := by
  exact (h₂ ∘ h₁) p

-- The `<|` operator is a function application operator that binds less tightly than function application.
-- It allows us to avoid parentheses by applying functions from right to left.
-- So `h₂ <| h₁ p` is equivalent to `h₂ (h₁ p)` but can be easier to read with nested applications.
-- The dollar sign `$` is a synonym for this operator.
example (P Q R : Prop) (p : P) (h₁ : P → Q) (h₂ : Q → R) : R := by
  exact h₂ <| h₁ p


/-
## The `intro` tactic

The `intro` tactic is used to prove implications (`→`) by assuming the antecedent.
When proving `P → Q`, `intro p` creates a hypothesis `p : P` and changes the goal to `Q`.
It is used around 12,000 times in mathlib.
-/

-- The identity function: shows that any proposition implies itself
example (P : Prop) : P → P := by
  intro p
  exact p

-- This is actually (essentially) the same as
example (P : Prop) (p : P) : P := p

-- Note that `ìd` is one instanciation of P → P (regardless of the type of P)
example (P : Prop) : P → P := by
  exact id


/-
## Exercises
-/

-- Function composition: shows how to combine P → Q and Q → R to create P → R
-- Solve this two different ways!
example (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  sorry

-- Shows how to chain three implications together: if we can go from
-- `P` to `Q` to `R` to `S`, then we can go from `P` to `S`
example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S := by
  sorry

-- Shows how to work with nested implications: if `P` implies `(Q → R)`,
-- and `P` implies `Q`, then `P` implies `R`
example (P Q R : Prop) (h₁ : P → Q → R) (h₂ : P → Q) : P → R := by
  sorry
