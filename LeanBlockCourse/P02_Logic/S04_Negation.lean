/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic

/-
# Negation and Classical Logic
=====================

This module builds on previous logical foundations to explore:

- Working with negation (`¬`) and contradiction
- Classical reasoning with `by_contra`
- Simplifying negations using `push_neg`
- Handling contradictions with `exfalso` and `contradiction`
-/

/-
## Understanding Negation

In Lean, `¬P` is defined as `P → False`. This perspective allows us to:

- Treat negations as implication arrows to `False`
- Use implication-handling tactics with negations
-/

-- Basic negation example showing definitional equivalence
example (P : Prop) : ¬P ↔ (P → False) := by
  rfl


-- Using negation in hypotheses requires handling implied contradictions
example (P Q : Prop) (h : P → ¬Q) (p : P) (q : Q) : False := by
  have := h p
  exact this q


/-
## The`contradiction` Tactics

The `contradiction` tactic automatically closes goals with:

- Direct `False` hypotheses
- Obviously conflicting assumptions
- Mismatched constructors in inductive types

It is used around 400 times in mathlib.
-/


-- Simple contradiction with False hypothesis
example (P : Prop) (h : False) : P := by
  contradiction  -- Automatically detects the False

example (P Q : Prop) (h : P) (hn : ¬P) : Q := by
  contradiction  -- Automatically detects the contradiction

-- Contradiction version
example (n : ℕ) (h : n ≠ n) : n = 37 := by
  contradiction  -- Automatically finds the contradiction

-- contradiction version
example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  contradiction


/-
# The `exfalso` tactic

The `exfalso` tactic converts any goal to `False`, allowing you to:

- Work explicitly with contradictions
- Use any false assumption to prove arbitrary claims
- Combine with other tactics for manual contradiction handling

It is used around 200 times in mathlib.
-/

-- exfalso allows proving anything from false assumptions
example (P : Prop) (h : False) : P := by
  exfalso    -- Changes goal to False
  exact h    -- Uses the False hypothesis

-- Contradiction from self-inequality
example (n : ℕ) (h : n ≠ n) : n = 37 := by
  exfalso        -- Explicitly work with False
  have : False :=  h rfl
  exact this    -- n ≠ n contradicts n = n from rfl

-- Contradiction from conflicting equalities
example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  exfalso        -- Manual mode
  exact g h
