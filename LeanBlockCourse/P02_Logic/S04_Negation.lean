/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NthRewrite

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



/-
## The `push_neg` Tactic (Classical logic)

Normalizes negated expressions by pushing negation inward:

- Converts `¬(P ∧ Q)` to `¬P ∨ ¬Q`
- Converts `¬(P → Q)` to `P ∧ ¬Q`
- Converts `¬¬P` to `P` (uses law of excluded middle: `P ∨ ¬P`)
- Simplifies nested negations
-/

example (P : Prop) : ¬¬P → P := by
  push_neg
  exact id

-- Simple example showing push_neg in action
example (P Q : Prop) : ¬(P ∧ Q) → (¬P ∨ ¬Q) := by
  intro h
  push_neg at h
  by_cases hP : P
  · right
    exact h hP
  · left
    assumption

-- Pushing negation through conjunction
example (P Q : Prop) : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'  -- Converts `¬(¬P ∨ ¬Q)` to `P ∧ Q`
    exact h h'
  · intro h hpq
    rcases h with np | nq
    · exact np hpq.1
    · exact nq hpq.2

-- Pushing negation through implication 
example (P Q : Prop) : ¬(P → Q) ↔ (P ∧ ¬Q) := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'  -- Converts `¬(P ∧ ¬Q)` to `¬P ∨ Q`
    apply h
    intro p
    have := h' p
    exact h' p
  · intro ⟨p, nq⟩ f
    exact nq (f p)


/-
## Exercises
-/


-- Prove double negation introduction: `P → ¬¬P`.
example (P : Prop) : P → ¬¬P := by
  intro p
  push_neg
  exact p

example (P : Prop) : P → ¬¬P := by
  intro p
  suffices ¬P → False by exact this -- remember that `¬¬P` is just `¬P → False`
  intro np 
  contradiction

example (P : Prop) : P → ¬¬P := by
  intro p np
  exact np p -- remember that `¬P` is just `P → False`

example (P : Prop) : P → ¬¬P := fun p np => np p


-- Prove that if `¬¬P` holds and `P → Q` holds, then `¬¬Q` holds.
example (P Q : Prop) (p : ¬¬P) (f : P → Q) : ¬¬Q := by
  push_neg -- applies to the goal
  push_neg at p -- applies to assumption `p`
  exact f p

example (P Q : Prop) (p : ¬¬P) (f : P → Q) : ¬¬Q := by
  push_neg at * -- applies it to all assumptions and the goal
  exact f p


-- Apply the associativity of or as well as and
example (P Q R : Prop) 
    (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  push_neg at *
  intro _ pq
  obtain ⟨p, q⟩ := pq
  exact h (by left; exact p) p q

example (P Q R : Prop) 
    (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  push_neg at *
  intro pqr ⟨p, q⟩
  have : P ∨ (Q ∨ R) := or_assoc.mp pqr -- we can find this with `exact?`
  exact h this p q 

example (P Q R : Prop) 
    (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rw [or_assoc, and_assoc]
  assumption


-- Proof this using `suffices`
example (P Q : Prop) (h : P → ¬ Q) (p : P) (q : Q) : False := by
  suffices ¬Q by contradiction
  exact h p

example (P Q : Prop) (h : P → ¬ Q) (p : P) (q : Q) : False := by
  have := h p
  have := this q
  exact this

example (P Q : Prop) (h : P → ¬ Q) (p : P) (q : Q) : False :=
  h p q -- `exact? directly gives us this term


/-
## Classical Reasoning with `by_contra`

Enables proof by contradiction in classical logic:

1. Assume the negation of the goal
2. Derive a contradiction
3. Conclude the original goal
-/

-- We already know that we can resolve this with `push_neg`
example (P : Prop) : ¬¬P → P := by
  push_neg
  exact id

-- But let's do a proof by contradiction
example (P : Prop) : ¬¬P → P := by
  intro nnp
  by_contra np
  contradiction

example (P : Prop) : ¬¬P → P := by
  intro nnp
  by_contra np
  exact nnp np


-- Direct application of by_contra with hypothesis derivation
example (P Q : Prop) (g : P → Q) (nq : ¬Q) : ¬P := by
  by_contra p
  have q : Q := g p
  contradiction

example (P Q : Prop) (g : P → Q) (nq : ¬Q) : ¬P := by
  by_contra p
  exact nq (g p)


-- Since ¬P is P → False, we can directly apply the implication
example (P Q : Prop) (g : P → Q) (nq : ¬Q) : ¬P := by
  -- suffices P → False by exact this
  intro p
  exact nq (g p)

example (P Q : Prop) (g : P → Q) (nq : ¬Q) : ¬P := fun p => nq (g p)



/-
## Classical Reasoning with `by_cases`

The `by_cases` tactic allows classical case analysis on any proposition:

- Splits the proof into two cases: one where the proposition is true, and one where it's false
- Particularly useful with excluded middle (`P ∨ ¬P`) in classical logic
- Often combined with `push_neg` for handling negations

This tactic is used around 1,200 times in mathlib.
-/


-- Basic usage: proving a simple disjunction
example (P : Prop) : P ∨ ¬P := by
  exact Classical.em P -- `Classical.em` is exact the law of the excluded middle

example (P : Prop) : P ∨ ¬P := by
  by_cases p : P
  · left; exact p
  · right; exact p 

-- `by_cases` just uses the law of excluded middle
example (P : Prop) : P ∨ ¬P := by
  have p_or_np := Classical.em P
  cases p_or_np with
  | inl p => left; exact p
  | inr np => right; exact np

example (P : Prop) : P ∨ ¬P := by
  rcases em P with (p | np)
  · left; exact p
  · right; exact np


-- Using case analysis with implications
example (P Q : Prop) : (P → Q) → (¬P → Q) → Q := by
  intro pq npq
  by_cases h : P
  · exact pq h
  · exact npq h

/-
## Exercises
-/


-- Prove contrapositive equivalence using multiple methods
example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro pq
    intro nq
    by_cases this : P
    · have q : Q := pq this
      exfalso
      exact nq q
    · exact this
  · intro nqnp
    intro p
    by_cases this : Q
    · exact this
    · have np : ¬P := nqnp this
      exfalso
      exact np p

example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro pq nq p
    exact nq (pq p)
  · intro nqnp p
    by_contra nq
    exact nqnp nq p

example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := not_imp_not.symm -- this result is already in mathlib as `not_imp_not`

-- Prove using case distinction on `P`
example (P Q : Prop) : (P → Q) → (¬P → Q) → Q := by
  intro pq npq
  by_cases this : P
  · exact pq this
  · exact npq this

-- Combine by_cases with push_neg for this classical tautology
example (P : Prop) : ¬(P ↔ ¬P) := by
  push_neg
  by_cases this : P
  · left; exact ⟨this, this⟩
  · right; exact ⟨this, this⟩ 

example (P : Prop) : ¬(P ↔ ¬P) := by
  push_neg
  by_cases this : P
  all_goals simp [this]

example (P : Prop) : ¬(P ↔ ¬P) := iff_not_self


/-
## Revisiting `rw` and `nth_rw`

In the following examples, we further explore rewriting tactics in Lean.
Each example shows a different approach to rewriting expressions involving double negation
(using the `not_not` lemma) to simplify our goals.
-/

-- Example 1: Automatically simplify the goal by pushing negations and finish by reflexivity.
example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  push_neg
  rfl     

-- Example 2: Use the `rw` tactic to explicitly rewrite all occurrences of double negation with `not_not`
example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  rw [not_not]
  rw [not_not]

-- Example 3: Use the `rw` tactic with more explicit arguments to control the rewrite order.
example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  rw [@not_not B]
  rw [@not_not C]

-- Example 4: Target specific occurrences with `nth_rewrite` to control the rewrite order.
example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  nth_rewrite 1 [not_not]
  nth_rewrite 2 [not_not]
  nth_rewrite 1 [not_not]
  rfl                    

-- Example 5: Use explicit type annotations with `nth_rewrite` for clarity on which lemma instance to use.
example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  nth_rewrite 2 [@not_not C]
  nth_rewrite 1 [@not_not B]
  nth_rewrite 1 [@not_not C]
  rfl
