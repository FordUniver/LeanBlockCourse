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
-- Solve this(at least) two different ways!
example (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  exact g ∘ f 

example (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  intro p
  exact g (f p)

example (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  intro p
  exact g <| f p

example (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  intro p
  exact (g ∘ f) p

example (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  exact fun a ↦ g (f a) -- we'll understand this later ...

-- Shows how to chain three implications together: if we can go from
-- `P` to `Q` to `R` to `S`, then we can go from `P` to `S`
example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S := by
  intro p
  exact h₃ (h₂ (h₁ p))

example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S := by
  intro p
  exact h₃ <| h₂ <| h₁ p

-- Shows how to work with nested implications: if `P` implies `(Q → R)`,
-- and `P` implies `Q`, then `P` implies `R`
-- Note: P → Q → R is P → (Q → R)
example (P Q R : Prop) (h₁ : P → Q → R) (h₂ : P → Q) : P → R := by
  intro p
  exact (h₁ p) (h₂ p)
  
-- We will learn more about the `have` tactic later!
example (P Q R : Prop) (h₁ : P → Q → R) (h₂ : P → Q) : P → R := by
  intro p
  have q : Q := (h₂ p)
  have h₃ : Q → R := h₁ p
  exact h₃ q

example (P Q R : Prop) (h₁ : P → Q → R) (h₂ : P → Q) : P → R := by
  exact fun a ↦ h₁ a (h₂ a)

example (P Q R : Prop) (h₂ : Q → R) : P → (Q → R) := by
  intro _ -- the p : P we are introducing is actually not needed or used!
  exact h₂

example (P Q R S : Prop) (h₂ : Q → R) : S → P → Q → R := by
  intro _ _ -- we can introduce multiple at the same time!
  exact h₂ 


/-
## The `revert` tactic

The `revert` tactic moves a hypothesis from the context back into the goal, essentially
reversing the effect of `intro`. It  is used only around 350 times in mathlib.
-/

-- Note that `hA : A` s exactly the same as `a : A`. It's just a name!
example (A B : Prop) (hA : A) (h : A → B) : B := by
  exact h hA

example (A B : Prop) (hA : A) (h : A → B) : B := by
  revert hA
  exact h


/-
## The `rw` tactic

The `rw` tactic performs substitutions using equalities (`=`) or equivalences (`↔`).
It's one of the most fundamental tactics in Lean, allowing us to:

- Use hypotheses to rewrite goals
- Use hypotheses to rewrite other hypotheses using `at`

This tactic is used around 70,000 times in mathlib.
-/

-- Basic rewriting in the goal
example (P Q : Prop) (h : P ↔ Q) : P → Q := by
  rw [h]
  intro q
  exact q

-- Without rewriting
example (P Q : Prop) (h : P ↔ Q) : P → Q := by
  intro p
  exact h.mp p -- mp (modus ponens) is the P → Q direction of P ↔ Q

-- Rewriting in hypotheses with `at`
example (P Q : Prop) (h₁ : P ↔ Q) (p : P) : Q := by
  rw [h₁] at p
  exact p

-- Multiple rewrites
example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁,h₂] -- implicit rfl call

-- Works with equality of propositions too
example (P Q R : Prop) (h₁ : P = Q) (h₂ : Q = R) : P = R := by
  rw [h₁, h₂]




/-
## Reverse Rewriting and Symmetry

Sometimes the equality (or equivalence) provided in a hypothesis goes in the opposite direction
than the one you need in your goal. There are several ways to handle this:

1. **Using `rw [← h]`:**  
   The arrow `←` tells Lean to use the *reverse* of the given hypothesis `h`.  
   For example, if you have `h : Q = P` and your goal is `P = Q`, then `rw [← h]` reverses `h`.
   This syntax is used around 55,000 times in mathlib.

2. **Using `h.symm`:**  
   If `h` is an equality (or an equivalence with a symmetric property), then `h.symm` produces 
   its symmetric version. You can use this directly in the `rw` tactic. This syntax is used around
   13,000 times in mathlib.

3. **Using the `symm` tactic (`symm at h`):**  
   The `symm` tactic can update a hypothesis in-place to its symmetric version.  
   After doing `symm at h`, the hypothesis `h` will have its arguments swapped.
   This tactic is basically unused in mathlib.

Below are examples illustrating each approach.
-/

-- Example 1: Reverse rewriting using `rw [← h]`
example (P Q : Prop) (h : Q = P) : P = Q := by
  rw [← h]

-- Example 2: Using h.symm in rewriting
example (P Q : Prop) (h : Q = P) : P = Q := by
  rw [h.symm]  -- h.symm is the symmetric version of h, equivalent to using `rw [← h]`

-- Example 3: Using the symm tactic to update a hypothesis in place
example (P Q : Prop) (h : P = Q) : Q = P := by
  symm at h 
  exact h

/-
Note that we can use the `nth_rw` tactic for some more precise control
over which occurrence of a pattern to rewrite. This is particularly useful when:
- There are multiple matches in the goal or hypothesis
- You need to preserve some instances while changing others
- The default rewrite behavior modifies the wrong occurrence

This tactic is only used around 400 times in mathlib.
-/

example (P Q : Prop) (h₁ : Q = P) (pqr : P ∧ Q ∧ P) : P ∧ Q ∧ Q := by
  nth_rw 2 [h₁]
  exact pqr


/-
## Exercises
-/

-- Shows how to use rw to prove that if `P` and `Q` are equivalent, and `Q` and
-- `R` are equivalent, then `P` and `R` are equivalent (transitivity of `↔`)
example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁, h₂] -- implicit rfl call

example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [← h₂]
  exact h₁

example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [← h₁] at h₂
  exact h₂

-- Shows how to use rw to prove that if `P` and `Q` are equivalent, and `Q` and `R`
-- are equivalent, then `P` and `R` are equivalent (transitivity of `↔`)
example (P Q : Prop) (h : Q ↔ P) : P → Q := by
  rw [h]
  intro p
  exact p

example (P Q : Prop) (h : Q ↔ P) : P → Q := by
  intro p
  exact h.mpr p



/-
# Term Mode and Direct Construction

Lean proofs can be written directly as terms, without tactics. This gives us two distinct
styles of proving:

1. Tactic Mode (using `by`)
   - More interactive and easier to write
   - More flexible and maintainable
   - Can be slower to compile
   - Can be less transparent about what's happening

2. Term Mode (direct construction)
   - Often more concise for simple proofs
   - More explicit and faster to compile
   - Can be more brittle to changes in mathlib
   - Harder or impossible to write for complex proofs
   - Can be challenging to read for complex proofs

You can see how your tactic proof translates to term mode using:
`#print "name_of_your_theorem"` though there are some nuances that
will become more clear when discussing quantifiers.

Some common patterns:
- `by exact p` becomes just `p`
- `by intro p; exact f p` becomes `fun p => f p`
- `by intro p; exact p` becomes `fun p => p` or simply `id`
- `by rw [h₁] at p; exact p` becomes `(h₁ ▸ p)`,

The last one only works for equality (`=`) in `h₁`, not for equivalence (`↔`).

Around 100,000 proofs out of 320,000 in mathlib are written in tactic mode,
though this includes proofs of minor facts where term mode is more appropriate.
-/

lemma id_proof (P Q : Prop) (p : P) (q : Q) : P := by
  assumption -- or exact p

-- You can print the term mode proof using `#print`
#print id_proof

lemma id_proof_term (P Q : Prop) (p : P) (q : Q) : P := p 

#print id_proof_term -- same output as #print id_proof


-- Identity function in various styles:
lemma intro_example (P : Prop) : P → P := by  -- tactic mode
  intro p
  exact p

#print intro_example

-- First syntax
example (P : Prop) : P → P := fun p => p

-- Second syntax
example (P : Prop) : P → P := λ p ↦ p

-- λ p ↦ p is just the identity function
lemma ex1 (P : Prop) : P → P := id -- have previously already seen `by exact id`

#print ex1 -- technically Lean looks at the term `fun P => id`

-- Lean actually takes all the arguments (things to the left of `:`) and `reverts` them into the goal before formulating the term mode
lemma ex2 : (P : Prop) → P → P := fun P p => p

example : ex1 = ex2 := rfl

example (P Q R : Prop) (h₁ : Q = P) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁] at h₂
  exact h₂

-- Sometimes `rw` can be express in term mode through `▸`
example (P Q R : Prop) (h₁ : Q = P) (h₂ : Q ↔ R) : P ↔ R := h₁ ▸ h₂


/-
# Exercises

Turn all of the previous exercises into term mode proofs.
-/

-- Chain three implications together: if we can go from `P` to `Q` to `R` to `S`,  then `P → S`
example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S :=
  fun p => h₃ (h₂ (h₁ p))

example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S :=
  fun p => h₃ <| h₂ <| h₁ p

example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S :=
  fun  p => (h₃ ∘ h₂ ∘ h₁) p

example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S :=
  h₃ ∘ h₂ ∘ h₁

-- Nested implications: if `P` implies `(Q → R)` and `P` implies `Q`, then `P` implies `R`
example (P Q R : Prop) (h₁ : P → Q → R) (h₂ : P → Q) : P → R :=
  fun p => (h₁ p) (h₂ p)

-- This fails because `▸` only works for equality, not for equivalence
example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁.symm] at h₂
  exact h₂

-- example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R :=
--   (h₁.symm ▸ h₂)
