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

-- From unique existence (`∃!`) we can deduce existence (`∃`):
example : ∀ (X : Type) (P : X → Prop),
  (∃! (x : X), P x) → ∃ (x : X), P x := by
  intro X P h
  obtain ⟨x, h_existence, h_uniqueness⟩ := h
  exact ⟨x, h_existence⟩

example : ∀ (X : Type) (P : X → Prop),
  (∃! (x : X), P x) → ∃ (x : X), P x := 
  fun _ _ ⟨x, h_existence, _⟩ => Exists.intro x h_existence


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
  constructor
  · intro h
    constructor
    · intro x
      obtain ⟨px, qx⟩ := h x
      exact px
    · intro x
      obtain ⟨px, qx⟩ := h x
      exact qx
  · intro ⟨h₁, h₂⟩
    intro x
    have px := h₁ x
    have qx := h₂ x
    exact ⟨px, qx⟩

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) ↔ ((∀ x : α, p x) ∧ (∀ x : α, q x)) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩ 

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) ↔ ((∀ x : α, p x) ∧ (∀ x : α, q x)) :=
  forall_and -- found through `exact?`

-- Prove that `∃ x, (p x ∨ q x) ↔ ((∃ x, p x) ∨ (∃ x, q x))`.
example (α : Type) (p q : α → Prop) : (∃ x : α, p x ∨ q x) ↔ ((∃ x : α, p x) ∨ (∃ x : α, q x)) := by
  constructor
  · intro h
    obtain ⟨x, (px | qx)⟩ := h
    · left; use x
    · right; use x
  · intro h
    obtain (⟨x, px⟩ | ⟨x, qx⟩) := h
    · use x; left; exact px
    · use x; right; exact qx 

example (α : Type) (p q : α → Prop) : (∃ x : α, p x ∨ q x) ↔ ((∃ x : α, p x) ∨ (∃ x : α, q x)) :=
  exists_or -- found through `exact?`

-- Prove that `((∀ x, p x) ∨ (∀ x, q x)) → (∀ x, p x ∨ q x)`.
example (α : Type) (p q : α → Prop) : ((∀ x : α, p x) ∨ (∀ x : α, q x)) → (∀ x : α, p x ∨ q x) := by
  intro h x
  obtain (px | qx) := h
  · left; exact px x
  · right; exact qx x

-- Prove that `(∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)`.
example (α : Type) (P Q : α → Prop) : (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  intro ⟨x, px, qx⟩
  constructor
  all_goals use x

-- Use the `choose` tactic to prove the following:
example (X : Type) (R : X → X → Prop) (h : ∀ x, ∃ y, R x y) :
    ∃ f : X → X, ∀ x, R x (f x) := by
  choose f hf using h
  use f

example (X : Type) (R : X → X → Prop) (h : ∀ x, ∃ y, R x y) :
    ∃ f : X → X, ∀ x, R x (f x) :=
  (fun f hf => Exists.intro f hf) (fun x => Classical.choose (h x)) fun x => Classical.choose_spec (h x)

-- Use the `use` tactic to prove the following:
example (X Y : Type) (P : X → Prop) (Q : Y → Prop)
  (h₁ : ∃ x, P x) (h₂ : ∃ y, Q y) : ∃ z : X × Y, P z.1 ∧ Q z.2 := by
  obtain ⟨x, px⟩ := h₁
  obtain ⟨y, qy⟩ := h₂
  use ⟨x, y⟩

/-
## Remark

Looking at mathlib, you will find `∃` is defined as follows:

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

`∃!` is defined as a predicate using `∃`:

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x
-/

#check Exists

-- `Exists` in the goal can be closed through `use` ...
example : ∃ n, n = 2 := by
  use 2

-- ... or through `exact` with a constructor.
example : ∃ n, n = 2 := by
  exact ⟨2, rfl⟩

example : ∃ n, n = 2 := by
  exact Exists.intro 2 rfl

-- `Exists` in an assumption can be destructured using `obtain`  
example (X : Type) (P : X → Prop) (h : (∃! (x : X), P x)) : ∃ (x : X), P x := by
  obtain ⟨x, px, unique_x⟩ := h
  exact ⟨x, px⟩


/-
For `∀` you will not find such a clear definition since it is notation.
However the following shows that we essentially have three ways of expressing the same thing:
-/
section

variable (X : Type) (P : X → Prop)

axiom f1 (x : X) : P x

axiom f2 : (x : X) → P x -- this is what is going on internally in lean

axiom f3 : ∀ (x : X), P x

example : f1 = f2 := rfl

example : f1 = f3 := rfl

example : f2 = f3 := rfl

end


-- For all in the goal can be therefore dealt with through `intro` ...
example : ∀ (P : Prop), P ↔ P := by
  intro P
  rfl

-- ... while for all in an assumption can be dealt with an application
example (P : ℕ → Prop) (h : ∀ x, P x) : P 0 :=
  by exact h 0
