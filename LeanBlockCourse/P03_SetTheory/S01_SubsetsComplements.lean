/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic

/-
So far we have always seen variables as explicit arguments to statements, usually
looking something like `(P : Prop)`. Here we are doing three things differently:

1. We are using `variable` to declare an that is used in any statement that follows.
2. We are using curly brackets `{}` to denote an implicit argument.
3. We are using `Type*` to denote an unspecified type (more on this later).

Also note that all of the named statements in this section are already in mathlib
in the namespace `Set` which one can access by either preceding the name with `Set.`
or by opening the namespace with `open Set`.
-/

variable {α : Type*}

/-
# Sets
=====================

`S : Set α` means `S` is a set of elements of type `α`.
-/

-- An element `x` being in the set defined by `P : α → Prop` means `P x`.
-- Here `{ x | P x}` constructs the set of all `x : α` for which `P x` holds. 
lemma mem_setOf (x : α) (P : α → Prop) : x ∈ { x | P x} ↔ P x := by rfl

-- `Nonempty S` means the type `S` is not empty.
example (x : α) (S : Set α) (h : x ∈ S) : Nonempty S := by
  use x

example (x : α) (S : Set α) (h : x ∈ S) : Nonempty S := by
  exact ⟨x, h⟩

-- `{x}` constructs the set containing `x`.
lemma mem_singleton_iff {x y : α} : x ∈ ({y} : Set α) ↔ x = y := by rfl

example {x y : α} : x ∈ Set.singleton y ↔ x = y := by rfl

-- `{x, y}` constructs the set containing two elements `x` and `y`.
lemma mem_pair (t x y : α) : t ∈ ({x, y} : Set α) ↔ t = x ∨ t = y := by rfl


/-
## Subsets
-/
  
-- `S ⊆ T` in Lean is defined as `∀ x, x ∈ S → x ∈ T`.
lemma subset_def {S T : Set α} : (S ⊆ T) = ∀ x ∈ S, x ∈ T := rfl

-- `S ⊂ T` in Lean is defined as `S ⊆ T ∧ ¬T ⊆ S`.
lemma ssubset_def {S T : Set α} : (S ⊂ T) = (S ⊆ T ∧ ¬T ⊆ S) := rfl

-- Reflexivity: Every set is a subset of itself.
lemma Subset.rfl (S : Set α) : S ⊆ S := by
  rw [subset_def] -- since `subset_def` is true by `rfl` this is just to unfold the definition in the infoview
  intro x h -- `∀ x ∈ S, ...` actually means `∀ (x : α), (h : x ∈ S) → ...`
  exact h

example (S : Set α) : S ⊆ S := fun _ h => h

-- Transitivity: If `S ⊆ T` and `T ⊆ R` then `S ⊆ R`.
lemma Subset.trans {S T R : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ R) : S ⊆ R := by
   rw [subset_def] at *
   intro x xs
   have xt := h₁ x xs
   have xr := h₂ x xt
   exact xr

example {S T R : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ R) : S ⊆ R := fun x xs => h₂ (h₁ xs)

-- The empty set is the set of elements of type `α` for which `False` holds.
example : ∅ = {x : α | False} := rfl

-- The empty set is a subset of every set.
lemma empty_subset (S : Set α) : ∅ ⊆ S := by
  rw [subset_def]
  intro x h
  exfalso
  exact h

example (S : Set α) : ∅ ⊆ S := by
  intro x h
  contradiction


/-
## Exercises
-/

-- Prove that if `S ⊆ T` and `x ∈ S`, then `x ∈ T`.
example (x : α) (S T : Set α) (h₁ : S ⊆ T) (h₂ : x ∈ S) : x ∈ T := by
  sorry

-- Prove that if `S ⊆ T` and `T ⊆ R`, then `S ⊆ R`.
example (x : α) (S T R : Set α) (h₁ : S ⊆ T) (h₂ : T ⊆ R) (h₃ : x ∈ S) : x ∈ R := by
  sorry

-- Prove that if `S ⊆ T` and `T ⊆ R`, then `S ⊆ R`.
example {x : α} {S T R : Set α} (h₁ : S ⊆ T) (h₂ : x ∈ T → x ∈ R) : x ∈ S → x ∈ R := by
  sorry

-- Prove that if `S ⊆ T`, then for any `x ∉ T`, we have `x ∉ S`.
example (S T : Set α) (h : S ⊆ T) (x : α) (hx : x ∉ T) : x ∉ S := by
  sorry

-- Prove that if `S ⊂ T` and `T ⊆ R`, then `S ⊂ R`.
example {S T R : Set α} (h₁ : S ⊂ T) (h₂ : T ⊆ R) : S ⊂ R := by
  sorry

-- Every set has a subset
example (S : Set α) : ∃ T, T ⊆ S := by
  sorry
