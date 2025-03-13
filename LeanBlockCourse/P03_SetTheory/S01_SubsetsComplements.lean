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
  rw [subset_def] at h₁
  have xt := h₁ x h₂
  exact xt 

example (x : α) (S T : Set α) (h₁ : S ⊆ T) (h₂ : x ∈ S) : x ∈ T := h₁ h₂

-- Prove that if `S ⊆ T` and `T ⊆ R`, then `S ⊆ R`.
example (x : α) (S T R : Set α) (h₁ : S ⊆ T) (h₂ : T ⊆ R) (h₃ : x ∈ S) : x ∈ R :=
  h₂ <| h₁ h₃

-- Prove that if `S ⊆ T` and `T ⊆ R`, then `S ⊆ R`.
example {x : α} {S T R : Set α} (h₁ : S ⊆ T) (h₂ : x ∈ T → x ∈ R) : x ∈ S → x ∈ R := by
  intro xs
  have xt := h₁ xs
  have xr := h₂ xt
  exact xr

example {x : α} {S T R : Set α} (h₁ : S ⊆ T) (h₂ : x ∈ T → x ∈ R) : x ∈ S → x ∈ R :=
  fun xs => (h₂ (h₁ xs))

-- Prove that if `S ⊆ T`, then for any `x ∉ T`, we have `x ∉ S`.
example (S T : Set α) (h : S ⊆ T) (x : α) (hx : x ∉ T) : x ∉ S := by
  by_contra xs
  have xt := h xs
  contradiction

example (S T : Set α) (h : S ⊆ T) (x : α) (hx : x ∉ T) : x ∉ S := fun xs => hx (h xs)

-- Prove that if `S ⊂ T` and `T ⊆ R`, then `S ⊂ R`.
example {S T R : Set α} (h₁ : S ⊂ T) (h₂ : T ⊆ R) : S ⊂ R := by
  obtain ⟨st, nts⟩ := h₁
  constructor
  · exact Subset.trans st h₂
  · intro rs
    have ts := Subset.trans h₂ rs
    exact nts ts

example {S T R : Set α} (h₁ : S ⊂ T) (h₂ : T ⊆ R) : S ⊂ R :=
  ⟨Subset.trans h₁.1 h₂, fun rs => h₁.2 (Subset.trans h₂ rs)⟩ 

-- Every set has a subset
example (S : Set α) : ∃ T, T ⊆ S := by
  use ∅
  exact empty_subset S

example (S : Set α) : ∃ T, T ⊆ S := by
  use S 



/-
## Set equality
-/

-- `S = T` iff `x ∈ S ↔ x ∈ T` for all `x`
lemma ext_iff {S T : Set α} : S = T ↔ ∀ x, x ∈ S ↔ x ∈ T := Set.ext_iff

-- The `ext` tactic can be used to prove equalities between sets
example (S : Set α) : S = S := by
  ext x
  rfl


/-
## Complements

For a set `S`, the complement `Sᶜ` is defined as the set of all elements of type
`α` that are not contained in `S`.
-/

-- `x ∈ Sᶜ` iff `x ∉ S`.
lemma mem_compl_iff (S : Set α) (x : α) : x ∈ Sᶜ ↔ x ∉ S := by rfl

example (S : Set α) : Sᶜ = compl S := rfl 

/-
## Exercises
-/

lemma Subset.antisymm {S T : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ S) : S = T := by
  ext x -- same as `rw [Set.ext_iff]; intro x`
  constructor
  · intro xs; exact h₁ xs
  · intro xt; exact h₂ xt

example {S T : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ S) : S = T := by
  rw [Set.ext_iff]
  exact fun x => ⟨fun xs => h₁ xs, fun xt => h₂ xt⟩

--Prove `S = T` is the same as `S ⊆ T ∧ T ⊆ S`
lemma Subset.antisymm_iff {S T : Set α} : (S = T) ↔ (S ⊆ T ∧ T ⊆ S) := by
  constructor
  · intro h
    rw [h]
    constructor
    · intro x xt; exact xt
    · intro x xs; exact xs
  · intro ⟨h₁, h₂⟩; exact Subset.antisymm h₁ h₂

example {S T : Set α} : (S = T) ↔ (S ⊆ T ∧ T ⊆ S) := by
  constructor
  · intro h
    rw [h]
    exact ⟨fun x xt =>  xt, fun x xs =>  xs⟩
  · intro ⟨h₁, h₂⟩; exact Subset.antisymm h₁ h₂

-- Prove that if `x ∈ S` and `x ∉ T`, then we cannot have `S ⊆ T`.
example {S T : Set α} {x : α} (h₁ : x ∈ S) (h₂ : x ∉ T) : ¬S ⊆ T := by
  by_contra st -- or `intro st`
  have xt :=  st h₁
  contradiction -- or `exact h₂ xt`

example {S T : Set α} {x : α} (h₁ : x ∈ S) (h₂ : x ∉ T) : ¬S ⊆ T :=
  fun st => h₂ (st h₁)

-- Prove that if S ⊆ T, then Tᶜ ⊆ Sᶜ.
lemma compl_subset_compl_of_subset {S T : Set α} (h₁ : S ⊆ T) : Tᶜ ⊆ Sᶜ := by
  intro x
  intro xtc
  rw [mem_compl_iff] -- not necessary since this just uses `rfl`
  intro h₃
  exact xtc (h₁ h₃)

example {S T : Set α} (h₁ : S ⊆ T) : Tᶜ ⊆ Sᶜ :=
  fun _ h₂ h₃ => h₂ (h₁ h₃)

-- `compl_compl`: The complement of the complement of `S` is `S`.
example (S : Set α) : Sᶜᶜ = S := by
  ext x
  repeat rw [mem_compl_iff]
  push_neg
  rfl

-- Equivalence between subset inclusion and inclusion of complements.
lemma compl_subset_compl (S T : Set α) : Tᶜ ⊆ Sᶜ ↔ S ⊆ T  := by
  constructor
  · intro h
    have := compl_subset_compl_of_subset h
    rw [compl_compl, compl_compl] at this
    exact this
  · intro h
    apply compl_subset_compl_of_subset
    exact h

example (S T : Set α) : Tᶜ ⊆ Sᶜ ↔ S ⊆ T  := 
  ⟨fun h₁ => compl_compl S ▸ compl_compl T ▸ compl_subset_compl_of_subset h₁,
  compl_subset_compl_of_subset⟩

-- Prove that if `S ⊆ T`, then for any `x ∈ Tᶜ`, we have `x ∈ Sᶜ`.
example (S T : Set α) (h : S ⊆ T) {x : α} (hx : x ∈ Tᶜ) : x ∈ Sᶜ := by
  rw [mem_compl_iff] at *
  intro xs 
  have xt := h xs
  contradiction

example (S T : Set α) (h : S ⊆ T) {x : α} (hx : x ∈ Tᶜ) : x ∈ Sᶜ :=
  fun xs => hx (h xs)

-- Prove that for any sets `R`, `S`, and `T`, if `R ⊆ S` and `S ⊆ T`, then `Tᶜ ⊆ Rᶜ`.
example (R S T : Set α) (h₁ : R ⊆ S) (h₂ : S ⊆ T) : Tᶜ ⊆ Rᶜ := by
  apply compl_subset_compl_of_subset
  exact Subset.trans h₁ h₂ 

example (R S T : Set α) (h₁ : R ⊆ S) (h₂ : S ⊆ T) : Tᶜ ⊆ Rᶜ :=
  compl_subset_compl_of_subset (Subset.trans h₁ h₂)

/-
## Remark

Our notion of set builds on DTT, so Sets are in fact just an inductive
type over some base type. This means every set always has a type associated
with it, even the empty set(s)! So the following doesn't work, not because 
it isn't true but because Lean's type check fails when you try to compare 
two sets of (possibly) different underlying types:

example (X Y : Type) : (∅ : Set X) = (∅ : Set Y) := by ...
-/


/-
## Remark
-/

#check Set.compl

-- This is the chain of logic how lean thinks about `x ∈ Sᶜ`
example (x : α) (S : Set α) : x ∈ Sᶜ ↔ x ∈ {a | a ∉ S} := by rfl

example (x : α) (S : Set α) : x ∈ {a | a ∉ S} ↔ x ∉ S := by rfl

example (x : α) (S : Set α) : x ∉ S ↔ ¬(x ∈ S) := by rfl

example (x : α) (S : Set α) : ¬(x ∈ S) ↔ (x ∈ S → False) := by rfl

-- We can  combine all of these into this
example (x : α) (S : Set α) : x ∈ Sᶜ ↔ (x ∈ S → False) := by rfl
