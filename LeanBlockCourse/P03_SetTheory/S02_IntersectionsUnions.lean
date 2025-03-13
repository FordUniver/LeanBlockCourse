/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Cases
import LeanBlockCourse.P03_SetTheory.S01_SubsetsComplements

variable {α : Type*}

/-
# Sets: Intersections and Unions
=====================

## Intersection Basics

The intersection of two sets `S` and `T`, denoted `S ∩ T`, is defined as the
set of elements `x` for which `x ∈ S ∧ x ∈ T`.
-/

example (S T : Set α) : S ∩ T = {x | x ∈ S ∧ x ∈ T} := rfl

-- `x ∈ S ∩ T` iff `x ∈ S` and `x ∈ T`.
lemma mem_inter_iff (x : α) (S T : Set α) : x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T := by rfl

-- If `x ∈ S ∩ T`, then `x ∈ T`.
lemma mem_of_mem_inter_right {x : α} {S T : Set α} (h : x ∈ S ∩ T) : x ∈ T := by
  rw [mem_inter_iff] at h
  exact h.2

example {x : α} {S T : Set α} (h : x ∈ S ∩ T) : x ∈ T := h.2

-- The intersection of two sets is a subset of the first set.
lemma inter_subset_left (S T : Set α) : S ∩ T ⊆ S := by
  intro x xst
  rw [mem_inter_iff] at xst
  exact xst.1

example (S T : Set α) : S ∩ T ⊆ S := fun _ xst => xst.1
  
-- If `x ∈ S` and `x ∈ T`, then `x ∈ S ∩ T`.
lemma mem_inter {x : α} {S T : Set α} (h₁ : x ∈ S) (h₂ : x ∈ T) : x ∈ S ∩ T := by
  rw [mem_inter_iff]
  constructor
  · exact h₁
  · exact h₂

example  (x : α) (S T : Set α) (h₁ : x ∈ S) (h₂ : x ∈ T) : x ∈ S ∩ T := ⟨h₁, h₂⟩

#check mem_inter -- this is ours
#check Set.mem_inter -- this is in mathlib


/-
## Exercises
-/

-- Prove that if `R ⊆ S` and `R ⊆ T`, then `R ⊆ S ∩ T`.
example (R S T : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T := by
  sorry

-- The intersection of two sets is a subset of the second set.
lemma inter_subset_swap (S T : Set α) : S ∩ T ⊆ T ∩ S := by
  sorry

-- If `R ⊆ S` and `R ⊆ T`, then `R ⊆ S ∩ T`.
lemma subset_inter (R S T : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T := by
  sorry

-- The intersection of two sets is commutative.
lemma inter_comm (S T : Set α) : S ∩ T = T ∩ S := by
  sorry

-- The intersection of three sets is associative.
lemma inter_assoc (R S T : Set α) : (R ∩ S) ∩ T = R ∩ (S ∩ T) := by
  sorry
