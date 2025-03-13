/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NthRewrite
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

-- The intersection of two sets is a subset of the second set.
lemma inter_subset_swap (S T : Set α) : S ∩ T ⊆ T ∩ S := by
  intro x xst
  rw [mem_inter_iff] at *
  obtain ⟨xs, xt⟩ := xst
  constructor
  · exact xt
  · exact xs

example (S T : Set α) : S ∩ T ⊆ T ∩ S := by
  intro x xst
  obtain : x ∈ S ∧ x ∈ T := xst
  suffices x ∈ T ∧ x ∈ S by exact this
  exact⟨xst.2, xst.1⟩ 

example (S T : Set α) : S ∩ T ⊆ T ∩ S := fun _ xst => ⟨xst.2, xst.1⟩

-- If `R ⊆ S` and `R ⊆ T`, then `R ⊆ S ∩ T`.
lemma subset_inter (R S T : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T := by
  intro x xr
  rw [mem_inter_iff]
  constructor
  · exact h₁ xr
  · exact h₂ xr

example (R S T : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T :=
  fun _ xr => ⟨h₁ xr, h₂ xr⟩

#check Set.subset_inter

-- The intersection of two sets is commutative.
lemma inter_comm (S T : Set α) : S ∩ T = T ∩ S := by
  ext x
  -- rw [mem_inter_iff, mem_inter_iff]
  exact And.comm

#check Set.inter_comm

-- The intersection of three sets is associative.
lemma inter_assoc (R S T : Set α) : (R ∩ S) ∩ T = R ∩ (S ∩ T) := by
  ext x
  -- rw [mem_inter_iff, mem_inter_iff, mem_inter_iff, mem_inter_iff]
  exact and_assoc

/-
## Union Basics

The union of two sets `S` and `T`, denoted `S ∪ T`, is defined as the
set of elements `x` for which `x ∈ S ∨ x ∈ T`.
-/

-- `x ∈ S ∪ T` iff `x ∈ S` or `x ∈ T`.
lemma mem_union (x : α) (S T : Set α) : x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T := by rfl

/-
## Exercises
-/

-- If `x ∈ T`, then `x ∈ S ∪ T`.
lemma subset_union_right (S T : Set α) : T ⊆ S ∪ T := by
  intro x xt
  rw [Set.mem_union]
  right
  exact xt

example (S T : Set α) : T ⊆ S ∪ T := fun _ xt => Or.inr xt

-- Prove that if `R ⊆ T` and `S ⊆ T`, then `R ∪ S ⊆ T`.
lemma union_subset (R S T : Set α) (h₁ : R ⊆ T) (h₂ : S ⊆ T) : R ∪ S ⊆ T := by
  rintro x (xr | xs)
  · exact h₁ xr
  · exact h₂ xs

example (R S T : Set α) (h₁ : R ⊆ T) (h₂ : S ⊆ T) : R ∪ S ⊆ T := by
  rintro x xrs
  cases' xrs with xr | xs
  · exact h₁ xr
  · exact h₂ xs

-- Prove that `S ∪ T ⊆ T ∪ S`.
lemma union_subset_swap (S T : Set α) : S ∪ T ⊆ T ∪ S := by
  intro x xst
  rw [mem_union] at *
  apply or_comm.mp 
  exact xst

example (S T : Set α) : S ∪ T ⊆ T ∪ S := by
  intro x xst
  rw [mem_union] at *
  rw [or_comm]
  exact xst

example (S T : Set α) : S ∪ T ⊆ T ∪ S := fun _ xst => or_comm.mp xst

-- Prove that `S ∪ T = T ∪ S`.
lemma union_comm (S T : Set α) : S ∪ T = T ∪ S := by
  ext x
  -- rw [mem_union]
  exact or_comm

-- Prove that the complement of the intersection of two sets is the union of their complements.
lemma compl_inter (S T : Set α) : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ := by
  ext x
  constructor
  · intro xstc
    obtain : x ∈ S ∩ T → False := xstc
    by_contra xsctc
    rw [mem_union] at xsctc
    push_neg at xsctc
    obtain ⟨xsc, xtc⟩ := xsctc
    obtain xs : x ∈ S := Set.not_mem_compl_iff.mp xsc
    obtain xt : x ∈ T := Set.not_mem_compl_iff.mp xtc
    rw [Set.mem_inter_iff] at xstc
    exact xstc ⟨xs, xt⟩
  · intro h
    by_contra nxstc
    obtain xst : x ∈ S ∩ T := Set.not_mem_compl_iff.mp nxstc
    obtain ⟨xs, xt⟩ := xst
    rw [mem_union] at h
    obtain (h₁ | h₂) := h
    · contradiction
    · contradiction

example (S T : Set α) : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ := by
  ext x
  rw [mem_compl_iff, mem_inter_iff, mem_union, mem_compl_iff, mem_compl_iff]
  push_neg
  constructor
  · intro h
    by_cases xs : x ∈ S 
    · right; exact h xs
    · left; exact xs
  · intro h xs
    obtain (nxs | nxt) := h
    · contradiction
    · exact nxt


-- Prove that the complement of the union of two sets is the intersection of their complements.
lemma compl_union (S T : Set α) : (S ∪ T)ᶜ = Sᶜ ∩ Tᶜ := by
  nth_rw 1 [← compl_compl S, ← compl_compl T]
  rw [← compl_inter Sᶜ Tᶜ, compl_compl]
  -- This nice proof is thanks to Silas!

-- Prove that the union of three sets is associative.
lemma union_assoc (R S T : Set α) : (R ∪ S) ∪ T = R ∪ (S ∪ T) := by
  ext x
  -- rw [mem_union, mem_union, mem_union, mem_union]
  exact or_assoc

-- Prove that the intersection of a set with the union of two sets is distributive.
lemma inter_distrib_left (R S T : Set α) : R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T) := by
  ext x
  -- rw [mem_union, mem_inter_iff, mem_union, mem_inter_iff, mem_inter_iff]
  exact and_or_left -- this is just `P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)`

-- Note the inconsistent naming scheme
#check Set.mem_union
#check Set.mem_inter_iff 

-- Prove that if `R ∪ T ⊆ S ∪ T` and `R ∩ T ⊆ S ∩ T`, then `R ⊆ S`. 
example (R S T : Set α) (h₁ : R ∪ T ⊆ S ∪ T) (h₂ : R ∩ T ⊆ S ∩ T) : R ⊆ S := by
  intro x xr
  have xrut : x ∈ R ∪ T := Or.inl xr
  have xsut : x ∈ S ∪ T := h₁ xrut
  obtain (xs | xt) := xsut
  · assumption
  · have xrit : x ∈ R ∩ T := ⟨xr, xt⟩
    have xsit : x ∈ S ∩ T := h₂ xrit
    obtain ⟨xs, xt⟩ := xsit
    assumption

example (R S T : Set α) (h₁ : R ∪ T ⊆ S ∪ T) (h₂ : R ∩ T ⊆ S ∩ T) : R ⊆ S := by
  intro x xr
  obtain (xs | xt) := h₁ (Or.inl xr)
  · exact xs
  · exact (h₂ ⟨xr, xt⟩).1
