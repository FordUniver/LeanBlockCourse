/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Cases

variable {α : Type*}

#check Set α  -- set with elements of type α
#check Set (Set α) -- set family of sets with elements of type α


/-
# Sets: Set Families
=====================

`S : Set (Set α)` means `S` is a set of sets (a set family) of elements of type `α`.

## Intersections of Set Families

We can use `⋂₀ S`, imported through `Mathlib.Order.SetNotation`, to
denote the intersection of a set family `S`.
-/

-- An element is in `⋂₀ S` iff if it is in every set of the family `S`.
lemma mem_sInter {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t := by rfl

-- If `S` is an element of (i.e. a set in) `F`, then `⋂₀ F` is a subset of `S`.
example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : ⋂₀ F ⊆ S := by
  intro x h
  rw [mem_sInter] at h
  have := h S h₁
  assumption

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : ⋂₀ F ⊆ S := fun _ h => h S h₁

-- If `F` is a subset of `G`, then `⋂₀ G` is a subset of `⋂₀ F`.
example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x h₂
  rw [mem_sInter] at *
  intro t h₃
  have : t ∈ G := h₁ h₃
  have : x ∈ t := h₂ t this
  assumption

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := fun _ h₂ t h₃ => h₂ t (h₁ h₃)

/-
## Unions of Set Families

We can also use `⋃₀ S` to denote the union of a set family `S`.
-/

-- An element is in `⋃₀ S` iff it is in some set of the family `S`.
lemma mem_sUnion {x : α} {S : Set (Set α)} : x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t := by rfl

-- If `S` is an element of `F`, then `S` is a subset of `⋃₀ F`.
example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : S ⊆ ⋃₀ F := by
  intro x xs
  rw [mem_sUnion]
  use S

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : S ⊆ ⋃₀ F := fun _ xs => ⟨S, h₁, xs⟩

-- If `F` is a subset of `G`, then `⋃₀ F` is a subset of `⋃₀ G`.
example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x h
  rw [mem_sUnion] at *
  obtain ⟨t, tf, xt⟩ := h
  have tg := h₁ tf
  use t 

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G :=
  fun _ ⟨t, tf, xt⟩ => ⟨t, h₁ tf, xt⟩ 


/-
## Exercises
-/

-- Prove that the union of two sets is the union of a set family containing those two sets.
example (R S : Set α) : R ∪ S = ⋃₀ {R, S} := by
  ext x
  constructor
  · rintro (xr | xs)
    · exact ⟨R, Or.inl rfl, xr⟩ 
    · exact ⟨S, Or.inr rfl, xs⟩
  · rintro ⟨t, ⟨tr | ts, h⟩⟩
    · exact Or.inl (tr ▸ h)
    · exact Or.inr (ts ▸ h)

-- Prove that the union of a set family is the union of a set family containing the unions of the sets in the original family.
example (F G : Set (Set α)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  constructor
  · rintro ⟨t, tf | tg, h₂⟩
    · left; exact ⟨t, tf, h₂⟩
    · right; exact ⟨t, tg, h₂⟩
  · rintro (⟨t, tf, h₁⟩ | ⟨t, tg, h₁⟩)
    · exact ⟨t, by left; exact tf, h₁⟩ 
    · exact ⟨t, by right; exact tg, h₁⟩

-- Prove that the union of a set family is a subset of a set if and only if every set in the family is a subset of the set.
example (S : Set α) (F : Set (Set α)) : ⋃₀ F ⊆ S ↔ ∀ t ∈ F, t ⊆ S := by
  constructor
  · intro h₁ t h₂ x h₃
    exact h₁ ⟨t, h₂, h₃⟩
  · intro h₁ x ⟨t, ht⟩
    exact h₁ t ht.left ht.right

-- Prove that the intersection of a set with the union of a set family is the union of the intersections of the set with the sets in the family.
example (S : Set α) (F : Set (Set α)) : S ∩ (⋃₀ F) = ⋃₀ {t | ∃ u ∈ F, t = S ∩ u} := by
  ext x
  constructor
  · rintro ⟨hS, t, ht₁, ht₂⟩
    exact ⟨S ∩ t, ⟨t, ht₁, rfl⟩, ⟨hS, ht₂⟩⟩
  · rintro ⟨t, ⟨u, hu₁, rfl⟩, ⟨hS, hu₂⟩⟩
    exact ⟨hS, u, hu₁, hu₂⟩

-- Prove that the intersection of two sets is the intersection of a set family containing those two sets.
example (R S : Set α) : R ∩ S = ⋂₀ {R, S} := by
  ext x
  constructor
  · rintro ⟨xr, xs⟩ t (rfl | rfl)
    · exact xr
    · exact xs
  · intro h
    exact ⟨h R (by left; rfl), h S (by right; rfl)⟩

-- Prove that the intersection of the union of two set families is the union of the intersections of the set families.
example (F G : Set (Set α)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  ext x
  constructor
  · intro h₁
    constructor
    · intro t h₂
      apply h₁ t
      left; exact h₂
    · intro t h₂
      apply h₁ t
      right; exact h₂
  · rintro ⟨h₁, h₂⟩ t (tf | tg)
    · exact h₁ t tf
    · exact h₂ t tg

-- Prove that a set is a subset of the intersection of a set family if and only if it is a subset of every set in the family.
example (S : Set α) (F : Set (Set α)) : S ⊆ ⋂₀ F ↔ ∀ t ∈ F, S ⊆ t := by
  constructor
  · intro h₁ t h₂ x h₃
    exact (h₁ h₃) t h₂
  · intro h₁ x h₂ t h₃
    exact (h₁ t h₃) h₂

-- Prove that the intersection of a set with the union of a set family is a subset of the union of the intersection of the set with the sets in the family.
example (S : Set α) (F G : Set (Set α)) (h₁ : ∀ t ∈ F, S ∪ t ∈ G) : ⋂₀ G ⊆ S ∪ (⋂₀ F) := by
  intro x h₂
  by_cases xs : x ∈ S
  · left; exact xs
  · right
    intro t h₄
    obtain (hS2 | ht) := h₂ (S ∪ t) (h₁ t h₄)
    · by_contra h₆
      exact xs hS2
    · exact ht

-- Prove that the intersection of the union of a set family with the intersection of another set family is a subset of the union of the intersections of the set family with the sets in the other set family.
example (F G H : Set (Set α)) (h₁ : ∀ t ∈ F, ∃ u ∈ G, t ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  intro x ⟨⟨t, ht₁, ht₂⟩, h_subset_all⟩
  obtain ⟨u, hu₁, hu₂⟩ := h₁ t ht₁
  use t ∩ u
  exact ⟨hu₂, ⟨ht₂, h_subset_all u hu₁⟩⟩

-- Prove that the complement of the union of a set family is the intersection of the complements of the sets in the family.
example (F : Set (Set α)) : (⋃₀ F)ᶜ = ⋂₀ {t | tᶜ ∈ F} := by
  ext x
  constructor
  · intro h₁ t h₂
    rw [Set.mem_compl_iff, mem_sUnion] at h₁
    push_neg at h₁
    have h₃ := h₁ tᶜ h₂
    rw [Set.mem_compl_iff] at h₃
    push_neg at h₃
    exact h₃
  · intro h₁
    rw [Set.mem_compl_iff, mem_sUnion]
    push_neg
    intro t h₂
    exact (h₁ tᶜ) (by rw [Set.mem_setOf, compl_compl]; exact h₂)

-- Prove that the complement of the intersection of a set family is the union of the complements of the sets in the family.
example (F : Set (Set α)) : (⋂₀ F)ᶜ = ⋃₀ {t | tᶜ ∈ F} := by
  ext x
  constructor
  · intro h₁
    rw [Set.mem_compl_iff, mem_sInter] at h₁
    push_neg at h₁
    obtain ⟨t, ht⟩ := h₁
    use tᶜ
    rw [Set.mem_setOf, compl_compl, Set.mem_compl_iff]
    exact ht
  · intro ⟨u, hu⟩
    rw [Set.mem_compl_iff, mem_sInter]
    push_neg
    use uᶜ
    constructor
    · exact hu.left
    · rw [Set.mem_compl_iff]
      push_neg
      exact hu.right

-- Prove that there exists a set that is an element of both set families if and only if there exists a set that is a subset of every set in the first set family and every set in the second set family.
example (F G : Set (Set α)) (h₁ : ∀ t ∈ F, ∃ u ∈ G, t ⊆ u) (h₂ : ∃ t ∈ F, ∀ u ∈ G, u ⊆ t) :
    ∃ s, s ∈ F ∩ G := by
  obtain ⟨t, ht₁, ht₂⟩ := h₂
  obtain ⟨u, hu₁, hu₂⟩ := h₁ t ht₁
  have h₁ : u ⊆ t := ht₂ u hu₁
  have h₂ : t = u := Set.Subset.antisymm hu₂ h₁
  exact ⟨t, ht₁, h₂ ▸ hu₁⟩

-- Prove that the intersection of the union of two set families with the complement of the union of the second set family is a subset of the union of the intersections of the set families with the complement of the union of the second set family.
example (F G : Set (Set α)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x ⟨⟨t, ht₁, ht₂⟩, h₁⟩
  use t
  constructor
  · constructor
    · exact ht₁
    · rw [Set.mem_compl_iff]
      by_contra h₂
      rw [Set.mem_compl_iff, mem_sUnion] at h₁
      push_neg at h₁
      exact h₁ t h₂ ht₂
  · exact ht₂

-- Prove that the union of the intersection of two set families with the intersection of the union of the second set family is a subset of the union of the intersections of the set families with the intersection of the union of the second set family.
example (F G : Set (Set α)) (h₁ : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  intro x ⟨⟨t, ht₁, ht₂⟩, hg⟩
  use t
  constructor
  · constructor
    · exact ht₁
    · by_contra h
      have : x ∈ ⋃₀ (F ∩ Gᶜ) := ⟨t, ⟨⟨ht₁, h⟩, ht₂⟩⟩
      exact (h₁ this).right hg
  · exact ht₂

-- Prove that the intersection of the union of two set families with the complement of the union of the second set family is a subset of the union of the intersections of the set families with the complement of the union of the second set family.
example (F G : Set (Set α)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {t | ∃ u ∈ F, ∃ v ∈ G, t = u ∩ vᶜ} := by
  intro x ⟨⟨u, hu⟩, h₁⟩
  rw [Set.mem_compl_iff, mem_sInter] at h₁
  push_neg at h₁
  obtain ⟨v, hv⟩ := h₁
  use u ∩ vᶜ
  constructor
  · use u
    constructor
    · exact hu.left
    · use v
      exact ⟨hv.left, rfl⟩
  · rw [Set.mem_inter_iff, Set.mem_compl_iff]
    exact ⟨hu.right, hv.right⟩

-- Prove that if a set is a subset of another set, then there exists a set that is an element of the first set family and a subset of the second set.
example (S : Set α) (h₁ : ∀ F, (⋃₀ F = S → S ∈ F)) : ∃ x, S = {x} := by
  have h₂ := h₁ {t | ∃ x ∈ S, t = {x}}
  have h₃ : ⋃₀ {t | ∃ x ∈ S, t = {x}} = S := by 
    ext x
    constructor
    intro h₃
    obtain ⟨t, ht⟩ := h₃
    obtain ⟨y, hy⟩ := ht.left
    rw [hy.right] at ht
    rw [ht.right]
    exact hy.left
    intro h₃
    use {x}
    constructor
    · use x
    · rfl
  obtain ⟨y, hy⟩ := h₂ h₃
  use y
  exact hy.right
