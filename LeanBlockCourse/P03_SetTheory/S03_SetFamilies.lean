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
  sorry

-- Prove that the union of a set family is the union of a set family containing the unions of the sets in the original family.
example (F G : Set (Set α)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  sorry

-- Prove that the union of a set family is a subset of a set if and only if every set in the family is a subset of the set.
example (S : Set α) (F : Set (Set α)) : ⋃₀ F ⊆ S ↔ ∀ t ∈ F, t ⊆ S := by
  sorry

-- Prove that the intersection of a set with the union of a set family is the union of the intersections of the set with the sets in the family.
example (S : Set α) (F : Set (Set α)) : S ∩ (⋃₀ F) = ⋃₀ {t | ∃ u ∈ F, t = S ∩ u} := by
  sorry

-- Prove that the intersection of two sets is the intersection of a set family containing those two sets.
example (R S : Set α) : R ∩ S = ⋂₀ {R, S} := by
  sorry

-- Prove that the intersection of the union of two set families is the union of the intersections of the set families.
example (F G : Set (Set α)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  sorry

-- Prove that a set is a subset of the intersection of a set family if and only if it is a subset of every set in the family.
example (S : Set α) (F : Set (Set α)) : S ⊆ ⋂₀ F ↔ ∀ t ∈ F, S ⊆ t := by
  sorry

-- Prove that the intersection of a set with the union of a set family is a subset of the union of the intersection of the set with the sets in the family.
example (S : Set α) (F G : Set (Set α)) (h₁ : ∀ t ∈ F, S ∪ t ∈ G) : ⋂₀ G ⊆ S ∪ (⋂₀ F) := by
  sorry

-- Prove that the intersection of the union of a set family with the intersection of another set family is a subset of the union of the intersections of the set family with the sets in the other set family.
example (F G H : Set (Set α)) (h₁ : ∀ t ∈ F, ∃ u ∈ G, t ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  sorry

-- Prove that the complement of the union of a set family is the intersection of the complements of the sets in the family.
example (F : Set (Set α)) : (⋃₀ F)ᶜ = ⋂₀ {t | tᶜ ∈ F} := by
  sorry

-- Prove that the complement of the intersection of a set family is the union of the complements of the sets in the family.
example (F : Set (Set α)) : (⋂₀ F)ᶜ = ⋃₀ {t | tᶜ ∈ F} := by
  sorry

-- Prove that there exists a set that is an element of both set families if and only if there exists a set that is a subset of every set in the first set family and every set in the second set family.
example (F G : Set (Set α)) (h₁ : ∀ t ∈ F, ∃ u ∈ G, t ⊆ u) (h₂ : ∃ t ∈ F, ∀ u ∈ G, u ⊆ t) :
    ∃ s, s ∈ F ∩ G := by
  sorry

-- Prove that the intersection of the union of two set families with the complement of the union of the second set family is a subset of the union of the intersections of the set families with the complement of the union of the second set family.
example (F G : Set (Set α)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  sorry

-- Prove that the union of the intersection of two set families with the intersection of the union of the second set family is a subset of the union of the intersections of the set families with the intersection of the union of the second set family.
example (F G : Set (Set α)) (h₁ : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  sorry

-- Prove that the intersection of the union of two set families with the complement of the union of the second set family is a subset of the union of the intersections of the set families with the complement of the union of the second set family.
example (F G : Set (Set α)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {t | ∃ u ∈ F, ∃ v ∈ G, t = u ∩ vᶜ} := by
  sorry

-- Prove that if a set is a subset of another set, then there exists a set that is an element of the first set family and a subset of the second set.
example (S : Set α) (h₁ : ∀ F, (⋃₀ F = S → S ∈ F)) : ∃ x, S = {x} := by
  sorry
