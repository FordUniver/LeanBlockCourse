/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse.P04_NaturalNumbers.S05_AdvancedAddition
import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra

namespace MyNat


/-
## Inequality

We define `m ≤ n` as *notation* for `∃ k, m = n + k`.
-/ 

def le (n m : MyNat) := ∃ k, m = n + k

instance : LE MyNat := ⟨MyNat.le⟩

lemma le_refl (n : MyNat) : n ≤ n := by
  use 0
  rfl

lemma zero_le (n : MyNat) : 0 ≤ n := by
  use n
  rw [zero_add]

lemma le_iff (n m : MyNat) : n ≤ m ↔ ∃ k, m = n + k := by rfl 

/-
We also define `m < n` as `m ≤ n ∧ m ≠ n` OR as `m + 1 ≤ n`
-/ 

def lt (n m : MyNat) := (succ n) ≤ m

instance : LT MyNat := ⟨MyNat.lt⟩

lemma zero_lt (n : MyNat) (h : n ≠ 0) : 0 < n := by
  cases' n with n'
  · contradiction
  · use n'
    rw [add_comm]
    rfl

lemma lt_iff_le_ne' (m n : MyNat) : m < n ↔ ∃k, k ≠ 0 ∧ m + k = n := by
  constructor
  · intro ⟨k, hk⟩
    use k.succ
    rw [succ_add] at hk
    constructor
    · exact (zero_ne_succ k).symm
    · exact hk.symm
  · intro ⟨k, nk, hk⟩
    obtain ⟨k', hk'⟩ := eq_succ_of_ne_zero nk
    use k' 
    rw [succ_add, ← add_succ, ← hk']
    exact hk.symm


/-
## Exercises
-/

lemma le_succ_self (n : MyNat) : n ≤ succ n := by
  -- rw [le_iff]
  use 1
  rfl 
  
lemma le_trans {n m k : MyNat} (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  rw [le_iff] at *
  obtain ⟨x, hx⟩ := hnm
  obtain ⟨y, hy⟩ := hmk
  rw [hy, hx]
  use x + y
  rw [add_assoc]

lemma le_zero {n : MyNat} (hn : n ≤ 0) : n = 0 := by
  obtain ⟨k, hk⟩ := hn
  exact add_right_eq_zero hk.symm

lemma le_antisymm (n m : MyNat) (hnm : n ≤ m) (hmn : m ≤ n) : n = m := by
  obtain ⟨x, hx⟩ := hnm
  obtain ⟨y, hy⟩ := hmn
  rw [hx]
  rw [hx, add_assoc] at hy
  replace hy := add_right_eq_self hy.symm
  have := add_right_eq_zero hy
  rw [this, add_zero]

lemma succ_le_succ {n m : MyNat} (hn : succ n ≤ succ m) : n ≤ m := by
  obtain ⟨x, hx⟩ := hn
  use x
  apply succ_inj
  rw [succ_add] at hx
  assumption 

example (n m : MyNat) (h : n = 37 ∨ m = 42) : m = 42 ∨ n = 37 := by
  cases h
  · right; assumption
  · left; assumption

lemma le_one {n : MyNat} (hn : n ≤ 1) : n = 0 ∨ n = 1 := by
  cases' n with n'
  · left; rfl 
  · right
    obtain ⟨x, hx⟩ := hn
    rw [one_eq_succ_zero, succ_add] at hx
    replace hx := succ_inj hx
    rw [add_right_eq_zero hx.symm]
    rfl 

lemma lt_iff_le_and_ne (m n : MyNat) : m < n ↔ m ≤ n ∧ m ≠ n := by
  constructor
  · intro ⟨k, hk⟩
    rw [succ_add] at hk
    constructor
    · use k.succ
      exact hk
    · by_contra hc
      rw [hc] at hk
      replace hk : 0 = k.succ := (add_right_eq_self hk.symm).symm
      contradiction
  · intro ⟨⟨k, hk⟩, h⟩
    cases' k with k'
    · symm at hk; contradiction
    · use k'
      rw [succ_add]
      assumption

lemma le_total (n m : MyNat) : n ≤ m ∨ m ≤ n := by
  induction' m with m' ih
  · right; rw [← zero_eq_zero]; exact zero_le n
  · obtain (⟨x, hx⟩ | ⟨x, hx⟩) := ih
    · left
      use x + 1
      rw [← succ_eq_add_one, add_succ, hx] 
    · cases' x with x'
      · rw [← zero_eq_zero, add_zero] at hx
        left
        rw [hx]
        exact le_succ_self m'
      · right
        use x'
        rw [add_succ] at hx
        rw [succ_add]
        assumption


/-
## Bonus: State Fermat's Last Theorem

Fermat's Last Theorem states that if `x, y, z > 0` and
`m ≥ 3` then `x^m + y^m ≠ z^m`.

The shortest solution known to humans would translate into
many millions of lines of Lean code. Kevin Buzzard is working
on translating the proof by Wiles and Taylor into Lean, although
this task will take many years.
-/

theorem fermats_last_theorem (x y z m : MyNat)
  (hm : m ≥ 3) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
  x^m + y^m ≠ z^m := by sorry
