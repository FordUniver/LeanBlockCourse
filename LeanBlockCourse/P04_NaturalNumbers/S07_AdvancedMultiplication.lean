/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse.P04_NaturalNumbers.S06_Inequalities
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Tauto

namespace MyNat

/-
## Exercises
-/

-- If `n ≤ m`, then `n * k ≤ m * k`
lemma mul_le_mul_right {n m : MyNat} (k : MyNat) (h : n ≤ m) : n * k ≤ m * k := by
  rw [le_iff] at *
  obtain ⟨x, h⟩ := h
  use x * k
  rw [h]
  rw [add_mul]

-- If `n ≠ 0`, then `1 ≤ n`
lemma one_le_of_ne_zero {n : MyNat} (hn : n ≠ 0) : 1 ≤ n := by
  cases' n with n'
  · contradiction
  · rw [le_iff]
    use n'
    rw [add_comm]
    rfl

-- If `n * m ≠ 0`, then `m ≠ 0`
lemma mul_left_ne_zero {n m : MyNat} (h : n * m ≠ 0) : m ≠ 0 := by
  intro hc
  rw [hc] at h
  rw [mul_zero] at h
  contradiction

-- If `n * m ≠ 0`, then `n ≤ n * m`
lemma le_mul_right {n m : MyNat} (h : n * m ≠ 0) : n ≤ n * m := by
  have h' := mul_left_ne_zero h
  have h'' := one_le_of_ne_zero h'
  have h''' := mul_le_mul_right n h''
  rw [one_mul, mul_comm] at h'''
  exact h'''

-- If `n * m = 1`, then `n = 1`
lemma mul_right_eq_one {n m : MyNat} (h : n * m = 1) : n = 1 := by
  have n_ne_zero : n ≠ 0 := by
    by_contra h'
    rw [h', zero_mul] at h
    contradiction

  have n_le_one : n ≤ 1 := by
    rw [h.symm]
    apply le_mul_right
    rw [h]
    exact one_ne_zero

  obtain (n_eq_zero | n_eq_one) := le_one n_le_one
  · contradiction
  · assumption

-- If `n ≠ 0` and `m ≠ 0`, then `n * m ≠ 0`
lemma mul_ne_zero {n m : MyNat} (hn : n ≠ 0) (hm : m ≠ 0) : n * m ≠ 0 := by
  have ⟨x, hx⟩ := eq_succ_of_ne_zero hn
  have ⟨y, hy⟩ := eq_succ_of_ne_zero hm
  rw [hx, hy, mul_succ, add_succ]
  symm
  apply zero_ne_succ


-- If `n * m = 0`, then `n = 0` or `m = 0`
lemma mul_eq_zero {n m : MyNat} (h : n * m = 0) : n = 0 ∨ m = 0 := by
  by_contra! hc -- `by_contra!` combines `by_contra` with `push_neg` 
  obtain ⟨h₁, h₂⟩ := hc
  have h' := mul_ne_zero h₁ h₂
  contradiction
