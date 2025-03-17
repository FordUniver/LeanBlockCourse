/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse.P04_NaturalNumbers.S04_Power

namespace MyNat

/-
## Exercises
-/

-- If n + k = m + k, then n = m
lemma add_right_cancel {n m k : MyNat} (h : n + k = m + k) : n = m := by
  induction' k with k' ih
  · assumption
  · -- repeat rw [add_succ] at h
    replace h := succ_inj h
    exact ih h

-- If k + n = k + m, then n = m
lemma add_left_cancel {n m k : MyNat} (h : k + n = k + m) : n = m := by
  rw [add_comm k, add_comm k] at h
  exact add_right_cancel h

-- If n + m = m, then n = 0
lemma add_left_eq_self {n m : MyNat} (h : n + m = m) : n = 0 := by
  nth_rewrite 2 [← zero_add m] at h 
  exact add_right_cancel h

-- If n + m = n, then m = 0
lemma add_right_eq_self {n m : MyNat} (h : n + m = n) : m = 0 := by
  nth_rw 2 [← add_zero n] at h
  exact add_left_cancel h 

example {n m : MyNat} (h : n + m = n) : m = 0 := by
  induction' n with n' ih
  · rw [← zero_eq_zero, zero_add] at h; assumption 
  · rw [succ_add] at h
    exact ih <| succ_inj h

-- If n + m = 0, then n = 0, proven by cases on n
lemma add_right_eq_zero {n m : MyNat} (h : n + m = 0) : n = 0 := by
  cases' n with n'
  · rfl
  · rw [succ_add] at h
    exfalso
    -- have := zero_ne_succ (n + m')
    contradiction

example {n m : MyNat} (h : n + m = 0) : n = 0 := by
  cases' m with m'
  · assumption
  · rw [add_succ] at h
    exfalso
    -- have := zero_ne_succ (n + m')
    contradiction

-- If a + b = 0, then b = 0
lemma add_left_eq_zero {n m : MyNat} (h : n + m = 0) : m = 0 := by
  rw [add_comm] at h
  exact add_right_eq_zero h
