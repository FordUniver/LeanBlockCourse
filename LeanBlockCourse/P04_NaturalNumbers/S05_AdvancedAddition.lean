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
  sorry

-- If k + n = k + m, then n = m
lemma add_left_cancel {n m k : MyNat} (h : k + n = k + m) : n = m := by
  sorry

-- If n + m = m, then n = 0
lemma add_left_eq_self {n m : MyNat} (h : n + m = m) : n = 0 := by
  sorry

-- If n + m = n, then m = 0
lemma add_right_eq_self {n m : MyNat} (h : n + m = n) : m = 0 := by
  sorry

-- If x + y = x, then y = 0, proven by induction on x
example {n m : MyNat} (h : n + m = n) : m = 0 := by
  sorry

-- If a + b = 0, then a = 0, proven by cases on a
lemma add_right_eq_zero {n m : MyNat} (h : n + m = 0) : n = 0 := by
  sorry

-- If a + b = 0, then b = 0
lemma add_left_eq_zero {n m : MyNat} (h : n + m = 0) : m = 0 := by
  sorry
