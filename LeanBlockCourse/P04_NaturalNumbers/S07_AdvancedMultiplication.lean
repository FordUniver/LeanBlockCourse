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
  sorry

-- If `n ≠ 0`, then `1 ≤ n`
lemma one_le_of_ne_zero {n : MyNat} (hn : n ≠ 0) : 1 ≤ n := by
  sorry

-- If `n * m ≠ 0`, then `m ≠ 0`
lemma mul_left_ne_zero {n m : MyNat} (h : n * m ≠ 0) : m ≠ 0 := by
  sorry

-- If `n * m ≠ 0`, then `n ≤ n * m`
lemma le_mul_right {n m : MyNat} (h : n * m ≠ 0) : n ≤ n * m := by
  sorry

-- If `n * m = 1`, then `n = 1`
lemma mul_right_eq_one {n m : MyNat} (h : n * m = 1) : n = 1 := by
  sorry

-- If `n ≠ 0` and `m ≠ 0`, then `n * m ≠ 0`
lemma mul_ne_zero {n m : MyNat} (hn : n ≠ 0) (hm : m ≠ 0) : n * m ≠ 0 := by
  sorry

-- If `n * m = 0`, then `n = 0` or `m = 0`
lemma mul_eq_zero {n m : MyNat} (h : n * m = 0) : n = 0 ∨ m = 0 := by
  sorry
