/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse.P04_NaturalNumbers.S03_Multiplication

namespace MyNat

-- Define power recursively
def pow (n m : MyNat) : MyNat :=
  match m with
  | zero    => 1
  | succ k  => pow n k * n

instance : Pow MyNat MyNat where
  pow := pow

-- The two axioms underlying the power function
lemma pow_zero (n : MyNat) : n ^ (0 : MyNat) = 1 := rfl

lemma pow_succ (n m : MyNat) : n ^ (succ m) = n ^ m * n := rfl

/-
## Exercises
-/

-- 0 ^ 0 = 1
lemma zero_pow_zero : (0 : MyNat) ^ (0 : MyNat) = 1 := by
  sorry

-- 0 ^ (succ n) = 0
lemma zero_pow_succ (n : MyNat) : (0 : MyNat) ^ (succ n) = 0 := by
  sorry

-- a ^ 1 = a
lemma pow_one (n : MyNat) : n ^ (1 : MyNat) = n := by
  sorry

-- 1 ^ n = 1
lemma one_pow (n : MyNat) : (1 : MyNat) ^ n = 1 := by
  sorry

-- a ^ 2 = a * a
lemma pow_two (n : MyNat) : n ^ (2 : MyNat) = n * n := bby
  sorry

-- n ^ (m + k) = n ^ m * n ^ k
lemma pow_add (n m k : MyNat) : n ^ (m + k) = n ^ m * n ^ k := by
  sorry

-- (a * b) ^ n = a ^ n * b ^ n
lemma mul_pow (n m k : MyNat) : (n * m) ^ k = n ^ k * m ^ k := by
  sorry

-- (a ^ m) ^ n = a ^ (m * n)
lemma pow_pow (n m k : MyNat) : (n ^ m) ^ k = n ^ (m * k) := by
  sorry

-- (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b
lemma add_sq (n m : MyNat) : (n + m) ^ (2 : MyNat) = n ^ (2 : MyNat) + m ^ (2 : MyNat) + 2 * n * m := by
  sorry
