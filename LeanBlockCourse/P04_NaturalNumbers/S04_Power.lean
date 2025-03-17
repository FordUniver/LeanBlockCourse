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
lemma zero_pow_zero : (0 : MyNat) ^ (0 : MyNat) = 1 := rfl

-- 0 ^ (succ n) = 0
lemma zero_pow_succ (n : MyNat) : (0 : MyNat) ^ (succ n) = 0 := by
  rw [pow_succ, mul_zero]

-- a ^ 1 = a
lemma pow_one (n : MyNat) : n ^ (1 : MyNat) = n := by
  rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]

-- 1 ^ n = 1
lemma one_pow (n : MyNat) : (1 : MyNat) ^ n = 1 := by
  induction' n with m ind_assump
  · rw [← zero_eq_zero, pow_zero]
  · rw [pow_succ, ind_assump, mul_one]

-- a ^ 2 = a * a
lemma pow_two (n : MyNat) : n ^ (2 : MyNat) = n * n := by
  rw [two_eq_succ_one, pow_succ, pow_one]

-- n ^ (m + k) = n ^ m * n ^ k
lemma pow_add (n m k : MyNat) : n ^ (m + k) = n ^ m * n ^ k := by
  induction' k with m ind_assump
  · rw [← zero_eq_zero, add_zero, pow_zero, mul_one]
  · rw [add_succ, pow_succ, pow_succ, ind_assump, mul_assoc]

-- (a * b) ^ n = a ^ n * b ^ n
lemma mul_pow (n m k : MyNat) : (n * m) ^ k = n ^ k * m ^ k := by
  induction' k with k' ind_assump
  · rw [← zero_eq_zero, pow_zero, pow_zero, pow_zero, mul_one]
  · rw [pow_succ, pow_succ, pow_succ, ind_assump]
    repeat rw [mul_assoc]
    rw [mul_comm n (_ * m), mul_assoc, mul_comm m n]

-- (a ^ m) ^ n = a ^ (m * n)
lemma pow_pow (n m k : MyNat) : (n ^ m) ^ k = n ^ (m * k) := by
  induction' k with k' ind_assump
  · rw [← zero_eq_zero, mul_zero, pow_zero, pow_zero]
  · rw [pow_succ, ind_assump, mul_succ, pow_add]

-- (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b
lemma add_sq (n m : MyNat) : (n + m) ^ (2 : MyNat) = n ^ (2 : MyNat) + m ^ (2 : MyNat) + 2 * n * m := by
  rw [pow_two, pow_two, pow_two]
  rw [add_right_comm]
  rw [mul_add, add_mul, add_mul]
  rw [two_mul, add_mul]
  rw [mul_comm m n]
  rw [← add_assoc, ← add_assoc]
