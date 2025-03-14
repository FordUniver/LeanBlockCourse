/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse.P04_NaturalNumbers.S02_Addition
import Mathlib.Tactic.ByContra

namespace MyNat

/-
## Exercise: Define Multiplication Inductively
-/

-- Define multiplication `mul` inductively
def mul (n m : MyNat) : MyNat :=
  match m with
  | MyNat.zero => 0
  | MyNat.succ k => (mul n k) + n

-- show that we have an instance of `instMul`
instance instMul : Mul MyNat where mul := mul

-- show that `n * 0 = 0`
lemma mul_zero (n : MyNat) : n * 0 = 0 := rfl

-- show that `n * succ m = n * m + n`
lemma mul_succ (n m : MyNat) : n * succ m = n * m + n := rfl


/-
## Exercises: Mixing Addition and Multiplication
-/

-- m * 1 = m
lemma mul_one (n : MyNat) : n * 1 = n := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

-- 0 * n = 0
lemma zero_mul (n : MyNat) : 0 * n = 0 := by
  induction' n with k ih
  · rfl
  · rw [mul_succ, ih, add_zero]

-- succ n * m = n * m + m
lemma succ_mul (n m : MyNat) : (succ n) * m = n * m + m := by
  induction' m with k ih
  · rfl
  · rw [mul_succ, ih, mul_succ]
    rw [add_assoc, add_assoc]
    rw [add_succ k, add_succ n]
    rw [add_comm n k]

-- Commutativity: n * m = m * n
lemma mul_comm (n m : MyNat) : n * m = m * n := by
  induction' m with k ih
  · rw [← zero_eq_zero, zero_mul]; rfl
  · rw [succ_mul, ← ih]; rfl

-- Multiplicative identity: 1 * m = m
lemma one_mul (m : MyNat): 1 * m = m := by
  rw [mul_comm, mul_one]

-- 2 * m = m + m 
lemma two_mul (m : MyNat): 2 * m = m + m := by
  rw [two_eq_succ_one, succ_mul, one_mul]

#print Nat.two_mul

-- Right distributive law: a * (b + c) = a * b + a * c
lemma mul_add (n m k : MyNat) : n * (m + k) = n * m + n * k := by
  induction' n with s ih
  · rw [← zero_eq_zero, zero_mul, zero_mul, zero_mul, add_zero]
  · rw [succ_mul, ih, succ_mul, succ_mul]
    rw [add_assoc, ← add_assoc (s*k), add_comm (s * k)]
    rw [add_assoc, add_assoc] 

example (n m k : MyNat) : n * (m + k) = n * m + n * k := by
  induction' m with s ih
  · rw [← zero_eq_zero, zero_add, mul_zero, zero_add]
  · rw [succ_add, mul_succ, mul_succ, add_right_comm, ih]

-- Left distributive law: (a + b) * c = a * c + b * c
lemma add_mul (n m k : MyNat) : (n + m) * k = n * k + m * k := by
  rw [mul_comm, mul_comm n, mul_comm m, mul_add]

-- Associativity: (a * b) * c = a * (b * c)
lemma mul_assoc (n m k : MyNat) : (n * m) * k = n * (m * k) := by
  induction' m with m' ih
  · rw [← zero_eq_zero, mul_zero, zero_mul]; rfl
  · rw [mul_succ, succ_mul, add_mul, ih, mul_add]
