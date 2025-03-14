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
  sorry

-- 0 * n = 0
lemma zero_mul (n : MyNat) : 0 * n = 0 := by
  sorry

-- succ n * m = n * m + m
lemma succ_mul (n m : MyNat) : (succ n) * m = n * m + m := by
  sorry

-- Commutativity: n * m = m * n
lemma mul_comm (n m : MyNat) : n * m = m * n := by
  sorry

-- Multiplicative identity: 1 * m = m
lemma one_mul (m : MyNat): 1 * m = m := by
  sorry

-- 2 * m = m + m 
lemma two_mul (m : MyNat): 2 * m = m + m := by
  sorry

-- Right distributive law: a * (b + c) = a * b + a * c
lemma mul_add (n m k : MyNat) : n * (m + k) = n * m + n * k := by
  sorry

-- Associativity: (a * b) * c = a * (b * c)
lemma mul_assoc (n m k : MyNat) : (n * m) * k = n * (m * k) := by
  sorry

-- Left distributive law: (a + b) * c = a * c + b * c
lemma add_mul (n m k : MyNat) : (n + m) * k = n * k + m * k := by
  sorry
