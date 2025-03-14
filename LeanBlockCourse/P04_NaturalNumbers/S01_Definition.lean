/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Use

/-
# Defining the natural numbers in Lean
=====================================

## The inductive definition of `MyNat`
-/



inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat


namespace MyNat

-- Establish `MyNat` as an inhabited type
instance : Inhabited MyNat where
  default := MyNat.zero

#check 0

-- Establish a conversion from `Nat` to `MyNat` so we can use numbers
def ofNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero   => MyNat.zero
  | Nat.succ b => MyNat.succ (ofNat b)

instance instofNat {n : Nat} : OfNat MyNat n where
  ofNat := ofNat n

#check (0 : MyNat) 
 
-- Some basic theorems about successors in MyNat
lemma one_eq_succ_zero : 1 = succ 0 := rfl
lemma two_eq_succ_one : 2 = succ 1 := rfl
lemma three_eq_succ_two : 3 = succ 2 := rfl
lemma four_eq_succ_three : 4 = succ 3 := rfl
lemma five_eq_succ_four : 5 = succ 4 := rfl
lemma zero_eq_zero : 0 = zero := rfl


/-
## Exercises
-/

-- 2 = succ (succ 0)
example : 2 = succ (succ 0) := by
  sorry

-- zero is not the successor of any number
lemma zero_ne_succ (n : MyNat) : 0 ≠ succ n := by
  sorry

-- 0 ≠ 1
lemma zero_ne_one : (0 : MyNat) ≠ 1 := by
  sorry

-- 1 ≠ 0
lemma one_ne_zero : (1 : MyNat) ≠ 0 := by
  sorry

-- Any non-zero natural number is the successor of another number
-- Hint: try the `cases` tactic  
lemma eq_succ_of_ne_zero {n : MyNat} (h : n ≠ 0) : ∃ m : MyNat, n = succ m := by
  sorry
