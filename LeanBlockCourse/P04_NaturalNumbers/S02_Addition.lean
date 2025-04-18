/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse.P04_NaturalNumbers.S01_Definition
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Cases

namespace MyNat

/-
## Defining Addition: Attempt #1
-/

axiom add' : MyNat → MyNat → MyNat
axiom add_zero' (a : MyNat) : add' a 0 = a
axiom add_succ' (a b : MyNat) : add' a (succ b) = succ (add' a b)

#check add'
#check add' 0 
#check add' 0 0 
-- #eval add' 0 0     -- does not work

/-
## Exercises
-/

-- x + 2 = x + 2
example (x : MyNat) : add' x 2 = add' x 2 := by
  rfl

-- a + (b + 0) + (c + 0) = a + b + c
example (a b c : MyNat) : add' a (add' (add' b 0) (add' c 0)) = add' a (add' b c) := by
  rw [add_zero', add_zero']

-- succ n = n + 1
lemma succ_eq_add_one' (n : MyNat) : succ n = add' n 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ']
  rw [add_zero']

-- 2 + 2 = 4
example : add' 2 2 = 4 := by
  nth_rw 2 [two_eq_succ_one]
  rw [add_succ']
  rw [one_eq_succ_zero]
  rw [add_succ']
  rw [add_zero']
  rfl


/-
But shouldn't all of these be *definitionally* equal? Something is off ...

## Defining Addition: Attempt #2
-/

def add (a b : MyNat) : MyNat :=
  match b with 
  | MyNat.zero => a                -- same as `axiom add_zero'`
  | MyNat.succ d => (add a d).succ -- same as `axiom add_succ'`

#eval add 2 3 

/-
## Exercises
-/

-- x + 2 = x + 2
example (x : MyNat) : add x 2 = add x 2 := by
  rfl

-- a + (b + 0) + (c + 0) = a + b + c
example (a b c : MyNat) : add a (add (add b 0) (add c 0)) = add a (add b c) := by
  rfl

-- succ n = n + 1
example (n : MyNat) : succ n = add n 1 := by
  rfl

-- 2 + 2 = 4
example : add 2 2 = 4 := by
  rfl

-- In fact, this is how it is done in mathlib
#check Nat.add_zero
#check Nat.add_succ


/-
## Using the `+` notation
-/

instance instAdd : Add MyNat where add := add

example : 2 + 2 = add 2 2 := rfl

lemma succ_eq_add_one (n : MyNat) : succ n = n + 1 := rfl

/-
## Comment

We can still prove and then use lemmas `add_zero` and `add_succ`
-/

lemma add_zero (a : MyNat) : a + 0 = a := rfl

lemma add_succ (a b : MyNat) : a + b.succ = (a + b).succ := rfl


/-
## Proof by induction on an inductive type
-/


-- 0 + n = n proved by induction on n
lemma zero_add (n : MyNat) : 0 + n = n := by
  induction' n with k ih
  · exact add_zero 0
  · rw [add_succ]
    rw [ih]

example (n : MyNat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [add_succ, ih]


/-
## Exercises
-/

-- succ n + m = succ (n + m)
lemma succ_add (n m : MyNat) : succ n + m = succ (n + m)  := by
  induction' m with k ih
  · rfl
  · rw [add_succ]
    rw [ih]
    rw [← add_succ] 

example (n m : MyNat) : succ n + m = succ (n + m)  := by
  induction' m with k ih
  · rfl
  · repeat rw [add_succ]
    rw [ih]

-- Commutativity of addition: n + m = m + n
lemma add_comm (n m : MyNat) : n + m = m + n := by
  induction' n with k ih
  · exact zero_add m
  · rw [add_succ, succ_add, ih]

example (n m : MyNat) : n + m = m + n := by
  induction' n with k ih
  · rw [← zero_eq_zero]
    rw [zero_add]
    rfl
  · rw [add_succ, succ_add, ih]
    
-- Associativity of addition: (n + m) + k = n + (m + k)
lemma add_assoc (n m k : MyNat) : (n + m) + k = n + (m + k) := by
  induction' k with l ih
  · rfl
  · rw [add_succ, add_succ, add_succ, ih]

example (n m k : MyNat) : (n + m) + k = n + (m + k) := by
  induction' n with l ih
  · rw [← zero_eq_zero, zero_add, zero_add]
  · rw [succ_add, succ_add, succ_add, ih]

example (n m k : MyNat) : (n + m) + k = n + (m + k) := by
  induction' m with l ih
  · rw [← zero_eq_zero, add_zero, zero_add]
  · rw [succ_add, add_succ, succ_add, add_succ, ih]

-- Right commutativity of addition: n + m + k = n + k + m
lemma add_right_comm (n m k : MyNat) : n + m + k = n + k + m := by
  rw [add_assoc]
  rw [add_comm m] -- or `rw [add_comm m k]` or `nth_rw 2 [add_comm]`
  rw [add_assoc]

example (n m : MyNat) (h : succ (n + 37) = succ (m + 42)) : n + 37 = m + 42 := by 
  exact succ_inj h 

example (n m : MyNat) (h1 : n = 37) (h2 : n = 37 → m = 42) : m = 42 := by
  exact h2 h1

example (n : MyNat) (h : n + 1 = 4) : n = 3 := by
  -- rw [← succ_eq_add_one] at h
  -- rw [four_eq_succ_three] at h
  exact succ_inj h 

example (n m : MyNat) (h1 : n = m) (h2 : n ≠ m) : False := by
  contradiction

example (n m : MyNat) (h1 : n = m) (h2 : n ≠ m) : False := h2 h1
