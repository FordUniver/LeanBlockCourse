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
  sorry

-- a + (b + 0) + (c + 0) = a + b + c
example (a b c : MyNat) : add' a (add' (add' b 0) (add' c 0)) = add' a (add' b c) := by
  sorry

-- succ n = n + 1
lemma succ_eq_add_one' (n : MyNat) : succ n = add' n 1 := by
  sorry

-- 2 + 2 = 4
example : add' 2 2 = 4 := by
  sorry
