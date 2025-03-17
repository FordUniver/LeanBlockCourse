/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse.P04_NaturalNumbers.S07_AdvancedMultiplication

set_option trace.Meta.Tactic.simp true
namespace MyNat

/-
## Introductory exercise
-/

lemma add_left_comm (a b c : MyNat) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc]
  rw [add_comm a b]
  rw [add_assoc]

example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  repeat rw [add_assoc]
  rw [add_comm d]; repeat rw [add_assoc]
  rw [add_comm f]; repeat rw [add_assoc]
  rw [add_comm h]; repeat rw [add_assoc]
  rw [add_comm c]; repeat rw [add_assoc]
  rw [add_comm g]; repeat rw [add_assoc]
  rw [add_comm e]; repeat rw [add_assoc]
  rw [add_comm d]; repeat rw [add_assoc]
  sorry
  
example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  repeat rw [← add_assoc]
  nth_rw 6 [add_comm]; repeat rw [← add_assoc]
  nth_rw 3 [add_comm]; repeat rw [← add_assoc]
  nth_rw 5 [add_comm]; repeat rw [← add_assoc]
  nth_rw 2 [add_comm]; repeat rw [← add_assoc]
  nth_rw 4 [add_comm]; repeat rw [← add_assoc]
  nth_rw 2 [add_comm]; repeat rw [← add_assoc]
  nth_rw 1 [add_comm]; repeat rw [← add_assoc]
  nth_rw 1 [add_comm]; repeat rw [← add_assoc] 


example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  repeat rw [add_assoc]
  repeat (rw [add_comm d]; repeat rw [add_assoc])
  repeat (rw [add_comm f]; repeat rw [add_assoc])
  repeat (rw [add_comm h]; repeat rw [add_assoc])
  repeat (rw [add_comm c]; repeat rw [add_assoc])
  repeat (rw [add_comm g]; repeat rw [add_assoc])
  repeat (rw [add_comm e]; repeat rw [add_assoc])

example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  repeat rw [add_assoc] 
  repeat rw [add_left_comm _ g] 
  repeat rw [add_left_comm _ f]
  repeat rw [add_left_comm _ d] 
  repeat rw [add_left_comm _ e]
  rw [add_comm _ h]
  repeat rw [add_left_comm _ h]
  rw [add_comm _ c] 

/-
## The `simp` tactic

Having to rearrange variables manually using commutativity and
associativity is very tedious. Lean's simplifier, `simp`, is "`rw` on steroids". It will rewrite every lemma
tagged with `simp` and every lemma fed to it by the user, as much as it can.

Furthermore, it will attempt to order variables into an internal order if fed
lemmas such as `add_comm`, so that it does not go into an infinite loop.
-/

-- simp will use tagged lemmas and anything supplied in the brackets
example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp [add_assoc, add_comm, add_left_comm]    

-- you can limit simp to only lemmas that you are supplying
example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_comm, add_left_comm]    

-- We can also tag lemmas with `simp` to make them simp lemmas.
attribute [simp] add_assoc add_comm add_left_comm mul_one

example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp

-- You can also incorporate 'local' hypotheses or just use `simp_all`
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  simp [p, q] 

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  simp_all



/-
## The `calc` tactic for chaining equalities

The `calc` tactic allows us to write proofs of (in)equalities as a sequence of
steps, where each step follows from the previous one.
-/


-- Basic example: using calc with addition
example (a b c : MyNat) : a + (b + c) = b + (a + c) := by
  calc
    a + (b + c) = (a + b) + c   := (add_assoc a b c).symm
    _           = (b + a) + c   := by nth_rw 4 [add_comm]
    _           = b + (a + c)   := add_assoc b a c 


/-
## Using calc with inequalities

The calc tactic also works with transitive relations like ≤.
Here we show how to chain inequalities using calc.
-/

-- Need to establish that ≤ is transitive
instance : Trans (@LE.le MyNat MyNat.instLE) (@LE.le MyNat MyNat.instLE) (@LE.le MyNat MyNat.instLE) where
  trans {_ _ _} h₁ h₂ := le_trans h₁ h₂

-- Basic inequality chaining
example (n m k : MyNat) (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  calc
    n ≤ m := hnm
    _ ≤ k := hmk 


/-
## Exercises
-/

-- Distributive law with calc
example (a b : MyNat) : a * (1 + b) = a + a * b := by
  calc a * (1 + b)   = a * 1 + a * b   := mul_add a 1 b
  _                  = a + a * b       := by simp

#check Nat.mul_one

-- Rearranging terms using calc
example (a b c : MyNat) : (a + b) + (b + c) = (b + b) + (a + c) := by
  calc (a + b) + (b + c) = a + (b + (b + c))      := by exact add_assoc a b (b + c) 
                       _ = a + ((b + b) + c)      := by rw [add_assoc]
                       _ = (b + b) + (a + c)      := add_left_comm a (b + b) c

example (a b c : MyNat) : (a + b) + (b + c) = (b + b) + (a + c) := by
  simp 
  
