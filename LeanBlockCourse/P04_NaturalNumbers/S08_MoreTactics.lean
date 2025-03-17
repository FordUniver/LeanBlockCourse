/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse.P04_NaturalNumbers.S07_AdvancedMultiplications

namespace MyNat

/-
## Introductory exercise
-/

example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  sorry
