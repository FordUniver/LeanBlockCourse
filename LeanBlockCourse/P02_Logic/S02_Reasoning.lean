/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic

/-
# Reasoning Tactics
=====================

After learning the basic building blocks, we now look at two complementary styles of reasoning:

Forward reasoning:
- `have`: introduce new facts from existing ones

Backward reasoning:
- `apply`: transform goals using implications
- `suffices`: introduce a fact and use it to rewrite the goal
- `refine`: a version of `exact` that permits placeholders
-/



/-
## Forward Reasoning with `have`

The `have` tactic introduces new facts derived from existing ones.
It's useful for breaking down complex proofs into steps and is
used around 30,000 times in mathlib.
-/

-- Using have to build up facts step by step
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  have q : Q := h₁ p -- this is term mode, `by exact h₁ p` would have also worked (tactic mode)
  have r : R := h₂ q
  exact r 

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := h₂ (h₁ p)


/-
## Backward Reasoning with `apply`

The `apply` tactic works backward from the goal, reducing it to simpler subgoals.
If we want to prove `Q` and we have `h : P → Q`, then `apply h` changes the goal
from `Q` to `P`. This tactic is used around 17,000 times in mathlib.
-/

-- The same proof using apply to work backward
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  apply h₂      -- To prove R, it suffices to prove Q
  apply h₁      -- To prove Q, it suffices to prove P
  exact p       -- We have P directly



/-
## Exercise: Graph of Implications

This exercise demonstrates how forward and backward reasoning can lead to very
different-looking proofs of the same fact. Consider the following graph of implications:

A - f -> B <- g - C
|        |        |
h        i        j
|        |        |
v        v        v
D <- k - E - l -> F
^        ^        |
|        |        p
m        n        |
|        |        v
G <- q - H - r -> I

Find a path from `A` to `I` using different reasoning styles.
-/

-- Forward reasoning with have: start from `A` and build towards `I`
example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := by
  sorry

-- Backward reasoning with apply: start from I and work back to A
example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := by
  sorry
