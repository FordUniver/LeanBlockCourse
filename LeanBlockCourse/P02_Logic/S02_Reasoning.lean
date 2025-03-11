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
  have b : B := f a
  have e : E := i b
  have f : F := l e
  have i : I := p f
  exact i

-- Forward reasoning through term mode: start from `A` and build towards `I`
example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := p <| l <| i <| f a

-- Backward reasoning with apply: start from `I` and work back to `A`
example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := by
  apply p
  apply l
  apply i
  apply f
  exact a

-- mixed reasoning: argue backwards from `I` to `E` and then forwards from `A`
example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := by
  apply p
  apply l
  exact i (f a)

/-
## Forgetting about assumptions with `clear`

The `clear` tactic lets you forget assumptions. You should generally not need 
this and instead structure your code to only have necessary assumptions in scope.
-/

example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := by
  clear g h j k m n q r
  exact p <| l <| i <| f a
  

/-
## The `suffices` Tactic

Enables explicit backward reasoning by declaring intermediate goals:

1. Declares a subgoal that would suffice to prove the original goal
2. Once proven, provides access to the subgoal proof via `this`
3. Maintains goal context for clearer proof structuring

This tactic is used around 2,600 times in mathlib.
-/

-- Basic suffices example showing goal transformation
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  suffices Q by
    exact h₂ this
  exact h₁ p

-- Compare with equivalent apply
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  apply h₂
  exact h₁ p

-- Using suffices with named hypothesis so you are using `q` instead of `this`
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  suffices q : Q by
    exact h₂ q
  exact h₁ p


/-
## The `refine` Tactic

The `refine` tactic behaves like `exact` but permits placeholders (i.e. `?_`)
in the provided term. Any unsolved hole that is not fixed by unification with
the main goal's target is converted into a new goal. This tactic is used
around 19,000 times in mathlib.
-/

-- Example using `refine`
example (P Q : Prop) (f : P → Q) (p : P) : Q := by
  refine f ?_ -- in this case it behaves like `apply`
  exact p -- this answers a sub-goal raised `_?`

example (P Q : Prop) (f : P → Q) (p : P) : Q := by
  refine f p -- in this case it behaves like `exact`

-- You can also stack proofs inside proofs
-- Example using `refine`
example (P Q : Prop) (f : P → Q) (p : P) : Q := by
  refine f (by
    exact p)

example (P Q : Prop) (f : P → Q) (p : P) : Q := by
  exact f (by
    exact p)


/-
## Exercise: Graph of Implications (Continued)
-/

-- Use only `suffices` to work backwards from the goal:
example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := by 
  suffices F by exact p this
  suffices e : E by exact l e
  suffices B by exact i this
  exact f a

-- Use only `refine` to work backwards from the goal:
example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := by
  refine p ?_
  refine l ?_
  refine i ?_
  refine f ?_
  exact a

-- Do a proof that comines `clear`, `exact`, `have`, `suffices`, `refine`, and `apply`
example (A B C D E F G H I : Prop) 
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) 
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) 
    (q : H → G) (r : H → I) (a : A) : I := by 
  clear g
  apply p
  suffices E by exact l this
  refine i ?_
  have b : B := f a
  exact b
