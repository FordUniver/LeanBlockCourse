/-
This part is based on `Theorem Proving in Lean 4` by Jeremy Avigad, Leonardo
de Moura, Soonho Kong and Sebastian Ullrich:
https://leanprover.github.io/theorem_proving_in_lean4/
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Defs

/-
# Dependent Type Theory
=====================

Dependent type theory is a powerful language for expressing mathematical
assertions and specifications, where every expression has an associated
*type*. Lean uses a version called the *Calculus of Constructions*, with
a countable hierarchy of non-cumulative universes and inductive types.

## Fundamental Types

Lean a fundamental hierarchy of types:
-/

#check Prop 
#check Type 
#check Type 1

-- These can also be expressed as `Sort`
example : Prop = Sort 0 := rfl
example : Type = Sort 1 := rfl
example : Type 1 = Sort 2 := rfl


universe u -- universes define the sort
variable {α : Type u}


/-
## Inductive Types

Every concrete type in Lean's library (other than universes) and every type constructor 
(other than dependent arrows) is an instance of inductive types.
An inductive type is built from constructors. Basic syntax:
-/


namespace Hidden

inductive Weekday where
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
  | sunday : Weekday

#check Weekday
  
def monday := Weekday.monday

#check monday 


/-
We can define functions on inductive types using pattern matching:
-/

def numberOfDay (d : Weekday) : ZMod 7 :=
  match d with
  | Weekday.monday     => 1
  | Weekday.tuesday    => 2 
  | Weekday.wednesday  => 3
  | Weekday.thursday   => 4
  | Weekday.friday     => 5
  | Weekday.saturday   => 6
  | Weekday.sunday     => 7

#eval numberOfDay monday 

-- Some important types are defined as inductive types:
inductive True : Prop where
  | intro : True

inductive False : Prop

-- Note that `Bool` also exists as a built-in inductive type.
-- and that `true` and `false` are the two constructors.
inductive Bool : Type where
  | false : Bool
  | true : Bool


-- Even Eq is an inductive type.
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a


/-
## Building new types from existing types

We can build new types from existing ones:

- Function types: `a → b` (or `a -> b`) represents
  functions from type `a` to type `b`
- Product types: `a × b` represents pairs containing
  an element of `a` and an element of `b`
  -/ 

-- The arrow is a primitive concept
#check Type → Type      -- type the arrow as "\to" or "\r"
#check Type -> Type     -- alternative ASCII notation

#check Type → Type → Type
#check Type → (Type → Type)  --  same type as above

-- The product is a structure (more on this later)
#check Type × Type      -- type the product as "\times"
#check Prod Type Type   -- alternative notation

--  `Set α` is actually defined as `α → Prop`
#check Set α 

-- `List α` is defined as an inductive type
#check List α

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

-- `Or` is an inductive type
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

/-
## Structures

In Lean, a structure (or record) is a non-recursive inductive type with a single constructor.
-/

structure Point where
  x : Nat
  y : Nat
  deriving Repr

-- Creating values of type `Point Nat` using the constructor.
def p : Point := { x := 10, y := 20 }
def q : Point := Point.mk 5 8 -- we will see in a second why this works

#check Point          -- Point : Type u → Type u
#check Point.mk       -- Point.mk : {α : Type u} → α → α → Point α

#check p.x            -- p.x : Nat
#check q.y            -- q.y : Nat

#eval p.x            -- Expected output: 10
#eval q.y            -- Expected output: 8

-- We already saw that the product of two types is a structure!
-- Under the hood, structures are defined as inductive types

inductive InductivePoint where
  | mk (x : Nat) (y : Nat) : InductivePoint


-- Creating values of type `Point Nat` using the constructor.
def ind_p := InductivePoint.mk 10 20
def ind_q := InductivePoint.mk 5 8

#check InductivePoint          -- InductivePoint : Type u → Type u
#check InductivePoint.mk       -- InductivePoint.mk : {α : Type u} → α → α → InductivePoint α

-- Define projection functions
def InductivePoint.x (p : InductivePoint) : Nat :=
  match p with
  | InductivePoint.mk x _ => x

def InductivePoint.y (p : InductivePoint) : Nat :=
  match p with
  | InductivePoint.mk _ y => y

#check ind_p.x                 -- ind_p.x : Nat
#check ind_q.y                 -- ind_q.y : Nat

#eval ind_p.x                  -- Expected output: 10
#eval ind_q.y                  -- Expected output: 8


-- Some important examples of structures
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

end Hidden

/-
## A remark on tactics

Note that many tactics just wrap a `match` on an inductive type
-/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  obtain (p | q) := h
  · right; exact p
  · left; exact q

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl p => exact Or.inr p
  | inr q => exact Or.inl q

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P :=
  match h with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q 


/-
## Type Classes

Type classes are special kinds of structures that enable ad-hoc polymorphism.
By marking instances as implicit, Lean automatically synthesizes implementations
for a given type. This mechanism is widely used to define operations such as addition,
default (inhabited) values, and coercions.
-/



-- Approach 1: Define a structure for generic addition
namespace foo

structure Add (α : Type) where add : α → α → α

def double (s : Add α) (x : α) : α := s.add x x

-- We would need to tell `double` explicitly what addition to use every time we call it!

end foo


-- Approach 2: Define a class for generic addition
namespace bar

class Add (α : Type u) where add : α → α → α

-- Note the square brackets around `Add α`!
def double [Add α] (x : α) : α := Add.add x x

-- This tells lean that Nat has an addition
instance : Add Nat where add := Nat.add

#eval double 10

end bar

#check Add
