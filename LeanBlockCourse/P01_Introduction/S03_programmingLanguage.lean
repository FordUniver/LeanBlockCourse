/-
# Introduction to Lean as a Programming Language
=====================

## Basic Values and Printing
In Lean, we declare values using `def`. The type can be inferred or explicitly stated.
-/

-- Basic Hello World
def hello : String := "Hello, World!"
#check hello -- #check shows the type of something

def hello2 := "Hello, World!"
#check hello2

/-
Compare with:
Python: message = "Hello, World!"    # Dynamic typing
C:      const char* hello = "Hello, World!";  # Static typing
-/

def printHello : IO Unit := -- Explicit type for IO operation
  IO.println hello

#check printHello -- tells us it is of typoe IO Unit
#eval printHello -- actually executes it and prints "Hello, World!"


/-
## Basic Arithmetic
Lean uses natural numbers (Nat) by default for integers. Functions can be defined
with explicit type annotations, similar to C but with a different syntax.
-/

def add (x y : Nat) : Nat := x + y

/-
Compare with:
Python: def add(x, y): return x + y
C:      int add(int x, int y) { return x + y; }
-/

#check add -- Nat (x) → Nat (y) → Nat (output)

#check add 2 3 -- Nat
#eval add 2 3 -- 5

#check add 0 -- partial binding works! Nat (y) → Nat (output)
-- #eval add 0 --

def triple_multiply (x y z : Nat) : Nat := x * y * z

#eval triple_multiply 2 3 4
#check triple_multiply -- Nat (x) → Nat (y) → Nat (z) → Nat (output)


/-
## Pattern Matching and Control Flow
Lean uses pattern matching as its primary control flow mechanism. This is more
powerful than traditional if/switch statements found in C or Python.
-/

def calculator (op : String) (x y : Nat) : Nat :=
  match op with
  | "+" => add x y -- or directly x + y
  | "-" => x - y
  | "*" => x * y
  | _ => 0 -- default case

/-
Compare with:
Python:
def calculator(op, x, y):
    if op == "+": return x + y
    elif op == "-": return x - y
    elif op == "*": return x * y
    else: return 0

C:
int calculator(char* op, int x, int y) {
    if (strcmp(op, "+") == 0) return x + y;
    else if (strcmp(op, "-") == 0) return x - y;
    else if (strcmp(op, "*") == 0) return x * y;
    else return 0;
}
-/

#eval calculator "*" 2 3
#check calculator -- String (op) → Nat (x) → Nat (y) → Nat (output)



/-
## String Interpolation
Lean provides string interpolation similar to modern programming languages.
-/

def greeting (name : String) : String :=
  s!"Hello, {name}!"

#eval greeting "Martin"
#check greeting -- String (name) → String (output)
#check greeting "Martin" -- String (output)


/-
## Type Inference
Lean has a powerful type inference system that can automatically determine types in many cases.
This makes code more concise while maintaining type safety. The compiler will infer the most
general type that satisfies the constraints.
-/

-- Type inference for simple values
def inferredNumber := 42        -- Inferred as Nat
def inferredText := "Hello"     -- Inferred as String
def inferredList := [1, 2, 3]   -- Inferred as List Nat

#check inferredList


-- Type inference for functions
def inferredAdd (x : Nat) y := x + y -- type of `y` and of output is inferred as `Nat`
def inferredConcat (x : String) y := x ++ y -- type of `y` and output is inferred as `String`



-- Sometimes explicit types are clearer or necessary
def explicitSubNat (x y : Nat) := x - y  -- Forces `Nat` arithmetic
#check explicitSubNat -- Nat (x) → Nat (y) → Nat (output)
#check explicitSubNat 2 3 -- Nat (output)
#eval explicitSubNat 2 3 -- 2 - 3 = 0 in Nat

def explicitSubInt (x y : Int) := x - y
#check explicitSubInt 2 3 -- Int (output)
#eval explicitSubInt 2 3 -- 2 -3 = -1 in Int

-- def explicitSub (x y) := x - y -- unable to infer type
-- def explicitSub (x y) : Int := x - y -- unable to infer type
def explicitSub (x : Int) y := x - y -- able to infer Int for y and output


/-
Compare with:
Python: Type hints are optional
def add(x, y):  # No types needed
    return x + y

TypeScript: Type inference with explicit options
let inferredNumber = 42;  // number
let explicitNumber: number = 42;
-/


/-
## Data Structures
Lean provides several ways to structure data. Here we demonstrate:
1. Simple structures (similar to C structs or Python classes)
2. Namespace organization
3. Method-like function definitions
-/

-- Basic structure definition
structure Point where
  x : Float
  y : Float
deriving Repr

/-
Compare with:
Python:
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y

C:
struct Point {
    double x;
    double y;
};
-/

def π : Float := 3.14159265358979323846

structure Rectangle where
  width : Float
  height : Float
deriving Repr

def Rectangle.area (r : Rectangle) : Float :=
  r.width * r.height

def myRectangle : Rectangle := { width := 4.0, height := 2.0 }

#eval myRectangle.area

def Rectangle.perimerter (r : Rectangle) : Float :=
  2.0 * (r.width + r.height)

-- Circle demonstrates namespace approach
structure Circle where
  center : Point
  radius : Float
deriving Repr

namespace Circle
  -- putting this into the namespace has the same effect
  -- as naming it Circle.area
  def area (c : Circle) : Float :=
    π * c.radius * c.radius

  def circumference (c : Circle) : Float :=
    2.0 * π * c.radius

  def containsPoint (c : Circle) (p : Point) : Bool :=
    let dx := c.center.x - p.x
    let dy := c.center.y - p.y
    dx * dx + dy * dy ≤ c.radius * c.radius
end Circle

def myCircle : Circle := {
  center := { x := 1.0, y := 1.0 }
  radius := 2.5
}

#eval myCircle                -- Shows the full structure
#eval myCircle.area          -- Calculates area
#eval myCircle.circumference -- Calculates circumference
#eval myCircle.containsPoint { x := 2.0, y := 2.0 }  -- Tests point containment


/-
-------------------------------------------------------------
## Propositions as Types – A Glimpse into Proofs in Lean

In Lean, every proposition is just a type, and a proof is a value (or term) of that type.
This is the essence of the propositions-as-types (or Curry–Howard) correspondence.
In other words, proving a proposition amounts to constructing a term that inhabits the type
representing that proposition.
-------------------------------------------------------------
-/

-- This function claims it returns a Nat
def t1 : Nat := 0 -- putting a string here would be a type error

#check t1 -- Nat
#eval t1 -- 0

def t2 (n : Nat) : Nat := n

def t2' (n : Nat) : Nat := 0

def t3 (T : Type) (n : T) : T := n

-- Nat is an example of T
example : t3 Nat = t2 := by
  rfl

-- This does not work because not only the type is checked (Nat)
-- but also the specific instance, which is not the same (0 != n)
-- example : t3 Nat = t2' := by
--   rfl

-- A constructive proof of the type of the statement `P → P`
def t4 (P : Prop) (p : P) : P := p

def t5 (P : Prop) (p : P) : P := by exact p -- same proof


-- Three proof of P ∧ Q → P

-- For return types of "parent type" `Prop` we usually write
-- `theorem` or `lemma` (or `example` if it is unnamed)
theorem t6 (P Q : Prop) : P ∧ Q → P := fun ⟨p, q⟩ => p -- an actual proof

-- We can explicitly emphasize that P ∧ Q → P is of type Prop
theorem t6' (P Q : Prop) : (P ∧ Q → P : Prop) := fun ⟨p, q⟩ => p

-- This complains about a type mismatch!
--
-- type mismatch
--   q
-- has type
--   Q : Prop
-- but is expected to have type
--   P : Prop
--
-- theorem t6' (P Q : Prop) : P ∧ Q → P := fun ⟨p, q⟩ => q

theorem t7 (P Q : Prop) : P ∧ Q → P := by sorry -- sorry skips the proof but type checker is happy

axiom t8 (P Q : Prop) : P ∧ Q → P -- no proof required for axioms!

-- Lean accepts all of these as instanciations of the type `P ∧ Q → P`
#check t6 -- Prop → Prop → (P ∧ Q → P)
#check t7 -- Prop → Prop → (P ∧ Q → P)
#check t8 -- Prop → Prop → (P ∧ Q → P)

-- This works because Prop is a special type:
-- only the fact that it is inhabited (true) matters!
example (P Q : Prop) : t6 P Q = t8 P Q := by rfl
