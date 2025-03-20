import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import LeanBlockCourse.ToMathlib.EdgeFinset
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-
State the following theorem in Lean:

The sum of the degrees of a finite graph is equal
to twice the number of edges.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

local notation "E" => G.edgeFinset
local notation "d(" v ")" => G.degree v
local notation "I(" v ")" => G.incidenceFinset v
local notation "N(" v ")" => G.neighborFinset v

open Finset

-- Remark: `∑ v` or `∑ v : V` but NOT `∑ v ∈ V` (`V` is a type!)
lemma handshaking : ∑ v, d(v) = 2 * #E := by
  let T := {(v, e) : V × (Sym2 V) | e ∈ E ∧ v ∈ e }.toFinset
  sorry
