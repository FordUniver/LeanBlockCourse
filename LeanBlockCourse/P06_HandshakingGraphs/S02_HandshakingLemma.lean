import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import LeanBlockCourse.ToMathlib.EdgeFinset

/-
State the following theorem in Lean:

The sum of the degrees of a finite graph is equal
to twice the number of edges.
-/

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

local notation "E" => G.edgeFinset
local notation "d(" v ")" => G.degree v
local notation "I(" v ")" => G.incidenceFinset v
local notation "N(" v ")" => G.neighborFinset v

open Finset

-- Remark: `∑ v` or `∑ v : V` but NOT `∑ v ∈ V` (`V` is a type!)
lemma handshaking : ∑ v, d(v) = 2 * #E := by
  sorry






















variable {α : Type*} [Fintype α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

local notation "E" => G.edgeFinset
local notation "d(" v ")" => G.degree v
local notation "I(" v ")" => G.incidenceFinset v
local notation "N(" v ")" => G.neighborFinset v

open Finset

lemma handshaking : ∑ v, d(v) = 2 * #E := by sorry
