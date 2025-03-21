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

example (v : V) : bipartiteAbove (fun v e => v ∈ e) E v = {e ∈ E | v ∈ e} := rfl

example (e : Sym2 V) : bipartiteBelow (fun v e => v ∈ e) univ e = {v ∈ @univ V _ | v ∈ e} := rfl

#check sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow


-- Remark: `∑ v` or `∑ v : V` but NOT `∑ v ∈ V` (`V` is a type!)
lemma handshaking : ∑ v, d(v) = 2 * #E := by
  calc ∑ v, d(v) = ∑ v, #{ e ∈ E | v ∈ e}  := by
                        apply Finset.sum_congr (rfl)
                        intro v hv
                        rw [← G.card_incidenceFinset_eq_degree v]
                        rw [G.incidenceFinset_eq_filter v]
               _ = ∑ e ∈ E, #{v | v ∈ e}    := by
                        exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow fun a b ↦ a ∈ b
               _ = ∑ e ∈ E, 2               := by
                        apply Finset.sum_congr (rfl)
                        intro e he
                        exact G.card_filter_mem_of_mem_edgeFinset e he
               _ = 2 * #E                   := by
                        rw [Finset.card_eq_sum_ones E]
                        exact (mul_sum E (fun i ↦ 1) 2).symm
