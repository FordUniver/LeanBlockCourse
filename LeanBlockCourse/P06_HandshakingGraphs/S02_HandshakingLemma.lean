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










-- Remark: `∑ v` or `∑ v : V` but NOT `∑ v ∈ V` (`V` is a type!)
lemma handshaking : ∑ v, d(v) = 2 * #E := by
  let T := {(v, e) : V × (Sym2 V) | e ∈ E ∧ v ∈ e }.toFinset

  -- d(v) = ∑ e ∈ E, if v ∈ e then 1 else 0
  have deg_eq_I_card (v : V) : d(v) = #I(v) := (G.card_incidenceFinset_eq_degree v).symm

  have I_eq_filter (v : V) : I(v) = {e ∈ E | v ∈ e} := G.incidenceFinset_eq_filter v

  have filter_card_eq_sum (v : V)  : #{e ∈ E | v ∈ e} = ∑ e ∈ E, if v ∈ e then 1 else 0  := by
    exact card_filter (fun i ↦ v ∈ i) G.edgeFinset

  have deg_eq_sum (v : V) : d(v) = ∑ e ∈ E, if v ∈ e then 1 else 0 := by
    rw [deg_eq_I_card, I_eq_filter, filter_card_eq_sum]


  -- (∑ v, if v ∈ e then 1 else 0) = 2
  have edge_set_card_eq_two (e : Sym2 V) (h : e ∈ E) : #{v | v ∈ e} = 2 :=
    SimpleGraph.card_filter_mem_of_mem_edgeFinset e h

  have edge_set_card_eq_edge_sum  (e : Sym2 V) : #{v | v ∈ e} = (∑ v, if v ∈ e then 1 else 0) :=
    card_filter (Membership.mem e) univ

  have edge_sum_eq_two (e : Sym2 V) (h : e ∈ E) : (∑ v, if v ∈ e then 1 else 0) = 2 := by
    rw [← edge_set_card_eq_two e h, edge_set_card_eq_edge_sum e]


  -- 2 * #E = ∑ e ∈ E, (∑ v, if v ∈ e then 1 else 0)
  have sum_vert_eq_T_card : ∑ v, (∑ e ∈ E, if v ∈ e then 1 else 0) = #T := by sorry

  have sum_edge_eq_T_card : ∑ e ∈ E, (∑ v, if v ∈ e then 1 else 0) = #T := by sorry

  have : ∑ v, (∑ e ∈ E, if v ∈ e then 1 else 0) = ∑ e ∈ E, (∑ v, if v ∈ e then 1 else 0) := by sorry

  have (v : V) : ∑ e ∈ E, if v ∈ e then 1 else 0 = #{e ∈ E | v ∈ e}  := by sorry

  have (e : Sym2 V):  (∑ v, if v ∈ e then 1 else 0) =  #{v | v ∈ e} :=
    Eq.symm (card_filter (Membership.mem e) univ)

  have sum_vert_eq_sum_edge : ∑ v, #{e ∈ E | v ∈ e} = ∑ e ∈ E, #{v | v ∈ e} :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow fun a b ↦ a ∈ b


  calc ∑ v, d(v)
  _ = ∑ v, (∑ e ∈ E, if v ∈ e then 1 else 0) := by simp [deg_eq_sum]
  _ = #T := sum_vert_eq_T_card
  _ = ∑ e ∈ E, (∑ v, if v ∈ e then 1 else 0) := sum_edge_eq_T_card.symm
  _ = ∑ e ∈ E, 2 := sum_congr rfl edge_sum_eq_two
  _ = 2 * ∑ e ∈ E, 1 := (mul_sum G.edgeFinset (fun i ↦ 1) 2).symm
  _ = 2 * #E := by rw [card_eq_sum_ones E]
