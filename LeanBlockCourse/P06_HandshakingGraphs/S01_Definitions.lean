import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import LeanBlockCourse.ToMathlib.EdgeFinset

/-
Blackboard definition of a graph
--------------------------------

A graph G = (V, E) consists of a vertex set V
and an edge set E ⊆ {{u, v} | u, v ∈ V, u ≠ v}


mathlib definition of a graph
-----------------------------

structure SimpleGraph (V : Type u) where
  Adj : V → V → Prop
  symm : Symmetric Adj := by aesop_graph
  loopless : Irreflexive Adj := by aesop_graph
-/

#check SimpleGraph

def triangle : SimpleGraph (Fin 3) := {
  Adj := fun v₁ v₂ => v₁ ≠ v₂
  symm := by aesop_graph
  loopless := by aesop_graph
}

/-
Biggest differences:

- We have a vertex type V instead of a vertex set V
- We have a symmetric and loopless adjacency notion
  instead of an edge set E ⊆ {{u, v} | u, v ∈ V, u ≠ v}

Note that neither of the above definitions requires V
to be finite!
-/

-- A graph is finite if the underlying vertex type is finite
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {v : V}

-- edges are somewhat inconveniently of type `Sym2 V`
#check G.edgeSet             -- Set (Sym2 V)
#check G.edgeFinset          -- Finset (Sym2 V)

local notation "E" => G.edgeFinset
#check E                     -- Finset (Sym2 V)
example : E = G.edgeFinset := rfl

-- the incidence set `I(v) = {e ∈ E | v ∈ e}`
#check G.incidenceSet v      -- Set (Sym2 V)
#check G.incidenceFinset v   -- Finset (Sym2 V)

local notation "I(" v ")" => G.incidenceFinset v
#check I(v)
example : I(v) = G.incidenceFinset v := rfl

-- the neighborhood `N(v) = {v' ∈ V | v ~ v'}`
#check G.neighborSet v       -- Set V
#check G.neighborFinset v    -- Finset V

local notation "N(" v ")" => G.neighborFinset v
#check N(v)
example : N(v) = G.neighborFinset v := rfl

-- the degree `d(v) = #N(v)`
#check G.degree v            -- ℕ

local notation "d(" v ")" => G.degree v
#check d(v)
example : d(v) = G.degree v := rfl



/-
# Exercises
-/

open Finset

-- 1) Define the graph we had on the blackboard with four vertices and three edges.
def blackboard_graph : SimpleGraph (Fin 4) := {
  Adj := fun v₁ v₂ => (v₁ = 1 ∧ v₂ = 2) ∨ (v₁ = 1 ∧ v₂ = 3) ∨ (v₁ = 2 ∧ v₂ = 3) ∨
                      (v₁ = 2 ∧ v₂ = 1) ∨ (v₁ = 3 ∧ v₂ = 1) ∨ (v₁ = 3 ∧ v₂ = 2)
  -- symm : Symmetric Adj := by aesop_graph -- this it figures out automatically!
  loopless := by
    rintro v' (h | h | h | h | h | h)
    all_goals obtain ⟨h', h''⟩ := h; rw [h'] at h''; contradiction
}

#eval (1 : Fin 4)
#eval (2 : Fin 4)
#eval (3 : Fin 4)
#eval (4 : Fin 4)

#eval (1 : Fin 4).val
#eval (2 : Fin 4).val
#eval (3 : Fin 4).val
#eval (4 : Fin 4).val



def blackboard_graph_alt : SimpleGraph (Fin 4) := {
  Adj := fun v₁ v₂ => v₁ ≠ v₂ ∧ v₁ ≠ 4 ∧ v₂ ≠ 4 -- Careful: either `v1 ≠ 4` or `v₁.val ≠ 0` but NOT `v₁.val ≠ 4`
  -- symm : Symmetric Adj := by aesop_graph -- this it figures out automatically!
  -- loopless : Symmetric Adj := by aesop_graph -- this it figures out automatically!
}

-- 2) Show that the degree is the cardinality of the incidence set
example : d(v) = #I(v) := (G.card_incidenceFinset_eq_degree v).symm

-- 3) Show that the incidence set is the set of all incident edges
example : I(v) = {e ∈ E | v ∈ e} := G.incidenceFinset_eq_filter v

-- 4) Show that an edge consists of two vertices
example (e : Sym2 V) (h : e ∈ E) : #{v | v ∈ e} = 2 :=
  SimpleGraph.card_filter_mem_of_mem_edgeFinset e h

example (e : Sym2 V) (h : e ∈ E) : #{v | v ∈ e} = 2 := by
  obtain ⟨v₁, v₂⟩ := e
  simp_all

  -- Side remarks:
  -- 1) `Finset.univ` is the set of all elements of a given type
  -- 2) `Finset.filter (P : α → Prop) (S : Finset α)` filters the set `S` according to `P`
  -- 3) `{s ∈ S | P s}` is just notation for `Finset.filter (P : α → Prop) (S : Finset α)`
  -- 4) `Finset.univ {α : Type u_1} [Fintype α]` has two hidden arguments (one implicit
  --    and one a type class), so if you need to explicitly construct it, you need to
  --    usually use `@univ α _`, where `@` makes every argument explicit but `_` still
  --    let's us infer the type class automatically
  ---
  -- have (x : V) : x ∈ @univ V _ := mem_univ x
  --
  -- have : (filter (fun v ↦ v = v₁ ∨ v = v₂) univ) =
  --       {v ∈ @univ V _ | v = v₁ ∨ v = v₂} := rfl

  have : (filter (fun v ↦ v = v₁ ∨ v = v₂) univ) = {v₁, v₂} := by ext x; simp_all
  rw [this]

  have : v₁ ≠ v₂ := (G.adj_symm h).ne'
  exact card_pair this














-- 1) Define the graph we had on the blackboard with four vertices and three edges.
-- def blackboard_graph

-- 2) Show that the degree is the cardinality of the incidence set
example : d(v) = #I(v) := by
  exact Eq.symm (SimpleGraph.card_incidenceFinset_eq_degree G v)

-- 3) Show that the incidence set is the set of all incident edges
example : I(v) = {e ∈ E | v ∈ e} := by
  exact SimpleGraph.incidenceFinset_eq_filter G v

-- 4) Show that an edge consists of two vertices
example (e : Sym2 V) (h : e ∈ E) : #{v | v ∈ e} = 2 := by
  obtain ⟨v₁, v₂⟩ := e
  simp_all

  have v1_ne_v2 : v₁ ≠ v₂ := (G.adj_symm h).ne'
  have v1_v2_card : #{v₁, v₂} = 2 := card_pair v1_ne_v2
  have : filter (fun v ↦ v = v₁ ∨ v = v₂) univ = {v₁, v₂} := by ext x; simp

  rw [this]
  assumption
