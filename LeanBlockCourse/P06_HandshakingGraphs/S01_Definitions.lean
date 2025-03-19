import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite


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
-- def blackboard_graph

-- 2) Show that the degree is the cardinality of the incidence set
example : d(v) = #I(v) := by
  sorry

-- 3) Show that the incidence set is the set of all incident edges
example : I(v) = {e ∈ E | v ∈ e} := by
  sorry

-- 4) Show that an edge consists of two vertices
example (e : Sym2 V) (h : e ∈ E) : #{v | v ∈ e} = 2 := by
  sorry
