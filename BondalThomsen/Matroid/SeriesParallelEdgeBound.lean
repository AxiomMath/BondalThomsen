module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

open Finset

namespace BondalThomsen.GraphDegeneracy

universe vertexUniverse

noncomputable def neighborsWithin {Vertex : Type*} (graph : SimpleGraph Vertex)
    (vertices : Finset Vertex) (vertex : Vertex) : Finset Vertex := by
  classical
  exact vertices.filter (graph.Adj vertex)

def IsDegenerate {Vertex : Type*} (bound : ℕ) (graph : SimpleGraph Vertex) : Prop :=
  ∀ vertices : Finset Vertex, vertices.Nonempty →
    ∃ vertex ∈ vertices, (neighborsWithin graph vertices vertex).card ≤ bound

abbrev IsTwoDegenerate {Vertex : Type*} (graph : SimpleGraph Vertex) : Prop :=
  IsDegenerate 2 graph

end BondalThomsen.GraphDegeneracy
