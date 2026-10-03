module

public import BondalThomsen.Fan.Parallel
public import BondalThomsen.Fan.Rank
public import BondalThomsen.Matroid.SeriesParallelEdgeBound
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

open Finset Module

namespace BondalThomsen

structure ConnectedGraphCountWitness {Ground : Type*} (matroid : Matroid Ground)
    (Vertex : Type*) [Fintype Vertex] where
  graph : SimpleGraph Vertex
  decidableAdj : DecidableRel graph.Adj
  connected : graph.Connected
  two_degenerate : GraphDegeneracy.IsTwoDegenerate graph
  ground_card : Nat.card matroid.E = Nat.card graph.edgeSet
  rank_eq : matroid.eRank.toNat = Fintype.card Vertex - 1

structure ComponentGraphCountWitness {Ground : Type*} (matroid : Matroid Ground)
    (Component : Type*) [Fintype Component] (Vertex : Component → Type*)
    [∀ component, Fintype (Vertex component)] where
  graph : ∀ component, SimpleGraph (Vertex component)
  decidableAdj : ∀ component, DecidableRel (graph component).Adj
  connected : ∀ component, (graph component).Connected
  two_degenerate : ∀ component, GraphDegeneracy.IsTwoDegenerate (graph component)
  ground_card : Nat.card matroid.E = ∑ component, Nat.card (graph component).edgeSet
  rank_eq : matroid.eRank.toNat = ∑ component, (Fintype.card (Vertex component) - 1)

end BondalThomsen

