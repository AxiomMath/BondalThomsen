module

public import BondalThomsen.Matroid.DeepK4Exclusion
public import BondalThomsen.DeepFan.Theorems
public import BondalThomsen.Fan.RayBound
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace BondalThomsen

open Module Set

universe groundUniverse

structure ComponentForestPresentation {Ground : Type groundUniverse} (matroid : Matroid Ground)
    where
  componentCount : ℕ
  vertexCount : Fin componentCount → ℕ
  graph : ∀ component, SimpleGraph (Fin (vertexCount component))
  connected : ∀ component, (graph component).Connected
  two_degenerate : ∀ component, GraphDegeneracy.IsTwoDegenerate (graph component)
  groundEquiv : matroid.E ≃ (component : Fin componentCount) × (graph component).edgeSet
  indep_iff : ∀ selected : Set Ground, selected ⊆ matroid.E →
    (matroid.Indep selected ↔ ∀ component,
      (SimpleGraph.fromEdgeSet (Subtype.val ''
        {edge : (graph component).edgeSet |
          (groundEquiv.symm ⟨component, edge⟩).val ∈ selected})).IsAcyclic)
  rank_eq : matroid.eRank.toNat = ∑ component, (vertexCount component - 1)

end BondalThomsen

namespace TauCeti.Toric.Fan

open Module Set BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem deep_minor_representable (fan : TauCeti.Toric.Fan embedding)
    {Field : Type*} [_root_.Field Field] {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) {smaller : Matroid fan.Ray}
    (minor : smaller ≤m fan.rayMatroid) : smaller.Representable Field :=
  (fan.deep_rayMatroid_representable (Field := Field) complete regular deep reference).of_isMinor
    minor

theorem deep_minor_no_isomorphic_k4 (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) {smaller : Matroid fan.Ray}
    (minor : smaller ≤m fan.rayMatroid) :
    ¬ ∃ candidate : Matroid fan.Ray,
      candidate ≤m smaller ∧ Nonempty (Matroid.Iso k4Matroid candidate) := by
  rintro ⟨candidate, candidate_minor, ⟨isomorphism⟩⟩
  exact no_isomorphic_k4_minor fan complete regular deep reference isomorphism
    (candidate_minor.trans minor)

end TauCeti.Toric.Fan
