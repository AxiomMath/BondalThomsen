module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace TauCeti.SetLike

abbrev Face {ι S : Type*} [_root_.SetLike S (Finset ι)] (K : S) := {σ : Finset ι // σ ∈ K}

end TauCeti.SetLike

namespace PreAbstractSimplicialComplex

variable {ι : Type*} {K L : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

@[simp]
theorem mem_inf {ρ : Finset ι} : ρ ∈ K ⊓ L ↔ ρ ∈ K ∧ ρ ∈ L :=
  Iff.rfl

end PreAbstractSimplicialComplex

