module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

@[expose] public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {v : ι}

structure IsCone (K : PreAbstractSimplicialComplex ι) (v : ι) : Prop where

  apex_mem : ({v} : Finset ι) ∈ K

  insert_mem : ∀ ⦃σ : Finset ι⦄, σ ∈ K → insert v σ ∈ K

end PreAbstractSimplicialComplex
