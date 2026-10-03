module

public import BondalThomsen.Ports.TauCeti.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Fin.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicTopology.SimplicialComplex.IsCone

@[expose] public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

def simplex (V : Finset ι) : _root_.PreAbstractSimplicialComplex ι where
  faces := {σ | σ.Nonempty ∧ σ ⊆ V}
  isRelLowerSet_faces := by
    rintro σ ⟨hσ, hσV⟩
    exact ⟨hσ, fun _ hτσ hτ => ⟨hτ, hτσ.trans hσV⟩⟩

end PreAbstractSimplicialComplex

