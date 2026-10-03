module

public import BondalThomsen.Matroid.ConnectedMatroidForestReconstruction
public import BondalThomsen.DeepFan.ConnectedComponents
public import BondalThomsen.Rarity.UnlabeledMatroidTreeCounting

@[expose] public section

open scoped Classical

namespace TauCeti.Toric.Fan

open Module BondalThomsen Set

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem rayMatroid_ground_nonempty_of_positive_dimension
    (fan : Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin dimension) ℤ Lattice) (positive_dimension : 0 < dimension) :
    fan.rayMatroid.E.Nonempty := by
  by_contra empty
  have ground_empty := Set.not_nonempty_iff_eq_empty.mp empty
  have rank_bound := fan.rayMatroid.eRank_le_encard_ground
  rw [ground_empty, Set.encard_empty,
    fan.rayMatroid_eRank_of_complete_regular complete regular reference] at rank_bound
  have zero_dimension : dimension = 0 := by exact_mod_cast (le_zero_iff.mp rank_bound)
  omega

end TauCeti.Toric.Fan
