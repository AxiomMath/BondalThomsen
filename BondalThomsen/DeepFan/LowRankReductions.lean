module

public import BondalThomsen.Matroid.Binary.RankFourCoverage
public import BondalThomsen.DeepFan.Classification
public import BondalThomsen.Matroid.Binary.MarkedRankFour

@[expose] public section

namespace TauCeti.Toric.Fan

open Module Set BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem deep_minor_no_graph_k4 (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) {smaller : Matroid fan.Ray}
    (minor : smaller ≤m fan.rayMatroid) :
    ¬ ∃ candidate : Matroid fan.Ray, candidate ≤m smaller ∧
      Nonempty (Matroid.Iso k4GraphCycleMatroid candidate) := by
  rintro ⟨candidate, candidate_minor, ⟨isomorphism⟩⟩
  exact fan.deep_minor_no_isomorphic_k4 complete regular deep reference minor
    ⟨candidate, candidate_minor, ⟨k4Matroid_iso_graphCycleMatroid.trans isomorphism⟩⟩

end TauCeti.Toric.Fan
