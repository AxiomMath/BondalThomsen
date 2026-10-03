module

public import BondalThomsen.Matroid.Binary.SeriesParallelCountRecursion
public import BondalThomsen.DeepFan.LowRankReductions

@[expose] public section

namespace BondalThomsen

universe groundUniverse

def BinaryK4ExcludedElementaryReducibility (Ground : Type groundUniverse) : Prop :=
  ∀ matroid : Matroid Ground, matroid.Finite → matroid.Representable (ZMod 2) →
    (¬ ∃ forbidden : Matroid Ground, forbidden ≤m matroid ∧
      Nonempty (Matroid.Iso k4GraphCycleMatroid forbidden)) → matroid.E.Nonempty →
    ∃ reduced, Matroid.ElementarySeriesParallelReduction matroid reduced

end BondalThomsen

namespace Matroid

open BondalThomsen Set

variable {Ground : Type*} {source : Matroid Ground}

theorem binary_k4_excluded_complete_trace_of_elementary_reducibility
    (reducibility : BinaryK4ExcludedElementaryReducibility Ground)
    [source.Finite] (binary : source.Representable (ZMod 2))
    (excluded : ¬ ∃ forbidden : Matroid Ground, forbidden ≤m source ∧
      Nonempty (Iso k4GraphCycleMatroid forbidden)) :
    SeriesParallelReductionTrace source (emptyOn Ground) source.E.ncard := by
  obtain ⟨target, empty, trace⟩ := reduction_trace_of_minor_closed_reducibility
    (matroid := source) (fun candidate => candidate.Representable (ZMod 2) ∧
      ¬ ∃ forbidden : Matroid Ground, forbidden ≤m candidate ∧
        Nonempty (Iso k4GraphCycleMatroid forbidden))
    (by
      intro candidate reduced member minor
      refine ⟨member.1.of_isMinor minor, ?_⟩
      rintro ⟨forbidden, forbidden_minor, isomorphism⟩
      exact member.2 ⟨forbidden, forbidden_minor.trans minor, isomorphism⟩)
    (by
      intro candidate member finite_candidate nonempty
      exact reducibility candidate finite_candidate member.1 member.2 nonempty)
    ⟨binary, excluded⟩
  exact ground_eq_empty_iff.mp empty ▸ trace

end Matroid

namespace TauCeti.Toric.Fan

open Module Set BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem deep_minor_complete_reduction_trace_of_elementary_reducibility
    (fan : Fan embedding) (reducibility : BinaryK4ExcludedElementaryReducibility fan.Ray)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    {smaller : Matroid fan.Ray} (minor : smaller ≤m fan.rayMatroid) :
    Matroid.SeriesParallelReductionTrace smaller (Matroid.emptyOn fan.Ray) smaller.E.ncard := by
  let : smaller.Finite := ⟨fan.rayMatroid.ground_finite.subset minor.subset⟩
  exact Matroid.binary_k4_excluded_complete_trace_of_elementary_reducibility reducibility
    (fan.deep_minor_representable complete regular deep reference minor)
    (fan.deep_minor_no_graph_k4 complete regular deep reference minor)

theorem deep_ray_count_le_four_dimension_sub_two_of_elementary_reducibility
    (fan : Fan embedding) (reducibility : BinaryK4ExcludedElementaryReducibility fan.Ray)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (positive_dimension : 0 < dimension) : Nat.card fan.Ray ≤ 4 * dimension - 2 :=
  fan.ray_count_le_four_dimension_sub_two_of_complete_reduction_traces_on_minors
    (fun _ minor => fan.deep_minor_complete_reduction_trace_of_elementary_reducibility
      reducibility complete regular deep reference minor) complete regular reference positive_dimension

end TauCeti.Toric.Fan
