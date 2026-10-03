module

public import BondalThomsen.Matroid.Binary.EightElementCoverage

@[expose] public section

namespace Matroid

open Set BondalThomsen

variable {Label : Type*} {source : Matroid Label}

theorem binary_simple_rank_four_k4_excluded_ground_card_le_seven
    [source.Finite] [source.Simple] (binary : source.Representable (ZMod 2))
    (rank : source.eRank ≤ 4)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso k4GraphCycleMatroid candidate)) : source.E.ncard ≤ 7 := by
  by_contra not_small
  obtain ⟨selected, subset, size⟩ := Set.exists_subset_card_eq (show 8 ≤ source.E.ncard by omega)
  let minor := (source.restrict_isRestriction selected subset).isMinor
  let : (source.restrict selected).Finite := ⟨source.ground_finite.subset subset⟩
  let : (source.restrict selected).Simple := Simple.restrict_ground_subset subset
  have restricted_binary := binary.of_isMinor minor
  have restricted_size : (source.restrict selected).E.ncard = 8 := by
    simpa only [restrict_ground_eq] using size
  have rank_upper := minor.eRank_le.trans rank
  have restricted_excluded : ¬ ∃ candidate : Matroid Label,
      candidate ≤m source.restrict selected ∧ Nonempty (Iso k4GraphCycleMatroid candidate) := by
    rintro ⟨candidate, candidate_minor, isomorphism⟩
    exact excluded ⟨candidate, candidate_minor.trans minor, isomorphism⟩
  by_cases small_rank : (source.restrict selected).eRank ≤ 3
  · have bound := binary_simple_rank_three_k4_excluded_ground_card_le_five
      restricted_binary small_rank restricted_excluded
    omega
  · have rank_lower : 4 ≤ (source.restrict selected).eRank :=
      (ENat.add_one_le_iff (by simp)).mpr (lt_of_not_ge small_rank)
    exact restricted_excluded (binary_simple_rank_four_eight_has_graph_k4_minor
      restricted_binary (le_antisymm rank_upper rank_lower) restricted_size)

theorem binary_rank_four_k4_excluded_exists_elementary_reduction
    [source.Finite] (binary : source.Representable (ZMod 2)) (rank : source.eRank ≤ 4)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso k4GraphCycleMatroid candidate)) (nonempty : source.E.Nonempty) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced := by
  by_cases simple : source.Simple
  · let := simple
    exact binary_seven_element_k4_excluded_exists_elementary_reduction binary
      (binary_simple_rank_four_k4_excluded_ground_card_le_seven binary rank excluded) excluded nonempty
  · exact exists_elementary_reduction_of_not_simple_or_dual (Or.inl simple)

end Matroid
