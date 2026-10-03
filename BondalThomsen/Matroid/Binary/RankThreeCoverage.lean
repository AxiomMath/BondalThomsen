module

public import BondalThomsen.Matroid.Binary.SixElementCoverage

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label}

theorem Simple.restrict_ground_subset [source.Simple]
    {selected : Set Label} (subset : selected ⊆ source.E) : (source.restrict selected).Simple := by
  apply simple_iff_forall_pair_indep.mpr
  intro first second first_member second_member
  exact restrict_indep_iff.mpr
    ⟨simple_iff_forall_pair_indep.mp inferInstance first second
      (subset first_member) (subset second_member), pair_subset first_member second_member⟩

theorem binary_simple_rank_three_six_restriction_iso_graph_k4
    [source.Finite] [source.Simple] (binary : source.Representable (ZMod 2))
    (rank : source.eRank ≤ 3) {selected : Set Label} (subset : selected ⊆ source.E)
    (size : selected.ncard = 6) :
    Nonempty (Iso (source.restrict selected) BondalThomsen.k4GraphCycleMatroid) := by
  let minor := (source.restrict_isRestriction selected subset).isMinor
  let : (source.restrict selected).Finite := ⟨source.ground_finite.subset subset⟩
  let : (source.restrict selected).Simple := Simple.restrict_ground_subset subset
  have restricted_binary := binary.of_isMinor minor
  have restricted_size : (source.restrict selected).E.ncard = 6 := by
    simpa only [restrict_ground_eq] using size
  have rank_upper := minor.eRank_le.trans rank
  have rank_not_small : ¬(source.restrict selected).eRank ≤ 2 := by
    intro rank_small
    have bound := binary_simple_rank_two_ground_card_le_three restricted_binary rank_small
    omega
  have rank_lower : 3 ≤ (source.restrict selected).eRank :=
    (ENat.add_one_le_iff (by simp)).mpr (lt_of_not_ge rank_not_small)
  exact binary_simple_rank_three_six_iso_graph_k4 restricted_binary
    (le_antisymm rank_upper rank_lower) restricted_size

theorem binary_simple_rank_three_k4_excluded_ground_card_le_five
    [source.Finite] [source.Simple] (binary : source.Representable (ZMod 2))
    (rank : source.eRank ≤ 3)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate)) : source.E.ncard ≤ 5 := by
  by_contra not_small
  obtain ⟨selected, subset, size⟩ := Set.exists_subset_card_eq (show 6 ≤ source.E.ncard by omega)
  obtain ⟨isomorphism⟩ :=
    binary_simple_rank_three_six_restriction_iso_graph_k4 binary rank subset size
  exact excluded ⟨source.restrict selected, (source.restrict_isRestriction selected subset).isMinor,
    ⟨isomorphism.symm⟩⟩

theorem binary_rank_three_k4_excluded_exists_elementary_reduction
    [source.Finite] (binary : source.Representable (ZMod 2)) (rank : source.eRank ≤ 3)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (nonempty : source.E.Nonempty) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced := by
  by_cases simple : source.Simple
  · let := simple
    exact binary_five_element_exists_elementary_reduction binary
      (binary_simple_rank_three_k4_excluded_ground_card_le_five binary rank excluded) nonempty
  · exact exists_elementary_reduction_of_not_simple_or_dual (Or.inl simple)

end Matroid
