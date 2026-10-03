module

public import BondalThomsen.Matroid.Binary.FourNormalization
public import BondalThomsen.Matroid.Binary.FourQuotientContraction

@[expose] public section

namespace Matroid

open Set BondalThomsen

variable {Label : Type*} {source : Matroid Label}

theorem binary_simple_rank_four_eight_has_graph_k4_minor [source.Finite] [source.Simple]
    (binary : source.Representable (ZMod 2)) (rank : source.eRank = 4)
    (cardinality : source.E.ncard = 8) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso k4GraphCycleMatroid candidate) := by
  obtain ⟨representation, selected, selected_card, ground_image⟩ :=
    binary.exists_binary_eight_normalized_ground rank cardinality
  exact representation.has_graph_k4_minor_of_normalized_eight_binary_points
    selected selected_card ground_image

theorem binary_eight_element_k4_excluded_exists_elementary_reduction [source.Finite]
    (binary : source.Representable (ZMod 2)) (size : source.E.ncard ≤ 8)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso k4GraphCycleMatroid candidate))
    (nonempty : source.E.Nonempty) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced := by
  rcases rank_or_corank_le_three_or_four_four_of_ground_ncard_le_eight size with
    small | ⟨rank, _, cardinality⟩
  · exact binary_rank_or_corank_three_k4_excluded_exists_elementary_reduction
      binary small excluded nonempty
  · by_cases simple : source.Simple
    · let := simple
      exact (excluded (binary_simple_rank_four_eight_has_graph_k4_minor
        binary rank cardinality)).elim
    · exact exists_elementary_reduction_of_not_simple_or_dual (Or.inl simple)

end Matroid
