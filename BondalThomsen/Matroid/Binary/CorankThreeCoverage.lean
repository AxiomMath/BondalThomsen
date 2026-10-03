module

public import BondalThomsen.Matroid.Binary.RankThreeCoverage
public import BondalThomsen.Matroid.Binary.MarkedCorankThreeReduction
public import BondalThomsen.Matroid.DualRepresentation

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label}

theorem binary_corank_three_k4_excluded_exists_elementary_reduction
    [source.Finite] (binary : source.Representable (ZMod 2)) (corank : source✶.eRank ≤ 3)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (nonempty : source.E.Nonempty) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced := by
  obtain ⟨reduced, reduction⟩ :=
    binary_rank_three_k4_excluded_exists_elementary_reduction binary.dual corank
      ((BondalThomsen.graph_k4_excluded_dual_iff source).mpr excluded)
      (by simpa only [dual_ground] using nonempty)
  exact ⟨reduced✶, by simpa only [dual_dual] using reduction.dual⟩

theorem binary_rank_or_corank_three_k4_excluded_exists_elementary_reduction
    [source.Finite] (binary : source.Representable (ZMod 2))
    (rank_or_corank : source.eRank ≤ 3 ∨ source✶.eRank ≤ 3)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (nonempty : source.E.Nonempty) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced := by
  rcases rank_or_corank with rank | corank
  · exact binary_rank_three_k4_excluded_exists_elementary_reduction
      binary rank excluded nonempty
  · exact binary_corank_three_k4_excluded_exists_elementary_reduction
      binary corank excluded nonempty

end Matroid
