module

public import BondalThomsen.Matroid.Binary.CorankThreeCoverage

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {marked : Label}

private theorem rank_corank_sum [source.Finite] :
    source.eRank.toNat + source✶.eRank.toNat = source.E.ncard := by
  have equality := congrArg ENat.toNat source.eRank_add_eRank_dual
  rw [ENat.toNat_add (source.eRank_ne_top_iff.mpr inferInstance)
    (source✶.eRank_ne_top_iff.mpr inferInstance),
    ← source.ground_finite.cast_ncard_eq, ENat.toNat_natCast] at equality
  exact equality

private theorem rank_corank_small_iff [source.Finite] :
    (source.eRank ≤ 3 ∨ source✶.eRank ≤ 3) ↔
      (source.eRank.toNat ≤ 3 ∨ source✶.eRank.toNat ≤ 3) := by
  rw [← ENat.natCast_toNat (source.eRank_ne_top_iff.mpr inferInstance),
    ← ENat.natCast_toNat (source✶.eRank_ne_top_iff.mpr inferInstance)]
  norm_cast

theorem rank_or_corank_le_three_of_ground_ncard_le_seven [source.Finite]
    (size : source.E.ncard ≤ 7) : source.eRank ≤ 3 ∨ source✶.eRank ≤ 3 := by
  apply rank_corank_small_iff.mpr
  have sum := rank_corank_sum (source := source)
  omega

theorem rank_or_corank_le_three_or_four_four_of_ground_ncard_le_eight [source.Finite]
    (size : source.E.ncard ≤ 8) :
    (source.eRank ≤ 3 ∨ source✶.eRank ≤ 3) ∨
      (source.eRank = 4 ∧ source✶.eRank = 4 ∧ source.E.ncard = 8) := by
  by_cases small : source.eRank ≤ 3 ∨ source✶.eRank ≤ 3
  · exact Or.inl small
  have not_small := mt (rank_corank_small_iff (source := source)).mpr small
  have sum := rank_corank_sum (source := source)
  right
  refine ⟨?_, ?_, by omega⟩
  · rw [← ENat.natCast_toNat (source.eRank_ne_top_iff.mpr inferInstance)]
    exact_mod_cast (show source.eRank.toNat = 4 by omega)
  · rw [← ENat.natCast_toNat (source✶.eRank_ne_top_iff.mpr inferInstance)]
    exact_mod_cast (show source✶.eRank.toNat = 4 by omega)

theorem binary_seven_element_k4_excluded_exists_elementary_reduction [source.Finite]
    (binary : source.Representable (ZMod 2)) (size : source.E.ncard ≤ 7)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (nonempty : source.E.Nonempty) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced :=
  binary_rank_or_corank_three_k4_excluded_exists_elementary_reduction binary
    (rank_or_corank_le_three_of_ground_ncard_le_seven size) excluded nonempty

end Matroid
