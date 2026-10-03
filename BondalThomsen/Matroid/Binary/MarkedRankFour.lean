module

public import BondalThomsen.Matroid.Binary.RankFourCoverage
public import BondalThomsen.Matroid.Binary.MarkedEightElement
public import BondalThomsen.Matroid.Binary.MarkedCorankThreeReduction

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {marked : Label}

theorem connected_binary_rank_four_pair_avoiding [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (rank : source.eRank ≤ 4) (lower : 3 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) : MarkedSeriesParallelPair source marked := by
  classical
  suffices result : ∀ cardinality : ℕ, ∀ candidate : Matroid Label, candidate.Finite →
      candidate.E.ncard = cardinality → candidate.Connected → candidate.Representable (ZMod 2) →
      candidate.eRank ≤ 4 → 3 ≤ cardinality →
      (¬ ∃ smaller : Matroid Label, smaller ≤m candidate ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller)) →
      ∀ basepoint ∈ candidate.E, MarkedSeriesParallelPair candidate basepoint by
    exact result source.E.ncard source inferInstance rfl connected binary rank lower
      excluded marked marked_member
  intro cardinality
  induction cardinality using Nat.strong_induction_on with
  | h cardinality induction =>
    intro candidate finite_candidate cardinality_eq connected binary rank lower excluded
      basepoint basepoint_member
    let : candidate.Finite := finite_candidate
    let : Finite candidate.E := candidate.ground_finite.to_subtype
    by_cases bounded : cardinality ≤ 8
    · exact connected_binary_eight_element_pair_avoiding connected binary
        (by omega) (by omega) excluded basepoint_member
    have nontrivial : candidate.E.Nontrivial := Set.one_lt_ncard_iff_nontrivial.mp (by omega)
    obtain ⟨reduced, reduction⟩ := binary_rank_four_k4_excluded_exists_elementary_reduction
      binary rank excluded ⟨basepoint, basepoint_member⟩
    have recurse_parallel {other : Label} (parallel : candidate.Parallel basepoint other)
        (distinct : basepoint ≠ other) : MarkedSeriesParallelPair candidate basepoint := by
      have smaller_size := parallel.delete_ground_ncard
      have smaller_minor : candidate.delete {basepoint} ≤m candidate :=
        (delete_isRestriction _ _).isMinor
      have smaller_excluded : ¬ ∃ smaller : Matroid Label,
          smaller ≤m candidate.delete {basepoint} ∧
            Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller) := by
        rintro ⟨smaller, minor, isomorphism⟩
        exact excluded ⟨smaller, minor.trans smaller_minor, isomorphism⟩
      have pair := induction (candidate.delete {basepoint}).E.ncard (by omega)
        (candidate.delete {basepoint}) inferInstance rfl
        (connected.delete_parallel parallel distinct) (binary.delete {basepoint})
        (smaller_minor.eRank_le.trans rank) (by omega) smaller_excluded other
        ⟨parallel.2.1.mem_ground, by simpa using distinct.symm⟩
      exact pair.of_parallel_delete parallel distinct
    have recurse_series {other : Label} (series : candidate✶.Parallel basepoint other)
        (distinct : basepoint ≠ other) : MarkedSeriesParallelPair candidate basepoint := by
      have smaller_size := series_contract_ground_ncard series
      have smaller_minor : candidate.contract {basepoint} ≤m candidate := contract_isMinor _ _
      have smaller_excluded : ¬ ∃ smaller : Matroid Label,
          smaller ≤m candidate.contract {basepoint} ∧
            Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller) := by
        rintro ⟨smaller, minor, isomorphism⟩
        exact excluded ⟨smaller, minor.trans smaller_minor, isomorphism⟩
      have pair := induction (candidate.contract {basepoint}).E.ncard (by omega)
        (candidate.contract {basepoint}) inferInstance rfl
        (connected.contract_series series distinct) (binary.contract {basepoint})
        (smaller_minor.eRank_le.trans rank) (by omega) smaller_excluded other
        ⟨series.2.1.mem_ground, by simpa using distinct.symm⟩
      exact pair.of_series_contract series distinct
    cases reduction with
    | loop element loop =>
      exact ((connected.isNonloop nontrivial loop.mem_ground).not_isLoop loop).elim
    | coloop element coloop =>
      exact (connected.not_isColoop nontrivial coloop.mem_ground coloop).elim
    | parallel left right distinct parallel =>
      by_cases left_marked : left = basepoint
      · subst left
        exact recurse_parallel parallel distinct
      by_cases right_marked : right = basepoint
      · subst right
        exact recurse_parallel parallel.symm distinct.symm
      exact ⟨left, parallel.1.mem_ground, right, parallel.2.1.mem_ground,
        distinct, left_marked, right_marked, Or.inl parallel⟩
    | series left right distinct series =>
      by_cases left_marked : left = basepoint
      · subst left
        exact recurse_series series distinct
      by_cases right_marked : right = basepoint
      · subst right
        exact recurse_series series.symm distinct.symm
      exact ⟨left, series.1.mem_ground, right, series.2.1.mem_ground,
        distinct, left_marked, right_marked, Or.inr series⟩

theorem connected_binary_corank_four_pair_avoiding [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (corank : source✶.eRank ≤ 4) (lower : 3 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) : MarkedSeriesParallelPair source marked := by
  apply markedSeriesParallelPair_dual_iff.mp
  exact connected_binary_rank_four_pair_avoiding connected.to_dual binary.dual corank
    (by simpa only [dual_ground] using lower)
    ((BondalThomsen.graph_k4_excluded_dual_iff source).mpr excluded)
    (by simpa only [dual_ground] using marked_member)

theorem connected_binary_rank_or_corank_four_pair_avoiding [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (small : source.eRank ≤ 4 ∨ source✶.eRank ≤ 4) (lower : 3 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) : MarkedSeriesParallelPair source marked := by
  rcases small with rank | corank
  · exact connected_binary_rank_four_pair_avoiding connected binary rank lower excluded marked_member
  · exact connected_binary_corank_four_pair_avoiding connected binary corank lower excluded marked_member

theorem connected_binary_no_marked_pair_forces_rank_corank_five [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (lower : 3 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) (failure : ¬MarkedSeriesParallelPair source marked) :
    5 ≤ source.eRank ∧ 5 ≤ source✶.eRank ∧ 10 ≤ source.E.ncard := by
  have not_small : ¬ (source.eRank ≤ 4 ∨ source✶.eRank ≤ 4) := by
    intro small
    exact failure (connected_binary_rank_or_corank_four_pair_avoiding connected binary
      small lower excluded marked_member)
  have rank_lower : 5 ≤ source.eRank :=
    (ENat.add_one_le_iff (by simp)).mpr (lt_of_not_ge (fun rank => not_small (Or.inl rank)))
  have corank_lower : 5 ≤ source✶.eRank :=
    (ENat.add_one_le_iff (by simp)).mpr (lt_of_not_ge (fun corank => not_small (Or.inr corank)))
  have ground_lower : (10 : ℕ∞) ≤ source.E.encard := by
    calc
      10 = (5 : ℕ∞) + 5 := by norm_num
      _ ≤ source.eRank + source✶.eRank := add_le_add rank_lower corank_lower
      _ = source.E.encard := source.eRank_add_eRank_dual
  rw [← source.ground_finite.cast_ncard_eq] at ground_lower
  exact ⟨rank_lower, corank_lower, by exact_mod_cast ground_lower⟩

end Matroid
