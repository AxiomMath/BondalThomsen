module

public import BondalThomsen.Matroid.Binary.EightElementCoverage
public import BondalThomsen.Matroid.Binary.MarkedRankThree
public import BondalThomsen.Matroid.Binary.MarkedCorankThreeReduction
public import BondalThomsen.Matroid.Binary.TwoSumLeafLifting

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {marked : Label}

theorem connected_binary_eight_element_pair_avoiding [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (size : source.E.ncard ≤ 8) (lower : 3 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) : MarkedSeriesParallelPair source marked := by
  classical
  suffices result : ∀ cardinality : ℕ, ∀ candidate : Matroid Label, candidate.Finite →
      candidate.E.ncard = cardinality → candidate.Connected → candidate.Representable (ZMod 2) →
      cardinality ≤ 8 → 3 ≤ cardinality →
      (¬ ∃ smaller : Matroid Label, smaller ≤m candidate ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller)) →
      ∀ basepoint ∈ candidate.E, MarkedSeriesParallelPair candidate basepoint by
    exact result source.E.ncard source inferInstance rfl connected binary size lower
      excluded marked marked_member
  intro cardinality
  induction cardinality using Nat.strong_induction_on with
  | h cardinality induction =>
    intro candidate finite_candidate cardinality_eq connected binary size lower excluded
      basepoint basepoint_member
    let : candidate.Finite := finite_candidate
    let : Finite candidate.E := candidate.ground_finite.to_subtype
    by_cases bounded : cardinality ≤ 6
    · exact connected_binary_six_element_pair_avoiding connected binary
        (by omega) (by omega) excluded basepoint_member
    have nontrivial : candidate.E.Nontrivial := Set.one_lt_ncard_iff_nontrivial.mp (by omega)
    obtain ⟨reduced, reduction⟩ := binary_eight_element_k4_excluded_exists_elementary_reduction
      binary (by omega) excluded ⟨basepoint, basepoint_member⟩
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
        (by omega) (by omega) smaller_excluded other
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
        (by omega) (by omega) smaller_excluded other
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

end Matroid
