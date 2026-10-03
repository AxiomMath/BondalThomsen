module

public import BondalThomsen.Matroid.Binary.MarkedLeafReduction

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {marked first second : Label}

theorem MarkedSeriesParallelPair.exists_connected_marked_leaf_reduction [source.Finite]
    (pair : MarkedSeriesParallelPair source marked)
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced ∧ reduced.Connected ∧
      marked ∈ reduced.E ∧ reduced.IsNonloop marked ∧ ¬reduced.IsColoop marked ∧
        reduced.E.ncard + 1 = source.E.ncard ∧ reduced.Representable (ZMod 2) ∧
          ¬ ∃ candidate : Matroid Label, candidate ≤m reduced ∧
            Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
  have source_lower := pair.ground_ncard_ge_three marked_member
  obtain ⟨left, left_member, right, right_member, distinct,
    left_avoids, right_avoids, property⟩ := pair
  have finish {reduced : Matroid Label}
      (reduction : ElementarySeriesParallelReduction source reduced)
      (reduced_connected : reduced.Connected) (marked_retained : marked ∈ reduced.E) :
      ElementarySeriesParallelReduction source reduced ∧ reduced.Connected ∧
        marked ∈ reduced.E ∧ reduced.IsNonloop marked ∧ ¬reduced.IsColoop marked ∧
          reduced.E.ncard + 1 = source.E.ncard ∧ reduced.Representable (ZMod 2) ∧
            ¬ ∃ candidate : Matroid Label, candidate ≤m reduced ∧
              Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
    let : reduced.Finite := ⟨source.ground_finite.subset reduction.isMinor.subset⟩
    let : Finite reduced.E := reduced.ground_finite.to_subtype
    have size := reduction.ground_ncard
    have nontrivial : reduced.E.Nontrivial := Set.one_lt_ncard_iff_nontrivial.mp (by omega)
    refine ⟨reduction, reduced_connected, marked_retained,
      reduced_connected.isNonloop nontrivial marked_retained,
      reduced_connected.not_isColoop nontrivial marked_retained, size,
      binary.of_isMinor reduction.isMinor, ?_⟩
    rintro ⟨candidate, minor, isomorphism⟩
    exact excluded ⟨candidate, minor.trans reduction.isMinor, isomorphism⟩
  rcases property with parallel | series
  · exact ⟨source.delete {left}, finish (.parallel left right distinct parallel)
      (connected.delete_parallel parallel distinct)
      ⟨marked_member, by simpa using left_avoids.symm⟩⟩
  · exact ⟨source.contract {left}, finish (.series left right distinct series)
      (connected.contract_series series distinct)
      ⟨marked_member, by simpa using left_avoids.symm⟩⟩

end Matroid
