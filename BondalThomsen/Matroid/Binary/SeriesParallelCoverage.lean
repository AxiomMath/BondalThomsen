module

public import BondalThomsen.Matroid.SeriesParallelRecursion
public import BondalThomsen.DeepFan.Classification
public import BondalThomsen.Matroid.K4GraphIdentification
public import BondalThomsen.Matroid.DeepGraphMinorExclusion

@[expose] public section

namespace Matroid

open Set

theorem exists_isLoop_or_para_of_not_simple {Label : Type*} {source : Matroid Label}
    (not_simple : ¬source.Simple) :
    (∃ edge, source.IsLoop edge) ∨
      ∃ first second, source.Parallel first second ∧ first ≠ second := by
  classical
  by_contra none
  have no_loop : ∀ edge, ¬source.IsLoop edge := by
    intro edge loop
    exact none (Or.inl ⟨edge, loop⟩)
  have equal : ∀ first second, source.Parallel first second → first = second := by
    intro first second parallel
    by_contra distinct
    exact none (Or.inr ⟨first, second, parallel, distinct⟩)
  apply not_simple
  refine ⟨?_⟩
  intro first second first_ground
  constructor
  · exact equal first second
  · rintro rfl
    have nonloop := source.isNonloop_of_not_isLoop first_ground (no_loop first)
    exact ⟨nonloop, nonloop, rfl⟩

theorem exists_elementary_reduction_of_not_simple_or_dual {Label : Type*}
    {source : Matroid Label} (obstruction : ¬source.Simple ∨ ¬source✶.Simple) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced := by
  rcases obstruction with not_simple | not_cosimple
  · rcases exists_isLoop_or_para_of_not_simple not_simple with
      ⟨edge, loop⟩ | ⟨first, second, parallel, distinct⟩
    · exact ⟨_, .loop edge loop⟩
    · exact ⟨_, .parallel first second distinct parallel⟩
  · rcases exists_isLoop_or_para_of_not_simple not_cosimple with
      ⟨edge, loop⟩ | ⟨first, second, series, distinct⟩
    · exact ⟨_, .coloop edge (dual_isLoop_iff_isColoop.mp loop)⟩
    · exact ⟨_, .series first second distinct series⟩

end Matroid

