module

public import BondalThomsen.Matroid.SeriesParallelReductions
public import Mathlib.Combinatorics.Matroid.Map

@[expose] public section

namespace Matroid

open Set Function

variable {Label : Type*} [DecidableEq Label] {source : Matroid Label}
    {existing added : Label} {selected : Set Label}

def parallelExtend (source : Matroid Label) (existing added : Label) : Matroid Label :=
  (source.comap (Function.update id added existing)).restrict (insert added source.E)

@[simp] theorem parallelExtend_ground (source : Matroid Label) (existing added : Label) :
    (source.parallelExtend existing added).E = insert added source.E := rfl

theorem parallelExtend_indep_iff :
    (source.parallelExtend existing added).Indep selected ↔
      source.Indep (Function.update id added existing '' selected) ∧
        InjOn (Function.update id added existing) selected ∧ selected ⊆ insert added source.E := by
  rw [parallelExtend, restrict_indep_iff, comap_indep_iff]
  tauto

theorem parallelExtend_delete_eq' (source : Matroid Label) (existing added : Label) :
    (source.parallelExtend existing added).delete {added} = source.delete {added} := by
  apply ext_indep (by simp)
  intro selected subset_ground
  have avoids : added ∉ selected := by
    intro member
    exact (subset_ground member).2 (by simp)
  have unchanged : EqOn (Function.update id added existing) id selected := by
    intro element member
    have distinct : element ≠ added := fun equal => avoids (equal ▸ member)
    exact Function.update_of_ne distinct _ _
  have injective : InjOn (Function.update id added existing) selected :=
    unchanged.injOn_iff.mpr (injective_id.injOn)
  have selected_subset : selected ⊆ insert added source.E := by
    intro element member
    exact (subset_ground member).1
  simp only [delete_indep_iff, parallelExtend_indep_iff, unchanged.image_eq,
    image_id, injective, selected_subset, and_true]

theorem parallelExtend_delete_eq (source : Matroid Label) (existing : Label)
    (new_label : added ∉ source.E) :
    (source.parallelExtend existing added).delete {added} = source := by
  rw [parallelExtend_delete_eq', source.deleteElem_eq_self new_label]

theorem parallelExtend_parallel (nonloop : source.IsNonloop existing) (added : Label) :
    (source.parallelExtend existing added).Parallel existing added := by
  have unchanged : Function.update id added existing existing = existing := by
    by_cases same : existing = added
    · subst added
      simp
    · exact Function.update_of_ne same _ _
  have existing_nonloop : (source.parallelExtend existing added).IsNonloop existing := by
    rw [← indep_singleton, parallelExtend_indep_iff]
    exact ⟨by simpa only [image_singleton, unchanged] using nonloop.indep,
      injOn_singleton _ _, by simp [nonloop.mem_ground]⟩
  have added_nonloop : (source.parallelExtend existing added).IsNonloop added := by
    rw [← indep_singleton, parallelExtend_indep_iff]
    exact ⟨by simpa using nonloop.indep, injOn_singleton _ _, by simp⟩
  apply parallel_iff_isNonloop_isNonloop_indep_imp_eq.mpr
  refine ⟨existing_nonloop, added_nonloop, ?_⟩
  intro independent
  have injective := (parallelExtend_indep_iff.mp independent).2.1
  exact injective (by simp) (by simp) (by simp [unchanged])

instance parallelExtend_finite (source : Matroid Label) [source.Finite]
    (existing added : Label) : (source.parallelExtend existing added).Finite :=
  ⟨source.ground_finite.insert added⟩

theorem parallelExtend_indep_iff_of_notMem (absent : added ∉ selected) :
    (source.parallelExtend existing added).Indep selected ↔ source.Indep selected := by
  have unchanged : EqOn (Function.update id added existing) id selected := by
    intro element member
    have distinct : element ≠ added := fun equal => absent (equal ▸ member)
    exact Function.update_of_ne distinct _ _
  have injective : InjOn (Function.update id added existing) selected :=
    unchanged.injOn_iff.mpr injective_id.injOn
  rw [parallelExtend_indep_iff, unchanged.image_eq, image_id]
  constructor
  · exact fun independent => independent.1
  · exact fun independent => ⟨independent, injective,
      independent.subset_ground.trans (subset_insert _ _)⟩

theorem parallelExtend_fold_injOn_iff (distinct : existing ≠ added) :
    InjOn (Function.update id added existing) selected ↔
      ¬(existing ∈ selected ∧ added ∈ selected) := by
  constructor
  · intro injective both
    exact distinct (injective both.1 both.2 (by simp [Function.update_of_ne distinct]))
  · intro avoids first first_member second second_member equal
    by_cases first_added : first = added
    · subst first
      by_cases second_added : second = added
      · exact second_added.symm
      · have second_existing : second = existing := by
          simpa [Function.update_of_ne second_added] using equal.symm
        exact (avoids ⟨second_existing ▸ second_member, first_member⟩).elim
    · by_cases second_added : second = added
      · subst second
        have first_existing : first = existing := by
          simpa [Function.update_of_ne first_added] using equal
        exact (avoids ⟨first_existing ▸ first_member, second_member⟩).elim
      · simpa [Function.update_of_ne first_added, Function.update_of_ne second_added] using equal

theorem parallelExtend_fold_image_of_mem (member : added ∈ selected) :
    Function.update id added existing '' selected = insert existing (selected \ {added}) := by
  ext element
  constructor
  · rintro ⟨original, original_member, rfl⟩
    by_cases equal : original = added
    · subst original
      simp
    · rw [Function.update_of_ne equal]
      exact Or.inr ⟨original_member, by simpa using equal⟩
  · rintro (rfl | ⟨element_member, absent⟩)
    · exact ⟨added, member, by simp⟩
    · have distinct : element ≠ added := by simpa using absent
      exact ⟨element, element_member, Function.update_of_ne distinct _ _⟩

theorem Parallel.eq_parallelExtend_delete (parallel : source.Parallel existing added)
    (distinct : existing ≠ added) :
    source = (source.delete {added}).parallelExtend existing added := by
  apply ext_indep (by
    rw [parallelExtend_ground, delete_ground, insert_sdiff_singleton,
      insert_eq_of_mem parallel.2.1.mem_ground])
  intro selected subset_ground
  by_cases added_member : added ∈ selected
  · by_cases existing_member : existing ∈ selected
    · have source_dependent : ¬source.Indep selected := by
        intro independent
        exact distinct ((parallel_iff_isNonloop_isNonloop_indep_imp_eq.mp parallel).2.2
          (independent.subset (pair_subset existing_member added_member)))
      have extension_dependent :
          ¬((source.delete {added}).parallelExtend existing added).Indep selected := by
        intro independent
        exact (parallelExtend_fold_injOn_iff distinct).mp
          (parallelExtend_indep_iff.mp independent).2.1 ⟨existing_member, added_member⟩
      exact iff_of_false source_dependent extension_dependent
    · have avoids : added ∉ insert existing (selected \ {added}) := by
        simp [distinct.symm]
      have subset : selected ⊆ insert added (source.delete {added}).E := by
        intro element member
        by_cases equal : element = added
        · exact Or.inl equal
        · exact Or.inr ⟨subset_ground member, by simpa using equal⟩
      rw [parallelExtend_indep_iff, parallelExtend_fold_image_of_mem added_member,
        delete_indep_iff, Set.disjoint_singleton_right]
      have injective : InjOn (Function.update id added existing) selected :=
        (parallelExtend_fold_injOn_iff distinct).mpr (by simp [existing_member])
      simp only [avoids, not_false_eq_true, and_true, injective, subset]
      exact parallel.symm.indep_substitute_iff added_member existing_member
  · rw [parallelExtend_indep_iff_of_notMem added_member, delete_indep_iff,
      Set.disjoint_singleton_right]
    simp only [added_member, not_false_eq_true, and_true]

def seriesExtend (source : Matroid Label) (existing added : Label) : Matroid Label :=
  (source✶.parallelExtend existing added)✶

@[simp] theorem seriesExtend_dual (source : Matroid Label) (existing added : Label) :
    (source.seriesExtend existing added)✶ = source✶.parallelExtend existing added := by
  rw [seriesExtend, dual_dual]

@[simp] theorem seriesExtend_ground (source : Matroid Label) (existing added : Label) :
    (source.seriesExtend existing added).E = insert added source.E := by
  rw [seriesExtend, dual_ground, parallelExtend_ground, dual_ground]

instance seriesExtend_finite (source : Matroid Label) [source.Finite]
    (existing added : Label) : (source.seriesExtend existing added).Finite := by
  rw [seriesExtend]
  infer_instance

theorem seriesExtend_dual_parallel (nonloop : source✶.IsNonloop existing)
    (added : Label) : (source.seriesExtend existing added)✶.Parallel existing added := by
  rw [seriesExtend_dual]
  exact parallelExtend_parallel nonloop added

theorem series_pair_eq_seriesExtend_contract
    (series : source✶.Parallel existing added) (distinct : existing ≠ added) :
    source = (source.contract {added}).seriesExtend existing added := by
  have equality := congrArg Matroid.dual (series.eq_parallelExtend_delete distinct)
  rw [dual_dual] at equality
  simpa only [seriesExtend, dual_contract] using equality

theorem seriesExtend_contract_eq (source : Matroid Label) (existing : Label)
    (new_label : added ∉ source.E) :
    (source.seriesExtend existing added).contract {added} = source := by
  rw [seriesExtend, ← dual_delete_dual, dual_dual,
    parallelExtend_delete_eq source✶ existing new_label,
    dual_dual]

end Matroid
