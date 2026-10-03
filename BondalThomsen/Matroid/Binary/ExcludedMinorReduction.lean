module

public import BondalThomsen.Matroid.Binary.SeriesParallelCoverage

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label}

theorem simple_cosimple_ground_encard_ge_four [source.Simple] [source✶.Simple]
    (nonempty : source.E.Nonempty) : 4 ≤ source.E.encard := by
  by_cases nontrivial : source.E.Nontrivial
  · obtain ⟨first, first_member, second, second_member, distinct⟩ := nontrivial
    have independent := simple_iff_forall_pair_indep.mp
      (inferInstance : source.Simple) first second first_member second_member
    have coindependent := simple_iff_forall_pair_indep.mp
      (inferInstance : source✶.Simple) first second first_member second_member
    have rank := independent.encard_le_eRank
    have corank := coindependent.encard_le_eRank
    rw [Set.encard_pair distinct] at rank corank
    calc
      4 = (2 : ℕ∞) + 2 := by norm_num
      _ ≤ source.eRank + source✶.eRank := add_le_add rank corank
      _ = source.E.encard := source.eRank_add_eRank_dual
  · obtain ⟨element, member⟩ := nonempty
    have independent := simple_iff_forall_pair_indep.mp
      (inferInstance : source.Simple) element element member member
    have coindependent := simple_iff_forall_pair_indep.mp
      (inferInstance : source✶.Simple) element element member member
    have rank := independent.encard_le_eRank
    have corank := coindependent.encard_le_eRank
    simp only [Set.pair_eq_singleton, Set.encard_singleton] at rank corank
    have lower : 2 ≤ source.E.encard := by
      calc
        2 = (1 : ℕ∞) + 1 := by norm_num
        _ ≤ source.eRank + source✶.eRank := add_le_add rank corank
        _ = source.E.encard := source.eRank_add_eRank_dual
    have upper : source.E.encard ≤ 1 := Set.encard_le_one_iff_subsingleton.mpr
      (Set.not_nontrivial_iff.mp nontrivial)
    have impossible := lower.trans upper
    norm_num at impossible

theorem compl_pair_isBase_of_simple_dual_corank_le_two [source✶.Simple]
    (corank : source✶.eRank ≤ 2) {first second : Label}
    (first_member : first ∈ source.E) (second_member : second ∈ source.E)
    (distinct : first ≠ second) : source.IsBase (source.E \ {first, second}) := by
  have independent := simple_iff_forall_pair_indep.mp
    (inferInstance : source✶.Simple) first second first_member second_member
  have base : source✶.IsBase {first, second} := by
    apply independent.isBase_of_eRk_ge (Set.toFinite _)
    rw [independent.eRk_eq_encard, Set.encard_pair distinct]
    exact corank
  exact base.compl_isBase_of_dual

theorem binary_not_simple_cosimple_of_corank_le_two [source.Finite]
    (binary : source.Representable (ZMod 2)) (corank : source✶.eRank ≤ 2)
    (nonempty : source.E.Nonempty) : ¬source.Simple ∨ ¬source✶.Simple := by
  classical
  by_contra obstruction
  have both : source.Simple ∧ source✶.Simple := by tauto
  let : source.Simple := both.1
  let : source✶.Simple := both.2
  have lower := simple_cosimple_ground_encard_ge_four (source := source) nonempty
  have ground_large : 3 < source.E.ncard := by
    rw [← source.ground_finite.cast_ncard_eq] at lower
    exact_mod_cast (show (3 : ℕ∞) < source.E.ncard from lt_of_lt_of_le (by norm_num) lower)
  obtain ⟨first, first_member, second, second_member, third, third_member,
    fourth, fourth_member, first_second, first_third, first_fourth,
    second_third, second_fourth, third_fourth⟩ :=
      (Set.three_lt_ncard source.ground_finite).mp ground_large
  let labels : Fin 4 → Label := ![first, second, third, fourth]
  have labels_injective : Function.Injective labels := by
    intro left right equality
    fin_cases left <;> fin_cases right <;> simp_all [labels]
  have labels_member (index : Fin 4) : labels index ∈ source.E := by
    fin_cases index <;> simp_all [labels]
  let selected : Set Label := Set.range labels
  let contracted : Set Label := source.E \ selected
  have selected_subset : selected ⊆ source.E := by
    rintro element ⟨index, rfl⟩
    exact labels_member index
  have first_base := compl_pair_isBase_of_simple_dual_corank_le_two corank
    first_member second_member first_second
  have contracted_indep : source.Indep contracted := first_base.indep.subset (by
    intro element member
    refine ⟨member.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact member.2 ⟨0, rfl⟩
    · exact member.2 ⟨1, rfl⟩)
  let smaller := source.contract contracted
  have smaller_ground : smaller.E = selected := by
    change source.E \ (source.E \ selected) = selected
    exact Set.sdiff_sdiff_cancel_left selected_subset
  have smaller_simple : smaller.Simple := by
    apply simple_iff_forall_pair_indep.mpr
    intro left right left_member right_member
    rw [smaller_ground] at left_member right_member
    obtain ⟨left_index, rfl⟩ := left_member
    obtain ⟨right_index, rfl⟩ := right_member
    have omitted : ∀ left right : Fin 4, ∃ omitted_first omitted_second : Fin 4,
        omitted_first ≠ omitted_second ∧ left ≠ omitted_first ∧ left ≠ omitted_second ∧
          right ≠ omitted_first ∧ right ≠ omitted_second := by decide
    obtain ⟨omitted_first, omitted_second, omitted_distinct, left_first, left_second,
      right_first, right_second⟩ := omitted left_index right_index
    have base := compl_pair_isBase_of_simple_dual_corank_le_two corank
      (labels_member omitted_first) (labels_member omitted_second)
      (labels_injective.ne omitted_distinct)
    apply contracted_indep.contract_indep_iff.mpr
    constructor
    · apply Set.disjoint_left.mpr
      intro element member outside
      apply outside.2
      rcases member with rfl | member
      · exact ⟨left_index, rfl⟩
      · have equality : element = labels right_index := member
        exact ⟨right_index, equality.symm⟩
    · apply base.indep.subset
      intro element member
      rcases member with member | member
      · rcases member with rfl | member
        · exact ⟨labels_member left_index, by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨labels_injective.ne left_first, labels_injective.ne left_second⟩⟩
        · have equality : element = labels right_index := member
          subst element
          exact ⟨labels_member right_index, by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨labels_injective.ne right_first, labels_injective.ne right_second⟩⟩
      · refine ⟨member.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rintro (rfl | rfl)
        · exact member.2 ⟨omitted_first, rfl⟩
        · exact member.2 ⟨omitted_second, rfl⟩
  have retained_base : smaller.IsBase {third, fourth} := by
    apply contracted_indep.contract_isBase_iff.mpr
    constructor
    · have equality : ({third, fourth} : Set Label) ∪ contracted =
          source.E \ {first, second} := by
        have selected_eq : selected = {first, second, third, fourth} := by
          ext element
          simp [selected, labels, or_comm, or_left_comm]
        rw [show contracted = source.E \ selected from rfl, selected_eq]
        ext element
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_sdiff]
        constructor
        · rintro ((rfl | rfl) | ⟨member, outside⟩)
          · exact ⟨third_member, by simp [Ne.symm first_third, Ne.symm second_third]⟩
          · exact ⟨fourth_member, by simp [Ne.symm first_fourth, Ne.symm second_fourth]⟩
          · exact ⟨member, fun forbidden => outside (by tauto)⟩
        · rintro ⟨member, outside⟩
          by_cases is_third : element = third
          · exact Or.inl (Or.inl is_third)
          by_cases is_fourth : element = fourth
          · exact Or.inl (Or.inr is_fourth)
          exact Or.inr ⟨member, by tauto⟩
      exact equality.symm ▸ first_base
    · apply Set.disjoint_left.mpr
      intro element member outside
      apply outside.2
      rcases member with rfl | member
      · exact ⟨2, rfl⟩
      · have equality : element = fourth := member
        exact ⟨3, equality.symm⟩
  have smaller_rank : smaller.eRank ≤ 2 := by
    rw [← retained_base.encard_eq_eRank, Set.encard_pair third_fourth]
  let : smaller.Finite := ⟨source.ground_finite.subset (contract_isMinor source contracted).subset⟩
  let : smaller.Simple := smaller_simple
  have bound := binary_simple_rank_two_ground_card_le_three
    (binary.contract contracted) smaller_rank
  have selected_card : selected.ncard = 4 := by
    rw [show selected = labels '' Set.univ by simp [selected],
      Set.ncard_image_of_injective _ labels_injective]
    simp
  rw [smaller_ground, selected_card] at bound
  omega

theorem binary_simple_cosimple_ground_encard_ge_six [source.Finite]
    [source.Simple] [source✶.Simple] (binary : source.Representable (ZMod 2))
    (nonempty : source.E.Nonempty) : 6 ≤ source.E.encard := by
  have ground_lower := simple_cosimple_ground_encard_ge_four (source := source) nonempty
  have rank_lower : 3 ≤ source.eRank := by
    by_contra small
    have low_rank : source.eRank ≤ 2 := (ENat.lt_add_one_iff (by simp)).mp (lt_of_not_ge small)
    have bound := binary_simple_rank_two_ground_card_le_three binary low_rank
    rw [← source.ground_finite.cast_ncard_eq] at ground_lower
    have ground_bound : (source.E.ncard : ℕ∞) ≤ 3 := by exact_mod_cast bound
    have impossible := ground_lower.trans ground_bound
    norm_num at impossible
  have corank_lower : 3 ≤ source✶.eRank := by
    by_contra small
    have low_corank : source✶.eRank ≤ 2 :=
      (ENat.lt_add_one_iff (by simp)).mp (lt_of_not_ge small)
    rcases binary_not_simple_cosimple_of_corank_le_two binary low_corank nonempty with
      not_simple | not_cosimple
    · exact not_simple inferInstance
    · exact not_cosimple inferInstance
  calc
    6 = (3 : ℕ∞) + 3 := by norm_num
    _ ≤ source.eRank + source✶.eRank := add_le_add rank_lower corank_lower
    _ = source.E.encard := source.eRank_add_eRank_dual

theorem binary_five_element_exists_elementary_reduction [source.Finite]
    (binary : source.Representable (ZMod 2)) (size : source.E.ncard ≤ 5)
    (nonempty : source.E.Nonempty) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced := by
  apply exists_elementary_reduction_of_not_simple_or_dual
  by_contra obstruction
  have both : source.Simple ∧ source✶.Simple := by tauto
  let : source.Simple := both.1
  let : source✶.Simple := both.2
  have lower := binary_simple_cosimple_ground_encard_ge_six binary nonempty
  rw [← source.ground_finite.cast_ncard_eq] at lower
  have lower_nat : 6 ≤ source.E.ncard := by exact_mod_cast lower
  omega

theorem IsMinor.dual {target : Matroid Label} (minor : target ≤m source) :
    target✶ ≤m source✶ := by
  obtain ⟨contracted, deleted, rfl⟩ := minor
  rw [dual_contract_delete, delete_contract_comm']
  exact contract_delete_isMinor _ _ _

end Matroid

