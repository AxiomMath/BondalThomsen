module

public import BondalThomsen.Matroid.MarkedTreeMatroidReconstruction

@[expose] public section

namespace BondalThomsen

open Set

def TreeBasisState : (tree : BinaryTree TreeMark) → Bool → Set (TreeLeaf tree) → Prop
  | .nil, true, selected => selected = Set.univ
  | .nil, false, selected => selected = ∅
  | .node .parallel left right, true, selected =>
    (TreeBasisState left true (Sum.inl ⁻¹' selected) ∧
      TreeBasisState right false (Sum.inr ⁻¹' selected)) ∨
    (TreeBasisState left false (Sum.inl ⁻¹' selected) ∧
      TreeBasisState right true (Sum.inr ⁻¹' selected))
  | .node .parallel left right, false, selected =>
    TreeBasisState left false (Sum.inl ⁻¹' selected) ∧
      TreeBasisState right false (Sum.inr ⁻¹' selected)
  | .node .series left right, true, selected =>
    TreeBasisState left true (Sum.inl ⁻¹' selected) ∧
      TreeBasisState right true (Sum.inr ⁻¹' selected)
  | .node .series left right, false, selected =>
    (TreeBasisState left true (Sum.inl ⁻¹' selected) ∧
      TreeBasisState right false (Sum.inr ⁻¹' selected)) ∨
    (TreeBasisState left false (Sum.inl ⁻¹' selected) ∧
      TreeBasisState right true (Sum.inr ⁻¹' selected))
  | .node .directSum left right, state, selected =>
    TreeBasisState left state (Sum.inl ⁻¹' selected) ∧
      TreeBasisState right state (Sum.inr ⁻¹' selected)

theorem preimage_inl_image_sumMap {Left Right NewLeft NewRight : Type*}
    (left : Left → NewLeft) (right : Right → NewRight) (selected : Set (Left ⊕ Right)) :
    Sum.inl ⁻¹' (Sum.map left right '' selected) = left '' (Sum.inl ⁻¹' selected) := by
  ext value
  constructor
  · rintro ⟨original, member, equality⟩
    cases original with
    | inl original => exact ⟨original, member, Sum.inl.inj equality⟩
    | inr original => exact (Sum.inr_ne_inl equality).elim
  · rintro ⟨original, member, rfl⟩
    exact ⟨.inl original, member, rfl⟩

theorem preimage_inr_image_sumMap {Left Right NewLeft NewRight : Type*}
    (left : Left → NewLeft) (right : Right → NewRight) (selected : Set (Left ⊕ Right)) :
    Sum.inr ⁻¹' (Sum.map left right '' selected) = right '' (Sum.inr ⁻¹' selected) := by
  ext value
  constructor
  · rintro ⟨original, member, equality⟩
    cases original with
    | inl original => exact (Sum.inl_ne_inr equality).elim
    | inr original => exact ⟨original, member, Sum.inr.inj equality⟩
  · rintro ⟨original, member, rfl⟩
    exact ⟨.inr original, member, rfl⟩

theorem injOn_sumMap_iff {Left Right NewLeft NewRight : Type*}
    (left : Left → NewLeft) (right : Right → NewRight) (selected : Set (Left ⊕ Right)) :
    Set.InjOn (Sum.map left right) selected ↔
      Set.InjOn left (Sum.inl ⁻¹' selected) ∧ Set.InjOn right (Sum.inr ⁻¹' selected) := by
  constructor
  · intro injective
    constructor
    · intro first first_member second second_member equality
      exact Sum.inl.inj (injective first_member second_member (congrArg Sum.inl equality))
    · intro first first_member second second_member equality
      exact Sum.inr.inj (injective first_member second_member (congrArg Sum.inr equality))
  · rintro ⟨left_injective, right_injective⟩ (first | first) first_member
      (second | second) second_member equality
    · exact congrArg Sum.inl (left_injective first_member second_member (Sum.inl.inj equality))
    · exact (Sum.inl_ne_inr equality).elim
    · exact (Sum.inr_ne_inl equality).elim
    · exact congrArg Sum.inr (right_injective first_member second_member (Sum.inr.inj equality))

theorem unit_preimage_eq {Left : Type*} (selected : Set Left) (element : Left) :
    ((fun _ : Unit => element) ⁻¹' selected = Set.univ ↔ element ∈ selected) ∧
    ((fun _ : Unit => element) ⁻¹' selected = ∅ ↔ element ∉ selected) := by
  constructor
  · constructor
    · intro equality
      exact Set.ext_iff.mp equality () |>.mpr (Set.mem_univ _)
    · intro member
      ext original
      simp [member]
  · constructor
    · intro equality member
      exact Set.ext_iff.mp equality () |>.mp member
    · intro absent
      ext original
      simp [absent]

theorem singleton_parallel_basis_state (state : Bool) (selected : Set (Unit ⊕ Unit)) :
    TreeBasisState (.node .parallel .nil .nil) state selected ↔
      TreeBasisState .nil state ((fun _ : Unit ⊕ Unit => ()) '' selected) ∧
        Set.InjOn (fun _ : Unit ⊕ Unit => ()) selected := by
  have left := unit_preimage_eq selected (.inl ())
  have right := unit_preimage_eq selected (.inr ())
  have image_full : (fun _ : Unit ⊕ Unit => ()) '' selected = Set.univ ↔
      (.inl () ∈ selected ∨ .inr () ∈ selected) := by
    constructor
    · intro equality
      obtain ⟨original, member, equal⟩ := Set.ext_iff.mp equality () |>.mpr (Set.mem_univ _)
      cases original with
      | inl original => cases original; exact Or.inl member
      | inr original => cases original; exact Or.inr member
    · intro member
      ext original
      cases original
      simp only [Set.mem_image, Set.mem_univ, iff_true]
      rcases member with member | member
      · exact ⟨.inl (), member, trivial⟩
      · exact ⟨.inr (), member, trivial⟩
  have image_empty : (fun _ : Unit ⊕ Unit => ()) '' selected = ∅ ↔
      (.inl () ∉ selected ∧ .inr () ∉ selected) := by
    rw [Set.image_eq_empty]
    constructor
    · rintro rfl
      simp
    · rintro ⟨left_absent, right_absent⟩
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro (original | original) member
      · cases original; exact left_absent member
      · cases original; exact right_absent member
  have injective : Set.InjOn (fun _ : Unit ⊕ Unit => ()) selected ↔
      ¬(.inl () ∈ selected ∧ .inr () ∈ selected) := by
    constructor
    · intro injective both
      exact Sum.inl_ne_inr (injective both.1 both.2 rfl)
    · intro avoids
      rintro (first | first) first_member (second | second) second_member equality
      · cases first; cases second; rfl
      · cases first; cases second; exact (avoids ⟨first_member, second_member⟩).elim
      · cases first; cases second; exact (avoids ⟨second_member, first_member⟩).elim
      · cases first; cases second; rfl
  cases state <;> simp only [TreeBasisState, injective] <;> tauto

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem treeBasisState_parallel_refinement (tree : BinaryTree TreeMark)
    (leaf : TreeLeaf tree) (state : Bool)
    (selected : Set (TreeLeaf (refineTreeLeaf tree leaf .parallel))) :
    TreeBasisState (refineTreeLeaf tree leaf .parallel) state selected ↔
      TreeBasisState tree state (refinedLeafFold tree leaf .parallel '' selected) ∧
        Set.InjOn (refinedLeafFold tree leaf .parallel) selected := by
  induction tree generalizing state with
  | nil => exact singleton_parallel_basis_state state selected
  | node root left right left_refinement right_refinement =>
    cases leaf with
    | inl leaf =>
      have fold_eq : refinedLeafFold (.node root left right) (.inl leaf) .parallel =
          Sum.map (refinedLeafFold left leaf .parallel) id := by
        funext original
        cases original <;> rfl
      cases root <;> cases state <;> dsimp only [TreeLeaf, refineTreeLeaf] at * <;>
        simp only [TreeBasisState, fold_eq,
          preimage_inl_image_sumMap, preimage_inr_image_sumMap, Set.image_id,
          injOn_sumMap_iff, Set.injOn_id, and_true,
          left_refinement leaf false, left_refinement leaf true] <;> tauto
    | inr leaf =>
      have fold_eq : refinedLeafFold (.node root left right) (.inr leaf) .parallel =
          Sum.map id (refinedLeafFold right leaf .parallel) := by
        funext original
        cases original <;> rfl
      cases root <;> cases state <;> dsimp only [TreeLeaf, refineTreeLeaf] at * <;>
        simp only [TreeBasisState, fold_eq,
          preimage_inl_image_sumMap, preimage_inr_image_sumMap, Set.image_id,
          injOn_sumMap_iff, Set.injOn_id, true_and,
          right_refinement leaf false, right_refinement leaf true] <;> tauto

theorem shape_compl_eq_empty {Value : Type*} (chosen : Set Value) :
    chosenᶜ = ∅ ↔ chosen = Set.univ := compl_eq_bot

theorem shape_compl_eq_univ {Value : Type*} (chosen : Set Value) :
    chosenᶜ = Set.univ ↔ chosen = ∅ := compl_eq_top

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem singleton_series_basis_state (state : Bool) (selected : Set (Unit ⊕ Unit)) :
    TreeBasisState (.node .series .nil .nil) state selected ↔
      TreeBasisState .nil state ((fun _ : Unit ⊕ Unit => ()) '' selectedᶜ)ᶜ ∧
        Set.InjOn (fun _ : Unit ⊕ Unit => ()) selectedᶜ := by
  have parallel := singleton_parallel_basis_state (!state) selectedᶜ
  cases state <;>
    simp only [TreeBasisState, Bool.not_false, Bool.not_true, Set.preimage_compl,
      shape_compl_eq_empty, shape_compl_eq_univ] at parallel ⊢ <;> tauto

theorem preimage_inl_compl_image_sumMap {Left Right NewLeft NewRight : Type*}
    (left : Left → NewLeft) (right : Right → NewRight) (selected : Set (Left ⊕ Right)) :
    Sum.inl ⁻¹' (Sum.map left right '' selectedᶜ)ᶜ =
      (left '' (Sum.inl ⁻¹' selected)ᶜ)ᶜ := by
  rw [Set.preimage_compl, preimage_inl_image_sumMap, Set.preimage_compl]

theorem preimage_inr_compl_image_sumMap {Left Right NewLeft NewRight : Type*}
    (left : Left → NewLeft) (right : Right → NewRight) (selected : Set (Left ⊕ Right)) :
    Sum.inr ⁻¹' (Sum.map left right '' selectedᶜ)ᶜ =
      (right '' (Sum.inr ⁻¹' selected)ᶜ)ᶜ := by
  rw [Set.preimage_compl, preimage_inr_image_sumMap, Set.preimage_compl]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem treeBasisState_series_refinement (tree : BinaryTree TreeMark)
    (leaf : TreeLeaf tree) (state : Bool)
    (selected : Set (TreeLeaf (refineTreeLeaf tree leaf .series))) :
    TreeBasisState (refineTreeLeaf tree leaf .series) state selected ↔
      TreeBasisState tree state (refinedLeafFold tree leaf .series '' selectedᶜ)ᶜ ∧
        Set.InjOn (refinedLeafFold tree leaf .series) selectedᶜ := by
  induction tree generalizing state with
  | nil => exact singleton_series_basis_state state selected
  | node root left right left_refinement right_refinement =>
    cases leaf with
    | inl leaf =>
      have fold_eq : refinedLeafFold (.node root left right) (.inl leaf) .series =
          Sum.map (refinedLeafFold left leaf .series) id := by
        funext original
        cases original <;> rfl
      have left_image := preimage_inl_compl_image_sumMap
        (refinedLeafFold left leaf .series) id selected
      have right_image := preimage_inr_compl_image_sumMap
        (refinedLeafFold left leaf .series) id selected
      have fold_injective := injOn_sumMap_iff
        (refinedLeafFold left leaf .series) id selectedᶜ
      cases root <;> cases state <;> dsimp only [TreeLeaf, refineTreeLeaf] at * <;>
        simp only [TreeBasisState, fold_eq,
          left_image, right_image, fold_injective, Set.preimage_compl,
          Set.image_id,
          Set.injOn_id, and_true, compl_compl,
          left_refinement leaf false, left_refinement leaf true] <;> tauto
    | inr leaf =>
      have fold_eq : refinedLeafFold (.node root left right) (.inr leaf) .series =
          Sum.map id (refinedLeafFold right leaf .series) := by
        funext original
        cases original <;> rfl
      have left_image := preimage_inl_compl_image_sumMap
        id (refinedLeafFold right leaf .series) selected
      have right_image := preimage_inr_compl_image_sumMap
        id (refinedLeafFold right leaf .series) selected
      have fold_injective := injOn_sumMap_iff
        id (refinedLeafFold right leaf .series) selectedᶜ
      cases root <;> cases state <;> dsimp only [TreeLeaf, refineTreeLeaf] at * <;>
        simp only [TreeBasisState, fold_eq,
          left_image, right_image, fold_injective, Set.preimage_compl,
          Set.image_id,
          Set.injOn_id, true_and, compl_compl,
          right_refinement leaf false, right_refinement leaf true] <;> tauto

namespace LabelledMarkedExtensionTree

theorem Valid.parallel_leafMatroid_eq_comap {Label : Type*} [DecidableEq Label]
    {tree : BinaryTree TreeMark} {previous : LabelledMarkedExtensionTree Label tree}
    {leaf : TreeLeaf tree} {added : Label}
    (valid : (previous.parallel leaf added).Valid) :
    (previous.parallel leaf added).leafMatroid =
      previous.leafMatroid.comap (refinedLeafFold tree leaf .parallel) := by
  apply Matroid.ext_indep
  · rw [(previous.parallel leaf added).leafMatroid_ground, Matroid.comap_ground_eq,
      previous.leafMatroid_ground, Set.preimage_univ]
  · intro selected subset_ground
    rw [Matroid.comap_indep_iff]
    exact (valid.parallel_sibling_fold selected).trans and_comm

theorem Valid.series_dual_leafMatroid_eq_comap {Label : Type*} [DecidableEq Label]
    {tree : BinaryTree TreeMark} {previous : LabelledMarkedExtensionTree Label tree}
    {leaf : TreeLeaf tree} {added : Label}
    (valid : (previous.series leaf added).Valid) :
    (previous.series leaf added).leafMatroid✶ =
      previous.leafMatroid✶.comap (refinedLeafFold tree leaf .series) := by
  apply Matroid.ext_indep
  · rw [Matroid.dual_ground, (previous.series leaf added).leafMatroid_ground,
      Matroid.comap_ground_eq, Matroid.dual_ground,
      previous.leafMatroid_ground, Set.preimage_univ]
  · intro selected subset_ground
    rw [Matroid.comap_indep_iff]
    exact (valid.series_sibling_fold selected).trans and_comm

theorem Valid.parallel_leafMatroid_isBase_iff {Label : Type*} [DecidableEq Label]
    {tree : BinaryTree TreeMark} {previous : LabelledMarkedExtensionTree Label tree}
    {leaf : TreeLeaf tree} {added : Label}
    (valid : (previous.parallel leaf added).Valid)
    (selected : Set (TreeLeaf (refineTreeLeaf tree leaf .parallel))) :
    (previous.parallel leaf added).leafMatroid.IsBase selected ↔
      previous.leafMatroid.IsBase (refinedLeafFold tree leaf .parallel '' selected) ∧
        Set.InjOn (refinedLeafFold tree leaf .parallel) selected := by
  rw [valid.parallel_leafMatroid_eq_comap, Matroid.comap_isBase_iff,
    previous.leafMatroid_ground, Set.preimage_univ, Set.image_univ,
    (refinedLeafFold_surjective tree leaf .parallel).range_eq,
    ← previous.leafMatroid_ground, Matroid.isBasis_ground_iff,
    and_iff_left (Set.subset_univ _)]

theorem Valid.series_leafMatroid_isBase_iff {Label : Type*} [DecidableEq Label]
    {tree : BinaryTree TreeMark} {previous : LabelledMarkedExtensionTree Label tree}
    {leaf : TreeLeaf tree} {added : Label}
    (valid : (previous.series leaf added).Valid)
    (selected : Set (TreeLeaf (refineTreeLeaf tree leaf .series))) :
    (previous.series leaf added).leafMatroid.IsBase selected ↔
      previous.leafMatroid.IsBase (refinedLeafFold tree leaf .series '' selectedᶜ)ᶜ ∧
        Set.InjOn (refinedLeafFold tree leaf .series) selectedᶜ := by
  have selected_subset : selected ⊆ (previous.series leaf added).leafMatroid.E := by
    rw [(previous.series leaf added).leafMatroid_ground]
    exact Set.subset_univ _
  have image_subset : refinedLeafFold tree leaf .series '' selectedᶜ ⊆
      previous.leafMatroid.E := by
    rw [previous.leafMatroid_ground]
    exact Set.subset_univ _
  rw [Matroid.base_iff_dual_isBase_compl selected_subset,
    (previous.series leaf added).leafMatroid_ground, ← Set.compl_eq_univ_sdiff,
    valid.series_dual_leafMatroid_eq_comap, Matroid.comap_isBase_iff,
    Matroid.dual_ground, previous.leafMatroid_ground, Set.preimage_univ,
    Set.image_univ, (refinedLeafFold_surjective tree leaf .series).range_eq,
    ← previous.leafMatroid_ground, ← Matroid.dual_ground (M := previous.leafMatroid),
    Matroid.isBasis_ground_iff, Matroid.dual_isBase_iff image_subset,
    previous.leafMatroid_ground, ← Set.compl_eq_univ_sdiff,
    and_iff_left (Set.subset_univ _)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem Valid.leafMatroid_isBase_shape_iff {Label : Type*} [DecidableEq Label]
    {tree : BinaryTree TreeMark} {construction : LabelledMarkedExtensionTree Label tree}
    (valid : construction.Valid) (selected : Set (TreeLeaf tree)) :
    construction.leafMatroid.IsBase selected ↔ TreeBasisState tree true selected := by
  induction construction with
  | singleton label =>
    change ((Matroid.freeOn {label}).comap (fun _ : Unit => label)).IsBase selected ↔
      selected = Set.univ
    rw [Matroid.comap_isBase_iff]
    have image_ground : (fun _ : Unit => label) ''
        ((fun _ : Unit => label) ⁻¹' (Matroid.freeOn {label}).E) = {label} := by
      ext value
      simp
    rw [image_ground]
    have basis_ground : (Matroid.freeOn {label}).IsBasis
        ((fun _ : Unit => label) '' selected) {label} ↔
        (Matroid.freeOn {label}).IsBase ((fun _ : Unit => label) '' selected) :=
      Matroid.isBasis_ground_iff
    rw [basis_ground, Matroid.freeOn_isBase_iff]
    have injective : Set.InjOn (fun _ : Unit => label) selected := by
      intro first first_member second second_member equality
      exact Subsingleton.elim _ _
    have subset_ground : selected ⊆
        (fun _ : Unit => label) ⁻¹' (Matroid.freeOn {label}).E := by
      intro original member
      simp
    rw [and_iff_left subset_ground, and_iff_left injective]
    constructor
    · intro equality
      obtain ⟨original, member, equal⟩ := Set.ext_iff.mp equality label |>.mpr (by simp)
      apply Set.eq_univ_iff_forall.mpr
      intro other
      exact (Subsingleton.elim original other) ▸ member
    · rintro rfl
      ext value
      simp
  | parallel previous leaf added induction =>
    rw [valid.parallel_leafMatroid_isBase_iff, induction valid.1,
      treeBasisState_parallel_refinement]
  | series previous leaf added induction =>
    rw [valid.series_leafMatroid_isBase_iff, induction valid.1,
      treeBasisState_series_refinement]

end LabelledMarkedExtensionTree

end BondalThomsen
