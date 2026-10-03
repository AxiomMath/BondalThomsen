module

public import BondalThomsen.Matroid.ConnectedMatroidForestReconstruction
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace BondalThomsen

open Set

def sigmaFinSuccComponentEquiv {count : ℕ} (fiber : Fin (count + 1) → Type*) :
    (component : Fin (count + 1)) × fiber component ≃
      fiber 0 ⊕ (component : Fin count) × fiber component.succ where
  toFun element := Fin.cases (fun leaf => Sum.inl leaf)
    (fun component leaf => Sum.inr ⟨component, leaf⟩) element.1 element.2
  invFun
    | .inl leaf => ⟨0, leaf⟩
    | .inr ⟨component, leaf⟩ => ⟨component.succ, leaf⟩
  left_inv := by
    rintro ⟨component, leaf⟩
    refine Fin.cases ?_ ?_ component leaf
    · intro leaf
      rfl
    · intro component leaf
      rfl
  right_inv := by
    rintro (leaf | ⟨component, leaf⟩) <;> rfl

def indexedComponentTree : (count : ℕ) →
    (Fin (count + 1) → BinaryTree TreeMark) → BinaryTree TreeMark
  | 0, trees => trees 0
  | count + 1, trees =>
    .node .directSum (trees 0) (indexedComponentTree count (fun component => trees component.succ))

theorem indexedComponentTree_valid (count : ℕ) (trees : Fin (count + 1) → BinaryTree TreeMark)
    (components : ∀ component, TreeHasNoDirectSum (trees component)) :
    ComponentTreeShape (indexedComponentTree count trees) := by
  induction count with
  | zero => exact noDirectSum_componentTreeShape _ (components 0)
  | succ count induction =>
    exact ⟨noDirectSum_componentTreeShape _ (components 0),
      induction (fun component => trees component.succ) (fun component => components component.succ)⟩

def indexedComponentLeafEquiv : (count : ℕ) →
    (trees : Fin (count + 1) → BinaryTree TreeMark) →
    TreeLeaf (indexedComponentTree count trees) ≃
      (component : Fin (count + 1)) × TreeLeaf (trees component)
  | 0, trees =>
    { toFun := fun leaf => ⟨0, leaf⟩
      invFun := fun element => by
        change TreeLeaf (trees 0)
        exact (Fin.eq_zero element.1) ▸ element.2
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨component, leaf⟩
        have equality := Fin.eq_zero component
        subst component
        rfl }
  | count + 1, trees =>
    (Equiv.sumCongr (Equiv.refl (TreeLeaf (trees 0)))
      (indexedComponentLeafEquiv count (fun component => trees component.succ))).trans
        (sigmaFinSuccComponentEquiv (fun component => TreeLeaf (trees component))).symm

theorem indexedComponentTree_numLeaves (count : ℕ)
    (trees : Fin (count + 1) → BinaryTree TreeMark) :
    (indexedComponentTree count trees).numLeaves = ∑ component, (trees component).numLeaves := by
  induction count with
  | zero => simp [indexedComponentTree]
  | succ count induction =>
    rw [indexedComponentTree, BinaryTree.numLeaves, induction]
    exact (Fin.sum_univ_succ (fun component => (trees component).numLeaves)).symm

theorem sigmaFinSuccComponentEquiv_zero_preimage {count : ℕ}
    (fiber : Fin (count + 1) → Type*) (selected : Set (fiber 0 ⊕ (component : Fin count) ×
      fiber component.succ)) :
    Sigma.mk 0 ⁻¹' ((sigmaFinSuccComponentEquiv fiber).symm '' selected) =
      Sum.inl ⁻¹' selected := by
  ext leaf
  rw [Equiv.image_eq_preimage_symm]
  rfl

theorem sigmaFinSuccComponentEquiv_succ_preimage {count : ℕ}
    (fiber : Fin (count + 1) → Type*) (selected : Set (fiber 0 ⊕ (component : Fin count) ×
      fiber component.succ)) (component : Fin count) :
    Sigma.mk component.succ ⁻¹' ((sigmaFinSuccComponentEquiv fiber).symm '' selected) =
      Sigma.mk component ⁻¹' (Sum.inr ⁻¹' selected) := by
  ext leaf
  rw [Equiv.image_eq_preimage_symm]
  rfl

theorem indexedComponentLeafEquiv_indep (count : ℕ)
    (trees : Fin (count + 1) → BinaryTree TreeMark)
    (components : ∀ component, TreeHasNoDirectSum (trees component))
    (selected : Set (TreeLeaf (indexedComponentTree count trees))) :
    (componentTreeMatroid (indexedComponentTree count trees)
      (indexedComponentTree_valid count trees components)).Indep selected ↔
      (Matroid.sigma fun component => seriesParallelTreeMatroid (trees component)
        (components component)).Indep (indexedComponentLeafEquiv count trees '' selected) := by
  induction count with
  | zero =>
    rw [Matroid.sigma_indep_iff]
    have fiber_image : Sigma.mk (0 : Fin 1) ⁻¹'
        (indexedComponentLeafEquiv 0 trees '' selected) = selected := by
      ext leaf
      change (∃ original ∈ selected, (⟨0, original⟩ :
        (component : Fin 1) × TreeLeaf (trees component)) = ⟨0, leaf⟩) ↔ leaf ∈ selected
      constructor
      · rintro ⟨original, member, equality⟩
        have same : original = leaf := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using equality
        exact same ▸ member
      · intro member
        exact ⟨leaf, member, rfl⟩
    change _ ↔ ∀ component : Fin 1, _
    rw [Fin.forall_fin_one, fiber_image]
    exact Iff.of_eq (congrArg (fun source : Matroid (TreeLeaf (trees 0)) => source.Indep selected)
      (componentTreeMatroid_eq_seriesParallel (trees 0) (components 0)))
  | succ count induction =>
    change ((componentTreeMatroid (trees 0) _).sum
      (componentTreeMatroid (indexedComponentTree count (fun component => trees component.succ)) _)).Indep
      selected ↔ _
    rw [Matroid.sum_indep_iff,
      componentTreeMatroid_eq_seriesParallel (trees 0) (components 0),
      induction (fun component => trees component.succ) (fun component => components component.succ),
      Matroid.sigma_indep_iff, Matroid.sigma_indep_iff]
    have image_split : indexedComponentLeafEquiv (count + 1) trees '' selected =
        (sigmaFinSuccComponentEquiv (fun component => TreeLeaf (trees component))).symm ''
          (Sum.map id (indexedComponentLeafEquiv count (fun component => trees component.succ)) ''
            selected) := by
      rw [Set.image_image]
      rfl
    rw [image_split]
    conv_rhs => rw [Fin.forall_fin_succ]
    rw [sigmaFinSuccComponentEquiv_zero_preimage]
    simp only [sigmaFinSuccComponentEquiv_succ_preimage,
      preimage_inl_image_sumMap, preimage_inr_image_sumMap, Set.image_id]

noncomputable def indexedComponentTreeIso (count : ℕ)
    (trees : Fin (count + 1) → BinaryTree TreeMark)
    (components : ∀ component, TreeHasNoDirectSum (trees component)) :
    Matroid.Iso
      (componentTreeMatroid (indexedComponentTree count trees)
        (indexedComponentTree_valid count trees components))
      (Matroid.sigma fun component => seriesParallelTreeMatroid (trees component)
        (components component)) := by
  let source := componentTreeMatroid (indexedComponentTree count trees)
    (indexedComponentTree_valid count trees components)
  let target := Matroid.sigma fun component => seriesParallelTreeMatroid (trees component)
    (components component)
  have source_ground : source.E = Set.univ := componentTreeMatroid_ground _ _
  have target_ground : target.E = Set.univ := by
    ext leaf
    simp [target, Matroid.sigma_ground_eq, seriesParallelTreeMatroid_ground]
  let equivalence : source.E ≃ target.E :=
    { toFun := fun leaf => ⟨indexedComponentLeafEquiv count trees leaf.val,
        target_ground ▸ Set.mem_univ _⟩
      invFun := fun leaf => ⟨(indexedComponentLeafEquiv count trees).symm leaf.val,
        source_ground ▸ Set.mem_univ _⟩
      left_inv := fun leaf => Subtype.ext ((indexedComponentLeafEquiv count trees).symm_apply_apply _)
      right_inv := fun leaf => Subtype.ext ((indexedComponentLeafEquiv count trees).apply_symm_apply _) }
  refine ⟨equivalence, ?_⟩
  intro selected
  rw [indexedComponentLeafEquiv_indep count trees components]
  apply Iff.of_eq
  apply congrArg target.Indep
  ext leaf
  constructor
  · rintro ⟨original, ⟨ground_leaf, member, rfl⟩, rfl⟩
    exact ⟨equivalence ground_leaf, ⟨ground_leaf, member, rfl⟩, rfl⟩
  · rintro ⟨original, ⟨ground_leaf, member, rfl⟩, rfl⟩
    exact ⟨ground_leaf.val, ⟨ground_leaf, member, rfl⟩, rfl⟩

theorem sigmaTreeMatroid_reindex_indep {Component OtherComponent : Type*}
    (equivalence : OtherComponent ≃ Component) (trees : Component → BinaryTree TreeMark)
    (components : ∀ component, TreeHasNoDirectSum (trees component))
    (selected : Set ((component : OtherComponent) × TreeLeaf (trees (equivalence component)))) :
    (Matroid.sigma fun component => seriesParallelTreeMatroid (trees (equivalence component))
      (components (equivalence component))).Indep selected ↔
      (Matroid.sigma fun component => seriesParallelTreeMatroid (trees component)
        (components component)).Indep
      (Equiv.sigmaCongrLeft (β := fun component => TreeLeaf (trees component)) equivalence '' selected) := by
  rw [Matroid.sigma_indep_iff, Matroid.sigma_indep_iff]
  have fiber_image : ∀ component, Sigma.mk (equivalence component) ⁻¹'
      (Equiv.sigmaCongrLeft (β := fun component => TreeLeaf (trees component)) equivalence '' selected) =
        Sigma.mk component ⁻¹' selected := by
    intro component
    ext leaf
    rw [Equiv.image_eq_preimage_symm]
    change (Equiv.sigmaCongrLeft (β := fun component => TreeLeaf (trees component)) equivalence).symm
      ⟨equivalence component, leaf⟩ ∈ selected ↔
      (⟨component, leaf⟩ : (component : OtherComponent) × TreeLeaf (trees (equivalence component))) ∈ selected
    rw [show (Equiv.sigmaCongrLeft (β := fun component => TreeLeaf (trees component)) equivalence).symm
        ⟨equivalence component, leaf⟩ =
        ⟨component, leaf⟩ from
      (Equiv.sigmaCongrLeft (β := fun component => TreeLeaf (trees component)) equivalence).symm_apply_apply
        ⟨component, leaf⟩]
  constructor
  · intro independent component
    obtain ⟨other, rfl⟩ := equivalence.surjective component
    rw [fiber_image]
    exact independent other
  · intro independent component
    have component_independent := independent (equivalence component)
    rw [fiber_image] at component_independent
    exact component_independent

noncomputable def sigmaTreeMatroidReindexIso {Component OtherComponent : Type*}
    (equivalence : OtherComponent ≃ Component) (trees : Component → BinaryTree TreeMark)
    (components : ∀ component, TreeHasNoDirectSum (trees component)) :
    Matroid.Iso
      (Matroid.sigma fun component => seriesParallelTreeMatroid (trees (equivalence component))
        (components (equivalence component)))
      (Matroid.sigma fun component => seriesParallelTreeMatroid (trees component)
        (components component)) := by
  let source := Matroid.sigma fun component => seriesParallelTreeMatroid (trees (equivalence component))
    (components (equivalence component))
  let target := Matroid.sigma fun component => seriesParallelTreeMatroid (trees component)
    (components component)
  have source_ground : source.E = Set.univ := by
    ext leaf
    simp [source, Matroid.sigma_ground_eq, seriesParallelTreeMatroid_ground]
  have target_ground : target.E = Set.univ := by
    ext leaf
    simp [target, Matroid.sigma_ground_eq, seriesParallelTreeMatroid_ground]
  let leaf_equiv := Equiv.sigmaCongrLeft (β := fun component => TreeLeaf (trees component)) equivalence
  let ground_equiv : source.E ≃ target.E :=
    { toFun := fun leaf => ⟨leaf_equiv leaf.val, target_ground ▸ Set.mem_univ _⟩
      invFun := fun leaf => ⟨leaf_equiv.symm leaf.val, source_ground ▸ Set.mem_univ _⟩
      left_inv := fun leaf => Subtype.ext (leaf_equiv.symm_apply_apply _)
      right_inv := fun leaf => Subtype.ext (leaf_equiv.apply_symm_apply _) }
  refine ⟨ground_equiv, ?_⟩
  intro selected
  rw [sigmaTreeMatroid_reindex_indep]
  apply Iff.of_eq
  apply congrArg target.Indep
  ext leaf
  constructor
  · rintro ⟨original, ⟨ground_leaf, member, rfl⟩, rfl⟩
    exact ⟨ground_equiv ground_leaf, ⟨ground_leaf, member, rfl⟩, rfl⟩
  · rintro ⟨original, ⟨ground_leaf, member, rfl⟩, rfl⟩
    exact ⟨ground_leaf.val, ⟨ground_leaf, member, rfl⟩, rfl⟩

theorem finiteComponentFamily_exists_tree_iso {Component : Type*} [Fintype Component]
    [Nonempty Component] (trees : Component → BinaryTree TreeMark)
    (components : ∀ component, TreeHasNoDirectSum (trees component)) :
    ∃ tree : BinaryTree TreeMark, ∃ valid : ComponentTreeShape tree,
      Nonempty (Matroid.Iso (componentTreeMatroid tree valid)
        (Matroid.sigma fun component => seriesParallelTreeMatroid (trees component)
          (components component))) ∧ tree.numLeaves = ∑ component, (trees component).numLeaves := by
  classical
  have positive := Fintype.card_pos (α := Component)
  obtain ⟨count, size⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  let equivalence : Fin (count + 1) ≃ Component :=
    (finCongr size.symm).trans (Fintype.equivFin Component).symm
  let reordered := fun component => trees (equivalence component)
  let reordered_components := fun component => components (equivalence component)
  refine ⟨indexedComponentTree count reordered,
    indexedComponentTree_valid count reordered reordered_components,
    ⟨(indexedComponentTreeIso count reordered reordered_components).trans
      (sigmaTreeMatroidReindexIso equivalence trees components)⟩, ?_⟩
  rw [indexedComponentTree_numLeaves]
  exact Fintype.sum_equiv equivalence _ _ (fun _ => rfl)

namespace ConnectedComponentForest

theorem exists_single_tree_iso {Label : Type*} [DecidableEq Label]
    {source : Matroid Label} [source.Finite]
    (forest : ConnectedComponentForest source) (nonempty : source.E.Nonempty) :
    ∃ tree : BinaryTree TreeMark, ∃ valid : ComponentTreeShape tree,
      Nonempty (Matroid.Iso (componentTreeMatroid tree valid) source) ∧
        tree.numLeaves = source.E.ncard := by
  classical
  let := Fintype.ofFinite source.ConnectedComponent
  obtain ⟨label, member⟩ := nonempty
  let component : source.ConnectedComponent :=
    ⟨source.connectedComponentSet ⟨label, member⟩, ⟨⟨label, member⟩, rfl⟩⟩
  let : Nonempty source.ConnectedComponent := ⟨component⟩
  obtain ⟨tree, valid, ⟨isomorphism⟩, leaves⟩ :=
    finiteComponentFamily_exists_tree_iso forest.tree forest.tree_noDirectSum
  refine ⟨tree, valid, ⟨isomorphism.trans forest.iso⟩, ?_⟩
  exact leaves.trans forest.totalLeaves_eq

end ConnectedComponentForest

end BondalThomsen
