module

public import BondalThomsen.Matroid.TreeShapeDirectSumInterpretation
public import BondalThomsen.Matroid.ConnectedComponents
public import BondalThomsen.Matroid.DisconnectedDecomposition

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace Matroid

variable {Label : Type*} {source : Matroid Label}

theorem loopless_singleton_eq_freeOn [source.Loopless]
    (size : source.E.ncard = 1) : ∃ label, source = freeOn {label} := by
  obtain ⟨label, ground⟩ := Set.ncard_eq_one.mp size
  refine ⟨label, eq_freeOn_iff.mpr ⟨ground, ?_⟩⟩
  rw [← ground]
  have nonloop := source.isNonloop_of_loopless (ground ▸ Set.mem_singleton label)
  simpa only [ground] using nonloop.indep

theorem connected_exists_extension_tree_of_marked_trace [DecidableEq Label]
    [source.Finite] [source.Loopless]
    (connected : source.Connected)
    (reducible : 2 ≤ source.E.ncard →
      ∃ marked target length, target.E.ncard = 2 ∧
        MarkedConnectedReductionTrace marked source target length) :
    ∃ (tree : BinaryTree BondalThomsen.TreeMark)
      (construction : BondalThomsen.LabelledMarkedExtensionTree Label tree),
      construction.Valid ∧ construction.interpret = source := by
  classical
  have positive : 0 < source.E.ncard :=
    connected.nonempty.ground_nonempty.ncard_pos source.ground_finite
  by_cases singleton : source.E.ncard = 1
  · obtain ⟨label, equality⟩ := loopless_singleton_eq_freeOn singleton
    exact ⟨.nil, .singleton label, trivial, equality.symm⟩
  · obtain ⟨marked, target, length, size, trace⟩ := reducible (by omega)
    obtain ⟨tree, construction, valid, equality, _, _, _⟩ :=
      trace.exists_labelled_extension_tree size
    exact ⟨tree, construction, valid, equality⟩

end Matroid

namespace BondalThomsen

variable {Label : Type*} (source : Matroid Label)

structure ConnectedComponentForest [DecidableEq Label] where
  tree : source.ConnectedComponent → BinaryTree TreeMark
  construction : ∀ component, LabelledMarkedExtensionTree Label (tree component)
  valid : ∀ component, (construction component).Valid
  interpret_eq : ∀ component, (construction component).interpret = source.componentMatroid component

namespace ConnectedComponentForest

variable [DecidableEq Label] {source : Matroid Label}
    (forest : ConnectedComponentForest source)

abbrev Leaf := (component : source.ConnectedComponent) × TreeLeaf (forest.tree component)

def labels (leaf : forest.Leaf) : Label := (forest.construction leaf.1).labels leaf.2

noncomputable def matroid : Matroid forest.Leaf :=
  Matroid.sigma fun component =>
    seriesParallelTreeMatroid (forest.tree component) (forest.construction component).no_directSum

theorem matroid_ground : forest.matroid.E = Set.univ := by
  ext leaf
  simp [matroid, Matroid.sigma_ground_eq, seriesParallelTreeMatroid_ground]

theorem labels_mem (leaf : forest.Leaf) : forest.labels leaf ∈ leaf.1.val := by
  have member : (forest.construction leaf.1).labels leaf.2 ∈
      (forest.construction leaf.1).interpret.E := by
    rw [(forest.construction leaf.1).interpret_ground]
    exact ⟨leaf.2, rfl⟩
  simpa only [forest.interpret_eq, Matroid.componentMatroid_ground, labels] using member

theorem labels_injective : Function.Injective forest.labels := by
  intro first second equality
  have components : first.1 = second.1 := by
    by_contra distinct
    exact Set.disjoint_left.mp (source.componentMatroid_pairwise_disjoint distinct)
      (forest.labels_mem first) (equality ▸ forest.labels_mem second)
  rcases first with ⟨component, first⟩
  rcases second with ⟨other, second⟩
  dsimp at components
  subst other
  exact congrArg (Sigma.mk component)
    ((forest.valid component).labels_injective equality)

theorem labels_range : Set.range forest.labels = source.E := by
  apply Set.Subset.antisymm
  · rintro label ⟨leaf, rfl⟩
    exact source.component_subset_ground leaf.1 (forest.labels_mem leaf)
  · intro label member
    let component : source.ConnectedComponent :=
      ⟨source.connectedComponentSet ⟨label, member⟩, ⟨⟨label, member⟩, rfl⟩⟩
    have component_member : label ∈ component.val := Matroid.connectedTo_self member
    have in_range : label ∈ Set.range (forest.construction component).labels := by
      rw [← (forest.construction component).interpret_ground, forest.interpret_eq]
      exact component_member
    obtain ⟨leaf, equality⟩ := in_range
    exact ⟨⟨component, leaf⟩, equality⟩

theorem labels_image_component (selected : Set forest.Leaf)
    (component : source.ConnectedComponent) :
    (forest.construction component).labels ''
      ((fun leaf : TreeLeaf (forest.tree component) =>
        (⟨component, leaf⟩ : forest.Leaf)) ⁻¹' selected) =
      forest.labels '' selected ∩ component.val := by
  ext label
  constructor
  · rintro ⟨leaf, member, rfl⟩
    exact ⟨⟨⟨component, leaf⟩, member, rfl⟩, forest.labels_mem ⟨component, leaf⟩⟩
  · rintro ⟨⟨leaf, member, rfl⟩, component_member⟩
    have same : leaf.1 = component := by
      by_contra distinct
      exact Set.disjoint_left.mp (source.componentMatroid_pairwise_disjoint distinct)
        (forest.labels_mem leaf) component_member
    rcases leaf with ⟨other, leaf⟩
    dsimp at same
    subst other
    exact ⟨leaf, member, rfl⟩

theorem matroid_indep_iff (selected : Set forest.Leaf) :
    forest.matroid.Indep selected ↔ source.Indep (forest.labels '' selected) := by
  rw [matroid, Matroid.sigma_indep_iff]
  have image_subset : forest.labels '' selected ⊆ source.E :=
    (Set.image_subset_range _ _).trans forest.labels_range.subset
  rw [show source.Indep (forest.labels '' selected) =
      (Matroid.disjointSigma source.componentMatroid
        source.componentMatroid_pairwise_disjoint).Indep (forest.labels '' selected) from
    congrArg (fun candidate : Matroid Label => candidate.Indep (forest.labels '' selected))
      source.eq_componentMatroid_disjointSigma]
  rw [Matroid.disjointSigma_indep_iff, source.componentMatroid_iUnion_ground,
    and_iff_left image_subset]
  apply forall_congr'
  intro component
  rw [← (forest.valid component).leafMatroid_eq_seriesParallelTreeMatroid,
    (forest.valid component).leafMatroid_indep_iff, forest.interpret_eq,
    forest.labels_image_component]
  rfl

noncomputable def leafEquiv : forest.Leaf ≃ source.E := by
  let labelMap : forest.Leaf → source.E := fun leaf =>
    ⟨forest.labels leaf, forest.labels_range ▸ Set.mem_range_self leaf⟩
  apply Equiv.ofBijective labelMap
  constructor
  · intro first second equality
    exact forest.labels_injective (congrArg Subtype.val equality)
  · intro label
    have member : label.val ∈ Set.range forest.labels := by
      rw [forest.labels_range]
      exact label.property
    obtain ⟨leaf, equality⟩ := member
    exact ⟨leaf, Subtype.ext equality⟩

noncomputable def iso : Matroid.Iso forest.matroid source := by
  let labelMap : forest.matroid.E → source.E := fun leaf => forest.leafEquiv leaf.val
  have injective : Function.Injective labelMap := by
    intro first second equality
    exact Subtype.ext (forest.leafEquiv.injective equality)
  have surjective : Function.Surjective labelMap := by
    intro label
    obtain ⟨leaf, equality⟩ := forest.leafEquiv.surjective label
    exact ⟨⟨leaf, forest.matroid_ground ▸ Set.mem_univ leaf⟩, equality⟩
  refine ⟨Equiv.ofBijective labelMap ⟨injective, surjective⟩, ?_⟩
  intro selected
  rw [forest.matroid_indep_iff]
  apply Iff.of_eq
  apply congrArg source.Indep
  ext label
  constructor
  · rintro ⟨leaf, ⟨original, member, rfl⟩, rfl⟩
    exact ⟨labelMap original, ⟨original, member, rfl⟩, rfl⟩
  · rintro ⟨label, ⟨leaf, member, rfl⟩, rfl⟩
    exact ⟨leaf.val, ⟨leaf, member, rfl⟩, rfl⟩

theorem tree_noDirectSum (component : source.ConnectedComponent) :
    TreeHasNoDirectSum (forest.tree component) :=
  (forest.construction component).no_directSum

instance leaf_finite [source.Finite] : Finite forest.Leaf := by
  let := source.ground_finite.to_subtype
  exact Finite.of_equiv source.E forest.leafEquiv.symm

instance matroid_finite [source.Finite] : forest.matroid.Finite := by
  constructor
  rw [forest.matroid_ground]
  exact Set.toFinite _

theorem leaf_card [source.Finite] : Nat.card forest.Leaf = source.E.ncard := by
  rw [Nat.card_congr forest.leafEquiv]
  rfl

noncomputable def totalLeaves [source.Finite] : ℕ := by
  letI := Fintype.ofFinite source.ConnectedComponent
  exact ∑ component : source.ConnectedComponent, (forest.tree component).numLeaves

theorem totalLeaves_eq [source.Finite] : forest.totalLeaves = source.E.ncard := by
  classical
  let := Fintype.ofFinite source.ConnectedComponent
  rw [← forest.leaf_card, Nat.card_sigma]
  change (∑ component : source.ConnectedComponent, (forest.tree component).numLeaves) =
    ∑ component : source.ConnectedComponent, Nat.card (TreeLeaf (forest.tree component))
  apply Finset.sum_congr rfl
  intro component member
  rw [Nat.card_eq_fintype_card, treeLeaf_card]

noncomputable def componentCount (_forest : ConnectedComponentForest source) : ℕ :=
  Nat.card source.ConnectedComponent

end ConnectedComponentForest

end BondalThomsen

namespace Matroid

variable {Label : Type*} {source : Matroid Label} [DecidableEq Label]

theorem exists_connectedComponentForest [source.Finite] [source.Loopless]
    (reducible : ∀ component : source.ConnectedComponent,
      2 ≤ (source.componentMatroid component).E.ncard →
      ∃ marked target length, target.E.ncard = 2 ∧
        MarkedConnectedReductionTrace marked (source.componentMatroid component) target length) :
    Nonempty (BondalThomsen.ConnectedComponentForest source) := by
  classical
  have component_trees : ∀ component : source.ConnectedComponent,
      ∃ (tree : BinaryTree BondalThomsen.TreeMark)
        (construction : BondalThomsen.LabelledMarkedExtensionTree Label tree),
        construction.Valid ∧ construction.interpret = source.componentMatroid component := by
    intro component
    let : (source.componentMatroid component).Loopless :=
      (source.restrict_isRestriction component.val (source.component_subset_ground component)).loopless
    exact connected_exists_extension_tree_of_marked_trace
      (source.componentMatroid_connected component) (reducible component)
  choose tree construction valid equality using component_trees
  exact ⟨⟨tree, construction, valid, equality⟩⟩

end Matroid
