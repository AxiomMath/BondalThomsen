module

public import BondalThomsen.Matroid.TreeShapeMatroidSemantics

@[expose] public section

namespace BondalThomsen

open Set

theorem exists_seriesParallel_sibling_pruning (tree : BinaryTree TreeMark)
    (no_sum : TreeHasNoDirectSum tree) (nonempty : tree ≠ .nil) :
    ∃ smaller : BinaryTree TreeMark, ∃ leaf : TreeLeaf smaller, ∃ mark : TreeMark,
      mark ≠ .directSum ∧ TreeHasNoDirectSum smaller ∧
        refineTreeLeaf smaller leaf mark = tree := by
  induction tree with
  | nil => exact (nonempty rfl).elim
  | node root left right left_prune right_prune =>
    by_cases left_empty : left = .nil
    · subst left
      by_cases right_empty : right = .nil
      · subst right
        exact ⟨.nil, (), root, no_sum.1, trivial, rfl⟩
      · obtain ⟨smaller, leaf, mark, mark_valid, smaller_valid, equality⟩ :=
          right_prune no_sum.2.2 right_empty
        exact ⟨.node root .nil smaller, .inr leaf, mark, mark_valid,
          ⟨no_sum.1, trivial, smaller_valid⟩, congrArg (BinaryTree.node root .nil) equality⟩
    · obtain ⟨smaller, leaf, mark, mark_valid, smaller_valid, equality⟩ :=
        left_prune no_sum.2.1 left_empty
      exact ⟨.node root smaller right, .inl leaf, mark, mark_valid,
        ⟨no_sum.1, smaller_valid, no_sum.2.2⟩,
        congrArg (fun branch => BinaryTree.node root branch right) equality⟩

theorem full_ground_surjective_comap_isBase_iff {Original New : Type*}
    (source : Matroid Original) (ground : source.E = Set.univ)
    (fold : New → Original) (surjective : Function.Surjective fold) (selected : Set New) :
    (source.comap fold).IsBase selected ↔
      source.IsBase (fold '' selected) ∧ Set.InjOn fold selected := by
  rw [Matroid.comap_isBase_iff, ground, Set.preimage_univ, Set.image_univ,
    surjective.range_eq, ← ground, Matroid.isBasis_ground_iff,
    and_iff_left (Set.subset_univ _)]

theorem full_ground_surjective_dual_comap_isBase_iff {Original New : Type*}
    (source : Matroid Original) (ground : source.E = Set.univ)
    (fold : New → Original) (surjective : Function.Surjective fold) (selected : Set New) :
    (source✶.comap fold)✶.IsBase selected ↔
      source.IsBase (fold '' selectedᶜ)ᶜ ∧ Set.InjOn fold selectedᶜ := by
  have next_ground : (source✶.comap fold).E = Set.univ := by
    rw [Matroid.comap_ground_eq, Matroid.dual_ground, ground, Set.preimage_univ]
  have selected_subset : selected ⊆ (source✶.comap fold).E := by
    rw [next_ground]
    exact Set.subset_univ _
  have image_subset : fold '' selectedᶜ ⊆ source.E := by
    rw [ground]
    exact Set.subset_univ _
  rw [Matroid.dual_isBase_iff selected_subset, next_ground, ← Set.compl_eq_univ_sdiff,
    full_ground_surjective_comap_isBase_iff source✶ (by rw [Matroid.dual_ground, ground])
      fold surjective, Matroid.dual_isBase_iff image_subset,
    ground, ← Set.compl_eq_univ_sdiff]

theorem exists_seriesParallel_shape_matroid (tree : BinaryTree TreeMark)
    (no_sum : TreeHasNoDirectSum tree) :
    ∃ source : Matroid (TreeLeaf tree), source.E = Set.univ ∧
      ∀ selected, source.IsBase selected ↔ TreeBasisState tree true selected := by
  generalize size_eq : tree.numNodes = size
  induction size using Nat.strong_induction_on generalizing tree with
  | h size induction =>
    by_cases empty : tree = .nil
    · subst tree
      exact ⟨Matroid.freeOn Set.univ, rfl, fun selected => Matroid.freeOn_isBase_iff⟩
    obtain ⟨smaller, leaf, mark, mark_valid, smaller_valid, equality⟩ :=
      exists_seriesParallel_sibling_pruning tree no_sum empty
    have smaller_size : smaller.numNodes < size := by
      have count := refineTreeLeaf_numNodes smaller leaf mark
      rw [equality, size_eq] at count
      omega
    obtain ⟨source, ground, bases⟩ := induction smaller.numNodes smaller_size smaller smaller_valid rfl
    subst tree
    cases mark with
    | directSum => exact (mark_valid rfl).elim
    | parallel =>
      refine ⟨source.comap (refinedLeafFold smaller leaf .parallel), ?_, ?_⟩
      · rw [Matroid.comap_ground_eq, ground, Set.preimage_univ]
      · intro selected
        rw [full_ground_surjective_comap_isBase_iff source ground _
          (refinedLeafFold_surjective smaller leaf .parallel), bases,
          treeBasisState_parallel_refinement]
    | series =>
      refine ⟨(source✶.comap (refinedLeafFold smaller leaf .series))✶, ?_, ?_⟩
      · rw [Matroid.dual_ground, Matroid.comap_ground_eq, Matroid.dual_ground,
          ground, Set.preimage_univ]
      · intro selected
        rw [full_ground_surjective_dual_comap_isBase_iff source ground _
          (refinedLeafFold_surjective smaller leaf .series), bases,
          treeBasisState_series_refinement]

noncomputable def seriesParallelTreeMatroid (tree : BinaryTree TreeMark)
    (no_sum : TreeHasNoDirectSum tree) : Matroid (TreeLeaf tree) :=
  Classical.choose (exists_seriesParallel_shape_matroid tree no_sum)

theorem seriesParallelTreeMatroid_ground (tree : BinaryTree TreeMark)
    (no_sum : TreeHasNoDirectSum tree) : (seriesParallelTreeMatroid tree no_sum).E = Set.univ :=
  (Classical.choose_spec (exists_seriesParallel_shape_matroid tree no_sum)).1

theorem seriesParallelTreeMatroid_isBase_iff (tree : BinaryTree TreeMark)
    (no_sum : TreeHasNoDirectSum tree) (selected : Set (TreeLeaf tree)) :
    (seriesParallelTreeMatroid tree no_sum).IsBase selected ↔ TreeBasisState tree true selected :=
  (Classical.choose_spec (exists_seriesParallel_shape_matroid tree no_sum)).2 selected

theorem seriesParallelTreeMatroid_unique (tree : BinaryTree TreeMark)
    (no_sum : TreeHasNoDirectSum tree) (source : Matroid (TreeLeaf tree))
    (ground : source.E = Set.univ)
    (bases : ∀ selected, source.IsBase selected ↔ TreeBasisState tree true selected) :
    source = seriesParallelTreeMatroid tree no_sum := by
  apply Matroid.ext_isBase
  · rw [ground, seriesParallelTreeMatroid_ground]
  · intro selected subset_ground
    rw [bases, seriesParallelTreeMatroid_isBase_iff]

namespace LabelledMarkedExtensionTree

theorem Valid.leafMatroid_eq_seriesParallelTreeMatroid {Label : Type*} [DecidableEq Label]
    {tree : BinaryTree TreeMark} {construction : LabelledMarkedExtensionTree Label tree}
    (valid : construction.Valid) (no_sum : TreeHasNoDirectSum tree) :
    construction.leafMatroid = seriesParallelTreeMatroid tree no_sum := by
  apply Matroid.ext_isBase
  · rw [construction.leafMatroid_ground, seriesParallelTreeMatroid_ground]
  · intro selected subset_ground
    rw [valid.leafMatroid_isBase_shape_iff, seriesParallelTreeMatroid_isBase_iff]

end LabelledMarkedExtensionTree

end BondalThomsen
