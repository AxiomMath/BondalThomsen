module

public import BondalThomsen.Matroid.Binary.MarkedRankFour
public import BondalThomsen.Ports.Matroid.ParallelExtension
public import BondalThomsen.Rarity.TreeEncoding

@[expose] public section

namespace BondalThomsen

open Set

def refinedTreeLeafLabels {Label : Type*} :
    (tree : BinaryTree TreeMark) → (leaf : TreeLeaf tree) → (mark : TreeMark) →
      (TreeLeaf tree → Label) → Label → TreeLeaf (refineTreeLeaf tree leaf mark) → Label
  | .nil, _, _, labels, _, .inl _ => labels ()
  | .nil, _, _, _, added, .inr _ => added
  | .node _ left _, .inl leaf, mark, labels, added, .inl refined =>
    refinedTreeLeafLabels left leaf mark (fun original => labels (.inl original)) added refined
  | .node _ _ _, .inl _, _, labels, _, .inr original => labels (.inr original)
  | .node _ _ _, .inr _, _, labels, _, .inl original => labels (.inl original)
  | .node _ _ right, .inr leaf, mark, labels, added, .inr refined =>
    refinedTreeLeafLabels right leaf mark (fun original => labels (.inr original)) added refined

theorem refinedTreeLeafLabels_range {Label : Type*}
    (tree : BinaryTree TreeMark) (leaf : TreeLeaf tree) (mark : TreeMark)
    (labels : TreeLeaf tree → Label) (added : Label) :
    Set.range (refinedTreeLeafLabels tree leaf mark labels added) = insert added (Set.range labels) := by
  induction tree with
  | nil =>
    ext element
    simp only [Set.mem_range, Set.mem_insert_iff]
    constructor
    · rintro ⟨original, rfl⟩
      cases original with
      | inl original => exact Or.inr ⟨(), rfl⟩
      | inr original => exact Or.inl rfl
    · rintro (rfl | ⟨original, rfl⟩)
      · exact ⟨.inr (), rfl⟩
      · exact ⟨.inl (), by cases original; rfl⟩
  | node root left right left_range right_range =>
    cases leaf with
    | inl leaf =>
      ext element
      have smaller := Set.ext_iff.mp (left_range leaf (fun original => labels (.inl original))) element
      simp only [Set.mem_range, Set.mem_insert_iff] at smaller ⊢
      constructor
      · rintro ⟨original, equality⟩
        cases original with
        | inl original =>
          rcases smaller.mp ⟨original, equality⟩ with equal | ⟨original, equal⟩
          · exact Or.inl equal
          · exact Or.inr ⟨.inl original, equal⟩
        | inr original => exact Or.inr ⟨.inr original, equality⟩
      · rintro (equal | ⟨original, equal⟩)
        · obtain ⟨refined, equality⟩ := smaller.mpr (Or.inl equal)
          exact ⟨.inl refined, equality⟩
        · cases original with
          | inl original =>
            obtain ⟨refined, equality⟩ := smaller.mpr (Or.inr ⟨original, equal⟩)
            exact ⟨.inl refined, equality⟩
          | inr original => exact ⟨.inr original, equal⟩
    | inr leaf =>
      ext element
      have smaller := Set.ext_iff.mp (right_range leaf (fun original => labels (.inr original))) element
      simp only [Set.mem_range, Set.mem_insert_iff] at smaller ⊢
      constructor
      · rintro ⟨original, equality⟩
        cases original with
        | inl original => exact Or.inr ⟨.inl original, equality⟩
        | inr original =>
          rcases smaller.mp ⟨original, equality⟩ with equal | ⟨original, equal⟩
          · exact Or.inl equal
          · exact Or.inr ⟨.inr original, equal⟩
      · rintro (equal | ⟨original, equal⟩)
        · obtain ⟨refined, equality⟩ := smaller.mpr (Or.inl equal)
          exact ⟨.inr refined, equality⟩
        · cases original with
          | inl original => exact ⟨.inl original, equal⟩
          | inr original =>
            obtain ⟨refined, equality⟩ := smaller.mpr (Or.inr ⟨original, equal⟩)
            exact ⟨.inr refined, equality⟩

theorem refinedTreeLeafLabels_fold {Label : Type*} [DecidableEq Label]
    (tree : BinaryTree TreeMark) (leaf : TreeLeaf tree) (mark : TreeMark)
    (labels : TreeLeaf tree → Label) (added : Label) (fresh : added ∉ Set.range labels) :
    Function.update id added (labels leaf) ∘ refinedTreeLeafLabels tree leaf mark labels added =
      labels ∘ refinedLeafFold tree leaf mark := by
  funext refined
  induction tree with
  | nil =>
    have leaf_eq : leaf = () := by cases leaf; rfl
    subst leaf
    cases refined with
    | inl original =>
      have distinct : labels () ≠ added := fun equal => fresh ⟨(), equal⟩
      change Function.update id added (labels ()) (labels ()) = labels ()
      exact Function.update_of_ne distinct (labels ()) id
    | inr original =>
      change Function.update id added (labels ()) added = labels ()
      simp
  | node root left right left_fold right_fold =>
    cases leaf with
    | inl leaf =>
      cases refined with
      | inl refined =>
        have fresh_left : added ∉ Set.range (fun original => labels (.inl original)) := by
          rintro ⟨original, equal⟩
          exact fresh ⟨.inl original, equal⟩
        exact left_fold leaf (fun original => labels (.inl original))
          fresh_left refined
      | inr original =>
        have distinct : labels (.inr original) ≠ added :=
          fun equal => fresh ⟨.inr original, equal⟩
        exact Function.update_of_ne distinct (labels (.inl leaf)) id
    | inr leaf =>
      cases refined with
      | inl original =>
        have distinct : labels (.inl original) ≠ added :=
          fun equal => fresh ⟨.inl original, equal⟩
        exact Function.update_of_ne distinct (labels (.inr leaf)) id
      | inr refined =>
        have fresh_right : added ∉ Set.range (fun original => labels (.inr original)) := by
          rintro ⟨original, equal⟩
          exact fresh ⟨.inr original, equal⟩
        exact right_fold leaf (fun original => labels (.inr original))
          fresh_right refined

inductive LabelledMarkedExtensionTree (Label : Type*) : BinaryTree TreeMark → Type _
  | singleton (label : Label) : LabelledMarkedExtensionTree Label .nil
  | parallel {tree : BinaryTree TreeMark} (previous : LabelledMarkedExtensionTree Label tree)
      (leaf : TreeLeaf tree) (added : Label) :
      LabelledMarkedExtensionTree Label (refineTreeLeaf tree leaf .parallel)
  | series {tree : BinaryTree TreeMark} (previous : LabelledMarkedExtensionTree Label tree)
      (leaf : TreeLeaf tree) (added : Label) :
      LabelledMarkedExtensionTree Label (refineTreeLeaf tree leaf .series)

namespace LabelledMarkedExtensionTree

variable {Label : Type*} {tree : BinaryTree TreeMark}

def labels : {tree : BinaryTree TreeMark} → LabelledMarkedExtensionTree Label tree →
    TreeLeaf tree → Label
  | _, .singleton label => fun _ => label
  | _, .parallel previous leaf added =>
    refinedTreeLeafLabels _ leaf .parallel previous.labels added
  | _, .series previous leaf added =>
    refinedTreeLeafLabels _ leaf .series previous.labels added

def interpret [DecidableEq Label] : {tree : BinaryTree TreeMark} →
    LabelledMarkedExtensionTree Label tree → Matroid Label
  | _, .singleton label => Matroid.freeOn {label}
  | _, .parallel previous leaf added =>
    previous.interpret.parallelExtend (previous.labels leaf) added
  | _, .series previous leaf added =>
    previous.interpret.seriesExtend (previous.labels leaf) added

def Valid [DecidableEq Label] : {tree : BinaryTree TreeMark} →
    LabelledMarkedExtensionTree Label tree → Prop
  | _, .singleton _ => True
  | _, .parallel previous leaf added => previous.Valid ∧ added ∉ previous.interpret.E ∧
      previous.interpret.IsNonloop (previous.labels leaf)
  | _, .series previous leaf added => previous.Valid ∧ added ∉ previous.interpret.E ∧
      previous.interpret✶.IsNonloop (previous.labels leaf)

theorem interpret_ground [DecidableEq Label] (construction : LabelledMarkedExtensionTree Label tree) :
    construction.interpret.E = Set.range construction.labels := by
  induction construction with
  | singleton label => ext element; simp [interpret, labels, TreeLeaf, eq_comm]
  | parallel previous leaf added ground =>
    simpa only [interpret, labels, Matroid.parallelExtend_ground, ground] using
      (refinedTreeLeafLabels_range _ leaf .parallel previous.labels added).symm
  | series previous leaf added ground =>
    simpa only [interpret, labels, Matroid.seriesExtend_ground, ground] using
      (refinedTreeLeafLabels_range _ leaf .series previous.labels added).symm

theorem interpret_finite [DecidableEq Label] (construction : LabelledMarkedExtensionTree Label tree) :
    construction.interpret.Finite := by
  constructor
  rw [construction.interpret_ground]
  exact Set.finite_range construction.labels

theorem Valid.ground_ncard [DecidableEq Label]
    {construction : LabelledMarkedExtensionTree Label tree} (valid : construction.Valid) :
    construction.interpret.E.ncard = tree.numLeaves := by
  induction construction with
  | singleton label => simp [interpret, BinaryTree.numLeaves]
  | parallel previous leaf added induction =>
    let := previous.interpret_finite
    rw [interpret, Matroid.parallelExtend_ground,
      Set.ncard_insert_of_notMem valid.2.1 previous.interpret.ground_finite,
      refineTreeLeaf_numLeaves, induction valid.1]
  | series previous leaf added induction =>
    let := previous.interpret_finite
    rw [interpret, Matroid.seriesExtend_ground,
      Set.ncard_insert_of_notMem valid.2.1 previous.interpret.ground_finite,
      refineTreeLeaf_numLeaves, induction valid.1]

theorem Valid.labels_injective [DecidableEq Label]
    {construction : LabelledMarkedExtensionTree Label tree} (valid : construction.Valid) :
    Function.Injective construction.labels := by
  have cardinality : (construction.labels '' Set.univ).ncard = (Set.univ : Set (TreeLeaf tree)).ncard := by
    rw [Set.image_univ, ← construction.interpret_ground, valid.ground_ncard]
    simp only [Set.ncard_univ, Nat.card_eq_fintype_card, treeLeaf_card]
  intro first second equality
  exact (Set.injOn_of_ncard_image_eq cardinality (Set.toFinite _))
    (Set.mem_univ first) (Set.mem_univ second) equality

theorem refine_no_directSum (shape : BinaryTree TreeMark) (leaf : TreeLeaf shape)
    (mark : TreeMark) (no_sum : TreeHasNoDirectSum shape) (not_sum : mark ≠ .directSum) :
    TreeHasNoDirectSum (refineTreeLeaf shape leaf mark) := by
  induction shape with
  | nil => exact ⟨not_sum, trivial, trivial⟩
  | node root left right left_induction right_induction =>
    cases leaf with
    | inl leaf => exact ⟨no_sum.1, left_induction leaf no_sum.2.1, no_sum.2.2⟩
    | inr leaf => exact ⟨no_sum.1, no_sum.2.1, right_induction leaf no_sum.2.2⟩

theorem no_directSum (construction : LabelledMarkedExtensionTree Label tree) : TreeHasNoDirectSum tree := by
  induction construction with
  | singleton label => trivial
  | parallel previous leaf added no_sum =>
    exact refine_no_directSum _ leaf .parallel no_sum (by decide)
  | series previous leaf added no_sum =>
    exact refine_no_directSum _ leaf .series no_sum (by decide)

def leafMatroid [DecidableEq Label] (construction : LabelledMarkedExtensionTree Label tree) :
    Matroid (TreeLeaf tree) := construction.interpret.comap construction.labels

theorem leafMatroid_ground [DecidableEq Label]
    (construction : LabelledMarkedExtensionTree Label tree) :
    construction.leafMatroid.E = Set.univ := by
  ext leaf
  simp only [leafMatroid, Matroid.comap_ground_eq, Set.mem_preimage,
    construction.interpret_ground, Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨leaf, rfl⟩

theorem Valid.leafMatroid_indep_iff [DecidableEq Label]
    {construction : LabelledMarkedExtensionTree Label tree} (valid : construction.Valid)
    (selected : Set (TreeLeaf tree)) :
    construction.leafMatroid.Indep selected ↔ construction.interpret.Indep
      (construction.labels '' selected) := by
  rw [leafMatroid, Matroid.comap_indep_iff,
    and_iff_left (valid.labels_injective.injOn.mono (Set.subset_univ selected))]

theorem Valid.leafMatroid_dual [DecidableEq Label]
    {construction : LabelledMarkedExtensionTree Label tree} (valid : construction.Valid) :
    construction.leafMatroid✶ = construction.interpret✶.comap construction.labels := by
  have preimage : construction.labels ⁻¹' construction.interpret.E = Set.univ :=
    construction.leafMatroid_ground
  have bijective : Set.BijOn construction.labels Set.univ construction.interpret.E := by
    refine ⟨?_, valid.labels_injective.injOn, ?_⟩
    · intro leaf member
      rw [construction.interpret_ground]
      exact ⟨leaf, rfl⟩
    · intro label member
      rw [construction.interpret_ground] at member
      obtain ⟨leaf, equal⟩ := member
      exact ⟨leaf, Set.mem_univ _, equal⟩
  have transport := Matroid.comapOn_dual_eq_of_bijOn bijective
  rw [← preimage, Matroid.comapOn_preimage_eq] at transport
  have dual_preimage : construction.labels ⁻¹' construction.interpret✶.E =
      construction.labels ⁻¹' construction.interpret.E := by rw [Matroid.dual_ground]
  rw [← dual_preimage, Matroid.comapOn_preimage_eq] at transport
  exact transport

theorem Valid.parallel_sibling_fold [DecidableEq Label]
    {previous : LabelledMarkedExtensionTree Label tree} {leaf : TreeLeaf tree} {added : Label}
    (valid : (LabelledMarkedExtensionTree.parallel previous leaf added).Valid) :
    TreeParallelExtension tree leaf .parallel previous.leafMatroid
      (LabelledMarkedExtensionTree.parallel previous leaf added).leafMatroid := by
  have next_injective := valid.labels_injective
  have previous_injective := valid.1.labels_injective
  have fresh : added ∉ Set.range previous.labels := by
    simpa only [← previous.interpret_ground] using valid.2.1
  have fold_eq := refinedTreeLeafLabels_fold tree leaf .parallel previous.labels added fresh
  intro selected
  rw [valid.leafMatroid_indep_iff, leafMatroid, Matroid.comap_indep_iff,
    and_iff_left previous_injective.injOn]
  change (previous.interpret.parallelExtend (previous.labels leaf) added).Indep
    (refinedTreeLeafLabels tree leaf .parallel previous.labels added '' selected) ↔ _
  rw [Matroid.parallelExtend_indep_iff]
  have image_eq : Function.update id added (previous.labels leaf) ''
      (refinedTreeLeafLabels tree leaf .parallel previous.labels added '' selected) =
      previous.labels '' (refinedLeafFold tree leaf .parallel '' selected) := by
    rw [← Set.image_comp, fold_eq, Set.image_comp]
  rw [image_eq]
  have subset_ground : refinedTreeLeafLabels tree leaf .parallel previous.labels added '' selected ⊆
      insert added previous.interpret.E := by
    rw [previous.interpret_ground, ← refinedTreeLeafLabels_range tree leaf .parallel previous.labels added]
    exact Set.image_subset_range _ _
  rw [and_iff_left subset_ground]
  have injectivity : Set.InjOn (Function.update id added (previous.labels leaf))
      (refinedTreeLeafLabels tree leaf .parallel previous.labels added '' selected) ↔
      Set.InjOn (refinedLeafFold tree leaf .parallel) selected := by
    constructor
    · intro injective first first_member second second_member equal
      apply next_injective
      apply injective ⟨first, first_member, rfl⟩ ⟨second, second_member, rfl⟩
      simpa only [Function.comp_apply] using
        (congrFun fold_eq first).trans
          ((congrArg previous.labels equal).trans (congrFun fold_eq second).symm)
    · intro injective first first_member second second_member equal
      obtain ⟨first_leaf, first_selected, rfl⟩ := first_member
      obtain ⟨second_leaf, second_selected, rfl⟩ := second_member
      have fold_equal : refinedLeafFold tree leaf .parallel first_leaf =
          refinedLeafFold tree leaf .parallel second_leaf := by
        apply previous_injective
        simpa only [Function.comp_apply] using
          (congrFun fold_eq first_leaf).symm.trans (equal.trans (congrFun fold_eq second_leaf))
      exact congrArg (refinedTreeLeafLabels tree leaf .parallel previous.labels added)
        (injective first_selected second_selected fold_equal)
  rw [injectivity, and_comm]

theorem Valid.series_sibling_fold [DecidableEq Label]
    {previous : LabelledMarkedExtensionTree Label tree} {leaf : TreeLeaf tree} {added : Label}
    (valid : (LabelledMarkedExtensionTree.series previous leaf added).Valid) :
    TreeParallelExtension tree leaf .series previous.leafMatroid✶
      (LabelledMarkedExtensionTree.series previous leaf added).leafMatroid✶ := by
  have next_injective := valid.labels_injective
  have previous_injective := valid.1.labels_injective
  have fresh : added ∉ Set.range previous.labels := by
    simpa only [← previous.interpret_ground] using valid.2.1
  have fold_eq := refinedTreeLeafLabels_fold tree leaf .series previous.labels added fresh
  intro selected
  rw [valid.leafMatroid_dual, valid.1.leafMatroid_dual, Matroid.comap_indep_iff,
    and_iff_left next_injective.injOn, Matroid.comap_indep_iff,
    and_iff_left previous_injective.injOn]
  change (previous.interpret.seriesExtend (previous.labels leaf) added)✶.Indep
    (refinedTreeLeafLabels tree leaf .series previous.labels added '' selected) ↔ _
  rw [Matroid.seriesExtend_dual, Matroid.parallelExtend_indep_iff]
  have image_eq : Function.update id added (previous.labels leaf) ''
      (refinedTreeLeafLabels tree leaf .series previous.labels added '' selected) =
      previous.labels '' (refinedLeafFold tree leaf .series '' selected) := by
    rw [← Set.image_comp, fold_eq, Set.image_comp]
  rw [image_eq]
  have subset_ground : refinedTreeLeafLabels tree leaf .series previous.labels added '' selected ⊆
      insert added previous.interpret✶.E := by
    rw [Matroid.dual_ground, previous.interpret_ground,
      ← refinedTreeLeafLabels_range tree leaf .series previous.labels added]
    exact Set.image_subset_range _ _
  rw [and_iff_left subset_ground]
  have injectivity : Set.InjOn (Function.update id added (previous.labels leaf))
      (refinedTreeLeafLabels tree leaf .series previous.labels added '' selected) ↔
      Set.InjOn (refinedLeafFold tree leaf .series) selected := by
    constructor
    · intro injective first first_member second second_member equal
      apply next_injective
      apply injective ⟨first, first_member, rfl⟩ ⟨second, second_member, rfl⟩
      simpa only [Function.comp_apply] using
        (congrFun fold_eq first).trans
          ((congrArg previous.labels equal).trans (congrFun fold_eq second).symm)
    · intro injective first first_member second second_member equal
      obtain ⟨first_leaf, first_selected, rfl⟩ := first_member
      obtain ⟨second_leaf, second_selected, rfl⟩ := second_member
      have fold_equal : refinedLeafFold tree leaf .series first_leaf =
          refinedLeafFold tree leaf .series second_leaf := by
        apply previous_injective
        simpa only [Function.comp_apply] using
          (congrFun fold_eq first_leaf).symm.trans (equal.trans (congrFun fold_eq second_leaf))
      exact congrArg (refinedTreeLeafLabels tree leaf .series previous.labels added)
        (injective first_selected second_selected fold_equal)
  rw [injectivity, and_comm]

end LabelledMarkedExtensionTree

end BondalThomsen

namespace Matroid

open Set BondalThomsen

variable {Label : Type*} [DecidableEq Label] {source target : Matroid Label} {marked : Label}

theorem Connected.two_element_extension_tree [source.Finite]
    (connected : source.Connected) (size : source.E.ncard = 2) (marked_member : marked ∈ source.E) :
    ∃ tree : BinaryTree TreeMark, ∃ construction : LabelledMarkedExtensionTree Label tree,
      construction.Valid ∧ construction.interpret = source ∧
      tree.numLeaves = 2 ∧ ∃ leaf : TreeLeaf tree, construction.labels leaf = marked := by
  obtain ⟨first, second, distinct, ground⟩ := ncard_eq_two.mp size
  have other : ∃ partner, partner ≠ marked ∧ source.E = {marked, partner} := by
    rw [ground] at marked_member
    rcases marked_member with equal | equal
    · subst first
      exact ⟨second, distinct.symm, ground⟩
    · have second_equal : marked = second := by simpa using equal
      subst second
      exact ⟨first, distinct, by rw [ground, pair_comm]⟩
  obtain ⟨partner, distinct, ground⟩ := other
  have parallel := (connected.two_element_parallel_and_series ground distinct.symm).1
  have deleted_ground : (source.delete {partner}).E = {marked} := by
    rw [delete_ground, ground]
    ext element
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨equal | equal, absent⟩
      · exact equal
      · exact (absent equal).elim
    · rintro rfl
      exact ⟨Or.inl rfl, distinct.symm⟩
  have deleted_nonloop : (source.delete {partner}).IsNonloop marked :=
    delete_isNonloop_iff.mpr ⟨parallel.1, by simpa using distinct.symm⟩
  have deleted_free : source.delete {partner} = freeOn {marked} :=
    eq_freeOn_iff.mpr ⟨deleted_ground, deleted_nonloop.indep⟩
  let singleton : LabelledMarkedExtensionTree Label .nil := .singleton marked
  let construction : LabelledMarkedExtensionTree Label (.node .parallel .nil .nil) :=
    .parallel singleton () partner
  have equality : construction.interpret = source := by
    change (freeOn {marked}).parallelExtend marked partner = source
    rw [← deleted_free]
    exact (parallel.eq_parallelExtend_delete distinct.symm).symm
  refine ⟨_, construction, ?_, equality, rfl, .inl (), rfl⟩
  change True ∧ partner ∉ (freeOn {marked}).E ∧ (freeOn {marked}).IsNonloop marked
  exact ⟨trivial, by simpa using distinct,
    indep_singleton.mp (freeOn_indep (by rfl))⟩

theorem MarkedConnectedReductionTrace.exists_labelled_extension_tree [source.Finite]
    {length : ℕ} (trace : MarkedConnectedReductionTrace marked source target length)
    (target_size : target.E.ncard = 2) :
    ∃ tree : BinaryTree TreeMark, ∃ construction : LabelledMarkedExtensionTree Label tree,
      construction.Valid ∧ construction.interpret = source ∧
      tree.numLeaves = source.E.ncard ∧ tree.numNodes = length + 1 ∧
      ∃ leaf : TreeLeaf tree, construction.labels leaf = marked := by
  have finite_source : source.Finite := inferInstance
  revert finite_source
  induction trace with
  | nil candidate connected nonloop not_coloop =>
    intro finite_candidate
    let : candidate.Finite := finite_candidate
    obtain ⟨tree, construction, valid, equality, leaves, marked_leaf⟩ :=
      connected.two_element_extension_tree target_size nonloop.mem_ground
    refine ⟨tree, construction, valid, equality, leaves.trans target_size.symm, ?_, marked_leaf⟩
    have count := BinaryTree.numLeaves_eq_numNodes_succ tree
    omega
  | @cons candidate intermediate target length connected nonloop not_coloop reduction remaining induction =>
    intro finite_candidate
    let : candidate.Finite := finite_candidate
    let : Finite candidate.E := candidate.ground_finite.to_subtype
    let : intermediate.Finite := ⟨candidate.ground_finite.subset reduction.isMinor.subset⟩
    obtain ⟨tree, construction, valid, equality, leaves, nodes, marked_leaf⟩ :=
      induction target_size inferInstance
    have cardinality := reduction.ground_ncard
    have lower : 2 ≤ candidate.E.ncard := by
      have remaining_card := remaining.ground_ncard
      omega
    have nontrivial : candidate.E.Nontrivial := one_lt_ncard_iff_nontrivial.mp (by omega)
    have reconstruct {existing added : Label} (mark : TreeMark)
        (added_absent : added ∉ intermediate.E) (existing_member : existing ∈ intermediate.E)
        (extension_eq : candidate = if mark = .parallel then
          intermediate.parallelExtend existing added else intermediate.seriesExtend existing added)
        (valid_existing : if mark = .parallel then intermediate.IsNonloop existing
          else intermediate✶.IsNonloop existing) (mark_choice : mark = .parallel ∨ mark = .series) :
        ∃ tree : BinaryTree TreeMark, ∃ construction : LabelledMarkedExtensionTree Label tree,
          construction.Valid ∧ construction.interpret = candidate ∧
          tree.numLeaves = candidate.E.ncard ∧ tree.numNodes = (length + 1) + 1 ∧
          ∃ leaf : TreeLeaf tree, construction.labels leaf = marked := by
      have member : existing ∈ Set.range construction.labels := by
        rw [← construction.interpret_ground, equality]
        exact existing_member
      obtain ⟨leaf, label_eq⟩ := member
      have finish (next : LabelledMarkedExtensionTree Label (refineTreeLeaf tree leaf mark))
          (next_valid : next.Valid) (next_eq : next.interpret = candidate) :
          ∃ tree : BinaryTree TreeMark, ∃ construction : LabelledMarkedExtensionTree Label tree,
            construction.Valid ∧ construction.interpret = candidate ∧
            tree.numLeaves = candidate.E.ncard ∧ tree.numNodes = (length + 1) + 1 ∧
            ∃ leaf : TreeLeaf tree, construction.labels leaf = marked := by
        refine ⟨_, next, next_valid, next_eq, ?_, ?_, ?_⟩
        · rw [refineTreeLeaf_numLeaves, leaves, cardinality]
        · rw [refineTreeLeaf_numNodes, nodes]
        · have member : marked ∈ Set.range next.labels := by
            rw [← next.interpret_ground, next_eq]
            exact nonloop.mem_ground
          exact member
      rcases mark_choice with rfl | rfl
      · simp only [ite_true] at extension_eq valid_existing
        apply finish (.parallel construction leaf added)
        · change construction.Valid ∧ added ∉ construction.interpret.E ∧
            construction.interpret.IsNonloop (construction.labels leaf)
          exact ⟨valid, equality ▸ added_absent, by simpa only [equality, label_eq] using valid_existing⟩
        · change construction.interpret.parallelExtend (construction.labels leaf) added = candidate
          rw [equality, label_eq]
          exact extension_eq.symm
      · simp only [reduceCtorEq, ite_false] at extension_eq valid_existing
        apply finish (.series construction leaf added)
        · change construction.Valid ∧ added ∉ construction.interpret.E ∧
            construction.interpret✶.IsNonloop (construction.labels leaf)
          exact ⟨valid, equality ▸ added_absent, by simpa only [equality, label_eq] using valid_existing⟩
        · change construction.interpret.seriesExtend (construction.labels leaf) added = candidate
          rw [equality, label_eq]
          exact extension_eq.symm
    cases reduction with
    | loop element loop => exact ((connected.isNonloop nontrivial loop.mem_ground).not_isLoop loop).elim
    | coloop element coloop => exact (connected.not_isColoop nontrivial coloop.mem_ground coloop).elim
    | parallel first second distinct parallel =>
      apply reconstruct (existing := second) (added := first) .parallel
      · simp
      · exact ⟨parallel.2.1.mem_ground, by simpa using distinct.symm⟩
      · simpa using parallel.symm.eq_parallelExtend_delete distinct.symm
      · simpa using delete_isNonloop_iff.mpr
          ⟨parallel.2.1, show second ∉ ({first} : Set Label) by simpa using distinct.symm⟩
      · exact Or.inl rfl
    | series first second distinct series =>
      apply reconstruct (existing := second) (added := first) .series
      · simp
      · exact ⟨by simpa using series.2.1.mem_ground, by simpa using distinct.symm⟩
      · simpa using series_pair_eq_seriesExtend_contract series.symm distinct.symm
      · simpa only [reduceCtorEq, ite_false, dual_contract] using delete_isNonloop_iff.mpr
          ⟨series.2.1, show second ∉ ({first} : Set Label) by simpa using distinct.symm⟩
      · exact Or.inr rfl

end Matroid
