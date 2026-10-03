module

public import BondalThomsen.Rarity.Counting
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Combinatorics.Matroid.Sum

@[expose] public section

namespace BondalThomsen

inductive TreeMark
  | series
  | parallel
  | directSum
  deriving DecidableEq, Repr

instance treeMarkFintype : Fintype TreeMark :=
  ⟨{.series, .parallel, .directSum}, by intro mark; cases mark <;> simp⟩

@[simp] theorem treeMark_card : Fintype.card TreeMark = 3 := by decide

def TreeDecoration : BinaryTree Unit → Type
  | .nil => Unit
  | .node _ left right => TreeMark × TreeDecoration left × TreeDecoration right

noncomputable instance treeDecorationFintype :
    (shape : BinaryTree Unit) → Fintype (TreeDecoration shape)
  | .nil => inferInstanceAs (Fintype Unit)
  | .node _ left right =>
    letI := treeDecorationFintype left
    letI := treeDecorationFintype right
    inferInstanceAs (Fintype (TreeMark × TreeDecoration left × TreeDecoration right))

theorem treeDecoration_card (shape : BinaryTree Unit) :
    Fintype.card (TreeDecoration shape) = 3 ^ shape.numNodes := by
  induction shape with
  | nil => exact @Fintype.card_unique Unit _ _
  | node value left right left_count right_count =>
    change Fintype.card (TreeMark × TreeDecoration left × TreeDecoration right) = _
    simp only [Fintype.card_prod, treeMark_card, left_count, right_count,
      BinaryTree.numNodes, pow_add, pow_succ]
    ring

def treeShape (tree : BinaryTree TreeMark) : BinaryTree Unit := tree.map (fun _ => ())

def decorateTree : (shape : BinaryTree Unit) → TreeDecoration shape → BinaryTree TreeMark
  | .nil, _ => .nil
  | .node _ left right, decoration =>
    .node decoration.1 (decorateTree left decoration.2.1)
      (decorateTree right decoration.2.2)

@[simp] theorem treeShape_decorateTree (shape : BinaryTree Unit)
    (decoration : TreeDecoration shape) :
    treeShape (decorateTree shape decoration) = shape := by
  induction shape with
  | nil => rfl
  | node value left right left_eq right_eq =>
    cases value
    change BinaryTree.node () (treeShape (decorateTree left decoration.2.1))
      (treeShape (decorateTree right decoration.2.2)) = BinaryTree.node () left right
    rw [left_eq, right_eq]

@[simp] theorem decorateTree_numNodes (shape : BinaryTree Unit)
    (decoration : TreeDecoration shape) :
    (decorateTree shape decoration).numNodes = shape.numNodes := by
  induction shape with
  | nil => rfl
  | node value left right left_eq right_eq =>
    simp [decorateTree, left_eq decoration.2.1, right_eq decoration.2.2]

@[simp] theorem treeShape_numNodes (tree : BinaryTree TreeMark) :
    (treeShape tree).numNodes = tree.numNodes := by
  induction tree with
  | nil => rfl
  | node mark left right left_eq right_eq =>
    change (treeShape left).numNodes + (treeShape right).numNodes + 1 = _
    rw [left_eq, right_eq]
    rfl

theorem decorateTree_injective (shape : BinaryTree Unit) :
    Function.Injective (decorateTree shape) := by
  induction shape with
  | nil => intro first second _; exact @Subsingleton.elim Unit _ first second
  | node value left right left_injective right_injective =>
    rintro ⟨first_mark, first_left, first_right⟩
      ⟨second_mark, second_left, second_right⟩ equality
    have parts := BinaryTree.node.inj equality
    exact Prod.ext parts.1
      (Prod.ext (left_injective parts.2.1) (right_injective parts.2.2))

theorem exists_treeDecoration (tree : BinaryTree TreeMark) :
    ∃ decoration : TreeDecoration (treeShape tree),
      decorateTree (treeShape tree) decoration = tree := by
  induction tree with
  | nil => exact ⟨(), rfl⟩
  | node mark left right left_exists right_exists =>
    obtain ⟨left_decoration, left_eq⟩ := left_exists
    obtain ⟨right_decoration, right_eq⟩ := right_exists
    refine ⟨⟨mark, left_decoration, right_decoration⟩, ?_⟩
    change BinaryTree.node mark (decorateTree (treeShape left) left_decoration)
      (decorateTree (treeShape right) right_decoration) = _
    rw [left_eq, right_eq]

abbrev MarkedTree (internal : ℕ) :=
  { tree : BinaryTree TreeMark // tree.numNodes = internal }

abbrev DecoratedShape (internal : ℕ) :=
  Σ shape : ↥(BinaryTree.treesOfNumNodesEq internal), TreeDecoration shape.val

noncomputable def decoratedShapeEquiv (internal : ℕ) :
    DecoratedShape internal ≃ MarkedTree internal := by
  let mapping : DecoratedShape internal → MarkedTree internal := fun decorated =>
    ⟨decorateTree decorated.1.val decorated.2,
      (decorateTree_numNodes _ _).trans
        (BinaryTree.mem_treesOfNumNodesEq.mp decorated.1.property)⟩
  apply Equiv.ofBijective mapping
  constructor
  · rintro ⟨first_shape, first_decoration⟩ ⟨second_shape, second_decoration⟩ equality
    have shape_eq : first_shape = second_shape := by
      apply Subtype.ext
      simpa only [mapping, treeShape_decorateTree] using
        congrArg (fun tree : MarkedTree internal => treeShape tree.val) equality
    cases shape_eq
    have decoration_eq : first_decoration = second_decoration :=
      decorateTree_injective first_shape.val (congrArg Subtype.val equality)
    cases decoration_eq
    rfl
  · rintro ⟨tree, size_eq⟩
    obtain ⟨decoration, decoration_eq⟩ := exists_treeDecoration tree
    refine ⟨⟨⟨treeShape tree, BinaryTree.mem_treesOfNumNodesEq.mpr ?_⟩, decoration⟩, ?_⟩
    · exact (treeShape_numNodes tree).trans size_eq
    · exact Subtype.ext decoration_eq

noncomputable instance markedTreeFintype (internal : ℕ) : Fintype (MarkedTree internal) :=
  Fintype.ofEquiv (DecoratedShape internal) (decoratedShapeEquiv internal)

theorem markedTree_card (internal : ℕ) :
    Fintype.card (MarkedTree internal) = markedTreeCount internal := by
  rw [← Fintype.card_congr (decoratedShapeEquiv internal), Fintype.card_sigma]
  simp only [treeDecoration_card]
  have sizes : ∀ shape : ↥(BinaryTree.treesOfNumNodesEq internal),
      shape.val.numNodes = internal := fun shape =>
    BinaryTree.mem_treesOfNumNodesEq.mp shape.property
  simp only [sizes, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_coe, BinaryTree.treesOfNumNodesEq_card_eq_catalan]
  exact Nat.mul_comm _ _

abbrev MarkedLeafTree (elements : ℕ) :=
  { tree : BinaryTree TreeMark // tree.numLeaves = elements }

def markedLeafTreeToMarkedTree (elements : ℕ) :
    MarkedLeafTree elements → MarkedTree (elements - 1) := fun tree =>
  ⟨tree.val, by have := BinaryTree.numLeaves_eq_numNodes_succ tree.val; omega⟩

noncomputable instance markedLeafTreeFintype (elements : ℕ) :
    Fintype (MarkedLeafTree elements) :=
  Fintype.ofInjective (markedLeafTreeToMarkedTree elements)
    (fun _ _ equality => Subtype.ext
      (congrArg (fun tree : MarkedTree (elements - 1) => tree.val) equality))

def markedLeafTreeEquiv (elements : ℕ) (positive : 0 < elements) :
    MarkedLeafTree elements ≃ MarkedTree (elements - 1) where
  toFun := markedLeafTreeToMarkedTree elements
  invFun tree := ⟨tree.val, by
    have := BinaryTree.numLeaves_eq_numNodes_succ tree.val
    have := tree.property
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedLeafTree_card (elements : ℕ) (positive : 0 < elements) :
    Fintype.card (MarkedLeafTree elements) = markedTreeCount (elements - 1) := by
  rw [Fintype.card_congr (markedLeafTreeEquiv elements positive), markedTree_card]

theorem markedLeafTree_card_zero : Fintype.card (MarkedLeafTree 0) = 0 := by
  let : IsEmpty (MarkedLeafTree 0) :=
    ⟨fun tree => by have := BinaryTree.numLeaves_pos tree.val; have := tree.property; omega⟩
  exact Fintype.card_eq_zero

def TreeLeaf {Label : Type*} : BinaryTree Label → Type
  | .nil => Unit
  | .node _ left right => TreeLeaf left ⊕ TreeLeaf right

noncomputable instance treeLeafFintype {Label : Type*} :
    (tree : BinaryTree Label) → Fintype (TreeLeaf tree)
  | .nil => inferInstanceAs (Fintype Unit)
  | .node _ left right =>
    letI := treeLeafFintype left
    letI := treeLeafFintype right
    inferInstanceAs (Fintype (TreeLeaf left ⊕ TreeLeaf right))

@[simp] theorem treeLeaf_card {Label : Type*} (tree : BinaryTree Label) :
    Fintype.card (TreeLeaf tree) = tree.numLeaves := by
  induction tree with
  | nil => exact @Fintype.card_unique Unit _ _
  | node label left right left_count right_count =>
    change Fintype.card (TreeLeaf left ⊕ TreeLeaf right) = _
    simp [left_count, right_count]

abbrev SignedMarkedTree (elements : ℕ) :=
  Σ tree : MarkedLeafTree elements, TreeLeaf tree.val → Bool

noncomputable instance signedMarkedTreeFintype (elements : ℕ) :
    Fintype (SignedMarkedTree elements) := by
  classical
  exact inferInstanceAs
    (Fintype (Σ tree : MarkedLeafTree elements, TreeLeaf tree.val → Bool))

theorem signedMarkedTree_card_mul (elements : ℕ) :
    Fintype.card (SignedMarkedTree elements) =
      2 ^ elements * Fintype.card (MarkedLeafTree elements) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, treeLeaf_card]
  have sizes : ∀ tree : MarkedLeafTree elements, tree.val.numLeaves = elements :=
    fun tree => tree.property
  simp only [sizes, Finset.sum_const, smul_eq_mul, Finset.card_univ]
  exact Nat.mul_comm _ _

theorem signedMarkedTree_card (elements : ℕ) (positive : 0 < elements) :
    Fintype.card (SignedMarkedTree elements) = signedTreeCount elements := by
  rw [signedMarkedTree_card_mul, markedLeafTree_card elements positive]
  rfl

theorem signedMarkedTree_card_le (elements : ℕ) :
    Fintype.card (SignedMarkedTree elements) ≤ signedTreeCount elements := by
  by_cases positive : 0 < elements
  · exact (signedMarkedTree_card elements positive).le
  · have elements_eq : elements = 0 := by omega
    subst elements
    rw [signedMarkedTree_card_mul, markedLeafTree_card_zero, Nat.mul_zero]
    exact Nat.zero_le _

def refineTreeLeaf : (tree : BinaryTree TreeMark) → TreeLeaf tree →
    TreeMark → BinaryTree TreeMark
  | .nil, _, mark => .node mark .nil .nil
  | .node root left right, .inl leaf, mark =>
    .node root (refineTreeLeaf left leaf mark) right
  | .node root left right, .inr leaf, mark =>
    .node root left (refineTreeLeaf right leaf mark)

theorem refineTreeLeaf_numNodes (tree : BinaryTree TreeMark) (leaf : TreeLeaf tree)
    (mark : TreeMark) :
    (refineTreeLeaf tree leaf mark).numNodes = tree.numNodes + 1 := by
  induction tree with
  | nil => rfl
  | node root left right left_count right_count =>
    cases leaf with
    | inl leaf => simp [refineTreeLeaf, left_count leaf]; omega
    | inr leaf => simp [refineTreeLeaf, right_count leaf]; omega

theorem refineTreeLeaf_numLeaves (tree : BinaryTree TreeMark) (leaf : TreeLeaf tree)
    (mark : TreeMark) :
    (refineTreeLeaf tree leaf mark).numLeaves = tree.numLeaves + 1 := by
  rw [BinaryTree.numLeaves_eq_numNodes_succ, refineTreeLeaf_numNodes,
    BinaryTree.numLeaves_eq_numNodes_succ]

def refinedLeafFold : (tree : BinaryTree TreeMark) → (leaf : TreeLeaf tree) →
    (mark : TreeMark) → TreeLeaf (refineTreeLeaf tree leaf mark) → TreeLeaf tree
  | .nil, _, _, _ => ()
  | .node _ left _, .inl leaf, mark, .inl refined =>
    .inl (refinedLeafFold left leaf mark refined)
  | .node _ _ _, .inl _, _, .inr original => .inr original
  | .node _ _ _, .inr _, _, .inl original => .inl original
  | .node _ _ right, .inr leaf, mark, .inr refined =>
    .inr (refinedLeafFold right leaf mark refined)

theorem refinedLeafFold_surjective (tree : BinaryTree TreeMark) (leaf : TreeLeaf tree)
    (mark : TreeMark) : Function.Surjective (refinedLeafFold tree leaf mark) := by
  induction tree with
  | nil => intro original; exact ⟨.inl (), by cases original; rfl⟩
  | node root left right left_surjective right_surjective =>
    cases leaf with
    | inl leaf =>
      intro original
      cases original with
      | inl original =>
        obtain ⟨refined, equality⟩ := left_surjective leaf original
        exact ⟨.inl refined, congrArg Sum.inl equality⟩
      | inr original => exact ⟨.inr original, rfl⟩
    | inr leaf =>
      intro original
      cases original with
      | inl original => exact ⟨.inl original, rfl⟩
      | inr original =>
        obtain ⟨refined, equality⟩ := right_surjective leaf original
        exact ⟨.inr refined, congrArg Sum.inr equality⟩

def TreeHasNoDirectSum : BinaryTree TreeMark → Prop
  | .nil => True
  | .node mark left right =>
    mark ≠ .directSum ∧ TreeHasNoDirectSum left ∧ TreeHasNoDirectSum right

def TreeParallelExtension (tree : BinaryTree TreeMark) (leaf : TreeLeaf tree)
    (mark : TreeMark) (original : Matroid (TreeLeaf tree))
    (extended : Matroid (TreeLeaf (refineTreeLeaf tree leaf mark))) : Prop :=
  ∀ selected, extended.Indep selected ↔
    Set.InjOn (refinedLeafFold tree leaf mark) selected ∧
      original.Indep (refinedLeafFold tree leaf mark '' selected)

structure TreeMatroidRecursion where
  interpret : (tree : BinaryTree TreeMark) → Matroid (TreeLeaf tree)
  ground : ∀ tree, (interpret tree).E = Set.univ
  singleton : ∀ selected, (interpret .nil).Indep selected
  directSum : ∀ left right,
    interpret (.node .directSum left right) = (interpret left).sum (interpret right)
  parallel : ∀ tree leaf,
    TreeParallelExtension tree leaf .parallel (interpret tree)
      (interpret (refineTreeLeaf tree leaf .parallel))
  series : ∀ tree leaf,
    TreeParallelExtension tree leaf .series (interpret tree).dual
      (interpret (refineTreeLeaf tree leaf .series)).dual

end BondalThomsen
