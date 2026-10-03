module

public import BondalThomsen.Matroid.TreeShapeMatroidInterpretation

@[expose] public section

namespace BondalThomsen

open Set

def ComponentTreeShape : BinaryTree TreeMark → Prop
  | .nil => True
  | .node .directSum left right => ComponentTreeShape left ∧ ComponentTreeShape right
  | .node .parallel left right => TreeHasNoDirectSum left ∧ TreeHasNoDirectSum right
  | .node .series left right => TreeHasNoDirectSum left ∧ TreeHasNoDirectSum right

theorem noDirectSum_componentTreeShape (tree : BinaryTree TreeMark)
    (no_sum : TreeHasNoDirectSum tree) : ComponentTreeShape tree := by
  cases tree with
  | nil => trivial
  | node root left right =>
    cases root with
    | directSum => exact (no_sum.1 rfl).elim
    | parallel => exact no_sum.2
    | series => exact no_sum.2

noncomputable def componentTreeMatroid :
    (tree : BinaryTree TreeMark) → ComponentTreeShape tree → Matroid (TreeLeaf tree)
  | .nil, _ => Matroid.freeOn Set.univ
  | .node .directSum left right, valid =>
    (componentTreeMatroid left valid.1).sum (componentTreeMatroid right valid.2)
  | .node .parallel left right, valid =>
    seriesParallelTreeMatroid (.node .parallel left right) ⟨by decide, valid⟩
  | .node .series left right, valid =>
    seriesParallelTreeMatroid (.node .series left right) ⟨by decide, valid⟩

theorem componentTreeMatroid_ground (tree : BinaryTree TreeMark)
    (valid : ComponentTreeShape tree) : (componentTreeMatroid tree valid).E = Set.univ := by
  induction tree with
  | nil => rfl
  | node root left right left_ground right_ground =>
    cases root with
    | series => exact seriesParallelTreeMatroid_ground _ _
    | parallel => exact seriesParallelTreeMatroid_ground _ _
    | directSum =>
      change ((componentTreeMatroid left valid.1).sum (componentTreeMatroid right valid.2)).E = _
      rw [Matroid.sum_ground, left_ground valid.1, right_ground valid.2]
      change Sum.inl '' (Set.univ : Set (TreeLeaf left)) ∪
        Sum.inr '' (Set.univ : Set (TreeLeaf right)) =
          (Set.univ : Set (TreeLeaf left ⊕ TreeLeaf right))
      ext original
      cases original <;> simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem componentTreeMatroid_isBase_iff (tree : BinaryTree TreeMark)
    (valid : ComponentTreeShape tree) (selected : Set (TreeLeaf tree)) :
    (componentTreeMatroid tree valid).IsBase selected ↔ TreeBasisState tree true selected := by
  induction tree with
  | nil => exact Matroid.freeOn_isBase_iff
  | node root left right left_bases right_bases =>
    cases root with
    | parallel => exact seriesParallelTreeMatroid_isBase_iff _ _ _
    | series => exact seriesParallelTreeMatroid_isBase_iff _ _ _
    | directSum =>
      change ((componentTreeMatroid left valid.1).sum (componentTreeMatroid right valid.2)).IsBase
        selected ↔ _
      rw [Matroid.sum_isBase_iff, left_bases valid.1, right_bases valid.2]
      rfl

theorem componentTreeMatroid_eq_seriesParallel (tree : BinaryTree TreeMark)
    (no_sum : TreeHasNoDirectSum tree) :
    componentTreeMatroid tree (noDirectSum_componentTreeShape tree no_sum) =
      seriesParallelTreeMatroid tree no_sum := by
  apply seriesParallelTreeMatroid_unique
  · exact componentTreeMatroid_ground _ _
  · exact componentTreeMatroid_isBase_iff _ _

end BondalThomsen
