module

public import BondalThomsen.Matroid.Binary.TriangleFrameConnector
public import BondalThomsen.Matroid.ComponentReduction
public import BondalThomsen.Matroid.ElementaryMatroidReconstruction
public import BondalThomsen.Rarity.DeepFanTreeSchemeCounting

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Set
open scoped Classical

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem deep_rayMatroid_single_tree (fan : Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (positive_dimension : 0 < dimension) :
    ∃ tree : BinaryTree BondalThomsen.TreeMark, ∃ valid : BondalThomsen.ComponentTreeShape tree,
      Nonempty (Matroid.Iso (BondalThomsen.componentTreeMatroid tree valid) fan.rayMatroid) ∧
        tree.numLeaves = Nat.card fan.Ray ∧ tree.numLeaves ≤ 4 * dimension :=
  fan.deep_rayMatroid_single_tree_of_triangle_triad_minor_lemma
    Matroid.binaryConnectedTriangleTriadK4MinorLemma_proved complete regular deep reference positive_dimension

end TauCeti.Toric.Fan

