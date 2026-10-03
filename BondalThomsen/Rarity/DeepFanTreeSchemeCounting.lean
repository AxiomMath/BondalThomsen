module

public import BondalThomsen.DeepFan.ForestReconstruction
public import BondalThomsen.DeepFan.SchemeTernaryFiniteness
public import BondalThomsen.Rarity.DeepFanSchemeCountingRigidity
public import BondalThomsen.Toric.Scheme.FanEquivSchemeIso
public import BondalThomsen.Rarity.Counting
public import Mathlib.CategoryTheory.Skeletal
public import BondalThomsen.Matroid.ColumnPermutationRigidity
public import BondalThomsen.Rarity.TreeEncoding
public import BondalThomsen.Rarity.AsymptoticRarity
public import BondalThomsen.Rarity.FamilyParameters
public import Mathlib.Data.Set.Card.Arithmetic
public import BondalThomsen.Matroid.ComponentReduction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set
open scoped Classical

namespace BondalThomsen

namespace MatroidIso

variable {Label OtherLabel : Type*} {source : Matroid Label} {target : Matroid OtherLabel}

noncomputable def univLabelEquiv (isomorphism : Matroid.Iso source target)
    (source_ground : source.E = Set.univ) (target_ground : target.E = Set.univ) :
    Label ≃ OtherLabel where
  toFun label := (isomorphism.toEquiv ⟨label, source_ground ▸ Set.mem_univ _⟩).val
  invFun label := (isomorphism.toEquiv.symm ⟨label, target_ground ▸ Set.mem_univ _⟩).val
  left_inv label := congrArg Subtype.val (isomorphism.toEquiv.symm_apply_apply
    ⟨label, source_ground ▸ Set.mem_univ _⟩)
  right_inv label := congrArg Subtype.val (isomorphism.toEquiv.apply_symm_apply
    ⟨label, target_ground ▸ Set.mem_univ _⟩)

theorem univLabelEquiv_indep (isomorphism : Matroid.Iso source target)
    (source_ground : source.E = Set.univ) (target_ground : target.E = Set.univ)
    (selected : Set Label) : source.Indep selected ↔
      target.Indep (univLabelEquiv isomorphism source_ground target_ground '' selected) := by
  have subset_ground : selected ⊆ source.E := source_ground ▸ Set.subset_univ _
  rw [isomorphism.indep_setImage_iff subset_ground]
  apply Iff.of_eq
  apply congrArg target.Indep
  ext label
  constructor
  · rintro ⟨original, ⟨ground_leaf, member, rfl⟩, rfl⟩
    exact ⟨ground_leaf.val, member, rfl⟩
  · rintro ⟨original, member, rfl⟩
    exact ⟨isomorphism.toEquiv ⟨original, subset_ground member⟩,
      ⟨⟨original, subset_ground member⟩, member, rfl⟩, rfl⟩

end MatroidIso

theorem rayMatroid_reindex_indep {Label OtherLabel Field Vector : Type*}
    [_root_.DivisionRing Field] [AddCommGroup Vector] [Module Field Vector]
    (vectors : OtherLabel → Vector) (labels : Label ≃ OtherLabel) (selected : Set Label) :
    (rayMatroid (Field := Field) (fun label => vectors (labels label))).Indep selected ↔
      (rayMatroid (Field := Field) vectors).Indep (labels '' selected) := by
  simp only [rayMatroid_indep_iff]
  constructor
  · exact fun independent => independent.image_of_comp labels vectors
  · exact fun independent => independent.comp_of_image labels.injective.injOn

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem labelledRayMatrix_rational_rank (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    {Label : Type*} [Fintype Label] (labels : Label ≃ fan.Ray) :
    ((basis.toMatrix (fun label => (labels label).val)).map (Int.castRingHom ℚ)).rank = dimension := by
  classical
  let matrix := (basis.toMatrix (fun label => (labels label).val)).map (Int.castRingHom ℚ)
  let basis_labels := fun index => labels.symm (fan.basisRay basis cone_basis index)
  have identity_minor : matrix.submatrix id basis_labels = (1 : Matrix (Fin dimension) (Fin dimension) ℚ) := by
    ext row column
    simp [matrix, basis_labels, Basis.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  apply le_antisymm
  · simpa only [Fintype.card_fin] using matrix.rank_le_card_height
  · have bound := matrix.rank_submatrix_le id basis_labels
    rw [identity_minor, Matrix.rank_one, Fintype.card_fin] at bound
    exact bound

theorem labelledRayMatroid_eq_tree (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (tree : BinaryTree BondalThomsen.TreeMark)
    (valid : BondalThomsen.ComponentTreeShape tree)
    (isomorphism : Matroid.Iso (BondalThomsen.componentTreeMatroid tree valid) fan.rayMatroid) :
    BondalThomsen.rayMatroid (Field := ℚ) (fun leaf row =>
      (basis.repr (BondalThomsen.MatroidIso.univLabelEquiv isomorphism
        (BondalThomsen.componentTreeMatroid_ground tree valid) (BondalThomsen.rayMatroid_ground _) leaf).val row : ℚ)) =
      BondalThomsen.componentTreeMatroid tree valid := by
  let labels := BondalThomsen.MatroidIso.univLabelEquiv isomorphism
    (BondalThomsen.componentTreeMatroid_ground tree valid) (BondalThomsen.rayMatroid_ground _)
  apply Matroid.ext_indep (by simp [BondalThomsen.componentTreeMatroid_ground])
  intro selected subset_ground
  rw [BondalThomsen.rayMatroid_reindex_indep (fun ray : fan.Ray =>
    fun row => (basis.repr ray.val row : ℚ)) labels selected]
  rw [← fan.rayMatroid_eq_coordinates basis]
  exact (BondalThomsen.MatroidIso.univLabelEquiv_indep isomorphism
    (BondalThomsen.componentTreeMatroid_ground tree valid) (BondalThomsen.rayMatroid_ground _) selected).symm

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem deep_rayMatroid_single_tree_of_triangle_triad_minor_lemma
    (fan : Fan embedding) (minor_lemma : Matroid.BinaryConnectedTriangleTriadK4MinorLemma fan.Ray)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (positive_dimension : 0 < dimension) :
    ∃ tree : BinaryTree BondalThomsen.TreeMark, ∃ valid : BondalThomsen.ComponentTreeShape tree,
      Nonempty (Matroid.Iso (BondalThomsen.componentTreeMatroid tree valid) fan.rayMatroid) ∧
        tree.numLeaves = Nat.card fan.Ray ∧ tree.numLeaves ≤ 4 * dimension := by
  classical
  let := fan.rayMatroid_loopless_of_basis reference
  obtain ⟨forest⟩ := Matroid.binary_exists_canonical_source_forest_of_triangle_triad_minor_lemma
    minor_lemma (fan.deep_minor_representable complete regular deep reference Matroid.IsMinor.refl)
    (fan.deep_minor_no_graph_k4 complete regular deep reference Matroid.IsMinor.refl)
  obtain ⟨tree, valid, isomorphism, leaves⟩ := forest.exists_single_tree_iso
    (fan.rayMatroid_ground_nonempty_of_positive_dimension complete regular reference positive_dimension)
  have leaf_count : tree.numLeaves = Nat.card fan.Ray := by
    simpa only [rayMatroid, BondalThomsen.rayMatroid_ground, Set.ncard_univ] using leaves
  have bound := fan.deep_ray_count_le_four_dimension_sub_two_of_elementary_reducibility
    (Matroid.binary_k4_excluded_elementary_reducibility_of_triangle_triad_minor_lemma minor_lemma)
    complete regular deep reference positive_dimension
  exact ⟨tree, valid, isomorphism, leaf_count, by rw [leaf_count]; omega⟩

end TauCeti.Toric.Fan

