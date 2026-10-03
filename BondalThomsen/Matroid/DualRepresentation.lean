module

public import BondalThomsen.Ports.MatroidDual.ColumnBasisDuality
public import BondalThomsen.Ports.Matroid.StandardRepresentation

@[expose] public section

open Set Submodule Matrix Module Function

namespace Matroid

variable {Label Index OtherIndex Field Vector : Type*} [_root_.Field Field]
    [AddCommGroup Vector] [Module Field Vector] {matroid : Matroid Label}

noncomputable def Rep.ofSubtypeFun (vectors : matroid.E → Vector)
    [DecidablePred (· ∈ matroid.E)]
    (independence : ∀ selected : Set matroid.E,
      matroid.Indep (Subtype.val '' selected) ↔ LinearIndepOn Field vectors selected) :
    matroid.Rep Field Vector :=
  Rep.ofGround
    (fun label => if member : label ∈ matroid.E then vectors ⟨label, member⟩ else 0)
    (by aesop)
    (by
      intro selected contained
      rw [← Subtype.range_val (s := matroid.E), subset_range_iff_exists_image_eq] at contained
      obtain ⟨selected, rfl⟩ := contained
      rw [independence]
      apply linearIndependent_equiv' (Equiv.Set.image _ _ Subtype.val_injective)
      ext label
      simp only [Function.comp_apply, Equiv.Set.image_apply,
        dite_eq_left label.val.property])

noncomputable def Rep.restrictSubtype (representation : matroid.Rep Field Vector)
    (selected : Set Label) : (matroid.restrictSubtype selected).Rep Field Vector where
  to_fun label := representation label
  indep_iff' independentSet := by
    rw [restrictSubtype_indep_iff, representation.indep_iff]
    symm
    apply linearIndependent_equiv' (Equiv.Set.image _ _ Subtype.val_injective)
    rfl

abbrev Rep.toMatrix (representation : matroid.Rep Field (Index → Field)) :
    Matrix Index Label Field := fun index label => representation label index

theorem Rep.colBasis_eq_isBase (representation : matroid.Rep Field (Index → Field)) :
    representation.toMatrix.ColBasis = matroid.IsBase := by
  have dependencies : LinearIndepOn Field representation.toMatrix.col = matroid.Indep := by
    funext selected
    exact propext representation.indep_iff.symm
  funext selected
  apply propext
  rw [colBasis_iff_maximal_linearIndependent, isBase_iff_maximal_indep, dependencies]

theorem eq_dual_of_rowSpace_eq_nullSpace_on_univ [Fintype Label]
    {first second : Matroid Label} (first_ground : first.E = univ)
    (second_ground : second.E = univ)
    (first_representation : first.Rep Field (Index → Field))
    (second_representation : second.Rep Field (OtherIndex → Field))
    (orthogonal : first_representation.toMatrix.rowSpace =
      second_representation.toMatrix.nullSpace) : second = first✶ := by
  apply ext_isBase (by rw [second_ground, dual_ground, first_ground])
  intro selected contained
  rw [← second_representation.colBasis_eq_isBase, dual_isBase_iff,
    ← first_representation.colBasis_eq_isBase, first_ground, ← compl_eq_univ_sdiff,
    colBasis_iff_colBasis_compl_of_orth orthogonal, compl_compl]

theorem Representable.dual [matroid.Finite] (representable : matroid.Representable Field) :
    matroid✶.Representable Field := by
  classical
  obtain ⟨representation⟩ := representable
  let : Fintype matroid.E := matroid.ground_finite.fintype
  let matrix := representation.toMatrix.colSubmatrix matroid.E
  let space := matrix.nullSpace
  let basis := Basis.ofVectorSpace Field space
  let vectors := basis.toRowMatrix.col
  let dualMatroid := BondalThomsen.rayMatroid (Field := Field) vectors
  let dualRepresentation := repOfRays (Field := Field) vectors
  have row_space : basis.toRowMatrix.rowSpace = matrix.nullSpace := basis.toRowMatrix_rowSpace
  have orthogonal : matrix.rowSpace = basis.toRowMatrix.nullSpace := by
    rw [nullSpace, row_space, orthSpace_nullSpace_eq_rowSpace]
  have actual_dual : dualMatroid = (matroid.restrictSubtype matroid.E)✶ := by
    apply eq_dual_of_rowSpace_eq_nullSpace_on_univ (by simp) (by simp)
      (representation.restrictSubtype matroid.E) dualRepresentation
    exact orthogonal
  let dualVectors : matroid✶.E → (Basis.ofVectorSpaceIndex Field space → Field) := vectors
  have independence : ∀ selected : Set matroid✶.E,
      matroid✶.Indep (Subtype.val '' selected) ↔
        LinearIndepOn Field dualVectors selected := by
    intro selected
    have subtype_dual : dualMatroid = matroid✶.restrictSubtype matroid.E :=
      actual_dual.trans (restrictSubtype_dual (M := matroid))
    have subtype_independence :
        (matroid✶.restrictSubtype matroid.E).Indep (selected : Set matroid.E) ↔
          LinearIndepOn Field vectors (selected : Set matroid.E) := by
      rw [← subtype_dual]
      exact BondalThomsen.rayMatroid_indep_iff vectors selected
    exact (restrictSubtype_indep_iff (M := matroid✶) (X := matroid.E)).symm.trans
      subtype_independence
  exact (Rep.ofSubtypeFun dualVectors independence).representable

end Matroid
