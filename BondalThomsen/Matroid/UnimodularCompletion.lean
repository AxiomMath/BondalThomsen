module

public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

@[expose] public section

namespace BondalThomsen

open Matrix

theorem determinant_instance_irrel {Index : Type*}
    (first_finite second_finite : Fintype Index) (first_decidable second_decidable : DecidableEq Index)
    (matrix : Matrix Index Index ℤ) :
    @Matrix.det Index first_decidable first_finite ℤ _ matrix =
      @Matrix.det Index second_decidable second_finite ℤ _ matrix := by
  cases Subsingleton.elim first_finite second_finite
  cases Subsingleton.elim first_decidable second_decidable
  rfl

theorem totallyUnimodular_of_full_minors {Row Column : Type*} [Fintype Row] [DecidableEq Row]
    (matrix : Matrix Row Column ℤ) (identity_columns : Row → Column)
    (identity : ∀ row column, matrix row (identity_columns column) = if row = column then 1 else 0)
    (full_minors : ∀ columns : Row → Column,
      (matrix.submatrix id columns).det ∈ Set.range SignType.cast) :
    matrix.IsTotallyUnimodular := by
  classical
  intro size rows columns rows_injective _columns_injective
  let selected := Equiv.ofInjective rows rows_injective
  let completed_columns := fun row =>
    if member : row ∈ Set.range rows then columns (selected.symm ⟨row, member⟩)
    else identity_columns row
  let completed := matrix.submatrix id completed_columns
  have selected_column : ∀ index, completed_columns (rows index) = columns index := by
    intro index
    simp [completed_columns, selected, Equiv.ofInjective_symm_apply]
  have omitted_column : ∀ row, row ∉ Set.range rows → completed_columns row = identity_columns row := by
    intro row omitted
    dsimp only [completed_columns]
    rw [dite_eq_right omitted]
  have zero_block : ∀ row, row ∈ Set.range rows → ∀ column, column ∉ Set.range rows →
      completed row column = 0 := by
    intro row member column omitted
    have distinct : row ≠ column := by
      intro equality
      exact omitted (equality ▸ member)
    simp [completed, Matrix.submatrix, omitted_column column omitted, identity, distinct]
  have complement_identity : completed.toSquareBlockProp (fun row => row ∉ Set.range rows) = 1 := by
    ext row column
    simp only [toSquareBlockProp_def, Matrix.of_apply, completed, submatrix_apply,
      omitted_column column.val column.property, identity]
    simp [Matrix.one_apply, Subtype.ext_iff]
  have selected_block :
      (completed.toSquareBlockProp (fun row => row ∈ Set.range rows)).submatrix selected selected =
        matrix.submatrix rows columns := by
    ext row column
    simp [toSquareBlockProp_def, completed, Matrix.submatrix, selected, selected_column]
  have selected_determinant :
      (completed.toSquareBlockProp (fun row => row ∈ Set.range rows)).det =
        (matrix.submatrix rows columns).det := by
    rw [← selected_block, Matrix.det_submatrix_equiv_self]
  have factorization := Matrix.twoBlockTriangular_det' completed (fun row => row ∈ Set.range rows)
    zero_block
  have factorization' : completed.det = (matrix.submatrix rows columns).det := by
    rw [factorization, complement_identity, det_one, mul_one]
    convert selected_determinant using 1
    exact determinant_instance_irrel _ _ _ _ _
  rw [← factorization']
  exact full_minors completed_columns

end BondalThomsen
