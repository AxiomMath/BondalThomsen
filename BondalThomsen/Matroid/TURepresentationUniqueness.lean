module

public import BondalThomsen.Matroid.K4RepresentationUniqueness

@[expose] public section

namespace BondalThomsen

open Matrix

theorem totallyUnimodular_entry_square {Row Column : Type*}
    {matrix : Matrix Row Column ℤ} (unimodular : matrix.IsTotallyUnimodular)
    {row : Row} {column : Column} (nonzero : matrix row column ≠ 0) :
    matrix row column * matrix row column = 1 := by
  rcases Int.isUnit_iff.mp (signedInteger_isUnit _ (unimodular.apply row column) nonzero) with
    equality | equality <;> simp [equality]

theorem unit_sum_eq_zero_of_signed {first second : ℤ} (first_unit : IsUnit first)
    (second_unit : IsUnit second) (signed : first + second ∈ Set.range SignType.cast) :
    first + second = 0 := by
  have bounds := signedInteger_bounds _ signed
  rcases Int.isUnit_iff.mp first_unit with positive | negative <;>
    rcases Int.isUnit_iff.mp second_unit with other_positive | other_negative <;> omega

def tuRelativeSign {Row Column : Type*} (first second : Matrix Row Column ℤ)
    (row : Row) (column : Column) : ℤ := second row column * first row column

theorem tuRelativeSign_isUnit {Row Column : Type*} {first second : Matrix Row Column ℤ}
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (support : ∀ row column, first row column = 0 ↔ second row column = 0)
    {row : Row} {column : Column} (nonzero : first row column ≠ 0) :
    IsUnit (tuRelativeSign first second row column) :=
  (signedInteger_isUnit _ (second_tu.apply _ _)
    (fun zero => nonzero ((support row column).mpr zero))).mul
    (signedInteger_isUnit _ (first_tu.apply _ _) nonzero)

theorem tuRelativeSign_recover {Row Column : Type*} {first second : Matrix Row Column ℤ}
    (first_tu : first.IsTotallyUnimodular)
    (support : ∀ row column, first row column = 0 ↔ second row column = 0)
    (row : Row) (column : Column) :
    first row column * tuRelativeSign first second row column = second row column := by
  by_cases zero : first row column = 0
  · simp [tuRelativeSign, zero, (support row column).mp zero]
  · have square := totallyUnimodular_entry_square first_tu zero
    unfold tuRelativeSign
    calc
      _ = (first row column * first row column) * second row column := by ring
      _ = _ := by rw [square, one_mul]

theorem integral_row_operation_of_signs {Row Column : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Column] [DecidableEq Column]
    (first second : Matrix Row Column ℤ) (row_sign : Row → ℤ) (column_sign : Column → ℤ)
    (rows_signed : ∀ row, row_sign row = 1 ∨ row_sign row = -1)
    (entry_equality : ∀ row column,
      second row column = row_sign row * first row column * column_sign column) :
    ∃ operation : (Matrix Row Row ℤ)ˣ,
      second = (operation : Matrix Row Row ℤ) * first * Matrix.diagonal column_sign := by
  have square : Matrix.diagonal row_sign * Matrix.diagonal row_sign = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext row column
    by_cases same : row = column
    · subst column
      rcases rows_signed row with equality | equality <;> simp [equality]
    · simp [same]
  refine ⟨⟨Matrix.diagonal row_sign, Matrix.diagonal row_sign, square, square⟩, ?_⟩
  ext row column
  change second row column =
    (Matrix.diagonal row_sign * first * Matrix.diagonal column_sign) row column
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact entry_equality row column

theorem normalized_integer_matroid_support {Row Column : Type*}
    [Fintype Row] [DecidableEq Row] (first second : Matrix Row Column ℤ)
    (basis_columns : Row → Column)
    (first_identity : first.submatrix id basis_columns = 1)
    (second_identity : second.submatrix id basis_columns = 1)
    (matching : rayMatroid (Field := ℚ) (fun column row => (first row column : ℚ)) =
      rayMatroid (Field := ℚ) (fun column row => (second row column : ℚ))) :
    ∀ row column, first row column = 0 ↔ second row column = 0 := by
  have rational_identity (matrix : Matrix Row Column ℤ)
      (identity : matrix.submatrix id basis_columns = 1) :
      (matrix.map (Int.castRingHom ℚ)).submatrix id basis_columns = 1 := by
    ext row column
    have entry := congrFun (congrFun identity row) column
    change (matrix row (basis_columns column) : ℚ) = _
    rw [show matrix row (basis_columns column) =
      (1 : Matrix Row Row ℤ) row column from entry]
    simp [Matrix.one_apply]
  intro row column
  have support := normalizedRepresentations_support_eq
    (first.map (Int.castRingHom ℚ)) (second.map (Int.castRingHom ℚ)) basis_columns
    (rational_identity first first_identity) (rational_identity second second_identity)
    matching row column
  change (first row column : ℚ) = 0 ↔ (second row column : ℚ) = 0 at support
  simpa only [Int.cast_eq_zero] using support

end BondalThomsen
