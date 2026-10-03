module

public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Tactic
public import BondalThomsen.Matroid.UnimodularCompletion
public import BondalThomsen.Matroid.UnimodularRepresentations
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

namespace BondalThomsen

open Matrix

variable {Row Column : Type*} [Fintype Row] [DecidableEq Row]

noncomputable def basisNormalization (matrix : Matrix Row Column ℤ)
    (basis_columns : Row → Column) : Matrix Row Column ℤ :=
  (matrix.submatrix id basis_columns)⁻¹ * matrix

theorem totallyUnimodular_basis_det_isUnit (matrix : Matrix Row Column ℤ)
    (unimodular : matrix.IsTotallyUnimodular) (basis_columns : Row → Column)
    (nonzero : (matrix.submatrix id basis_columns).det ≠ 0) :
    IsUnit (matrix.submatrix id basis_columns).det := by
  obtain ⟨sign, equality⟩ :=
    (Matrix.isTotallyUnimodular_iff_fintype matrix).mp unimodular Row id basis_columns
  rw [← equality] at nonzero ⊢
  apply Int.isUnit_iff.mpr
  cases sign <;> simp_all [SignType.cast]

theorem basisNormalization_basis_block (matrix : Matrix Row Column ℤ)
    (basis_columns : Row → Column)
    (basis_unit : IsUnit (matrix.submatrix id basis_columns).det) :
    (basisNormalization matrix basis_columns).submatrix id basis_columns = 1 := by
  rw [basisNormalization, Matrix.submatrix_mul _ _ id id basis_columns Function.bijective_id,
    Matrix.submatrix_id_id]
  exact Matrix.nonsing_inv_mul _ basis_unit

theorem basisNormalization_undo (matrix : Matrix Row Column ℤ)
    (basis_columns : Row → Column)
    (basis_unit : IsUnit (matrix.submatrix id basis_columns).det) :
    matrix.submatrix id basis_columns * basisNormalization matrix basis_columns = matrix :=
  Matrix.mul_nonsing_inv_cancel_left _ _ basis_unit

theorem basisNormalization_totallyUnimodular (matrix : Matrix Row Column ℤ)
    (unimodular : matrix.IsTotallyUnimodular) (basis_columns : Row → Column)
    (basis_unit : IsUnit (matrix.submatrix id basis_columns).det) :
    (basisNormalization matrix basis_columns).IsTotallyUnimodular := by
  apply totallyUnimodular_of_full_minors _ basis_columns
  · intro row column
    exact congrFun (congrFun (basisNormalization_basis_block matrix basis_columns basis_unit)
      row) column
  · intro columns
    have factorization : ((basisNormalization matrix basis_columns).submatrix id columns).det =
        (matrix.submatrix id basis_columns)⁻¹.det * (matrix.submatrix id columns).det := by
      rw [basisNormalization,
        Matrix.submatrix_mul _ _ id id columns Function.bijective_id,
        Matrix.submatrix_id_id, Matrix.det_mul]
    have inverse_unit : IsUnit (matrix.submatrix id basis_columns)⁻¹.det :=
      Matrix.isUnit_det_of_left_inverse (Matrix.mul_nonsing_inv _ basis_unit)
    obtain ⟨sign, equality⟩ :=
      (Matrix.isTotallyUnimodular_iff_fintype matrix).mp unimodular Row id columns
    rcases Int.isUnit_iff.mp inverse_unit with positive | negative
    · exact ⟨sign, by simp [factorization, positive, ← equality]⟩
    · exact ⟨-sign, by simp [factorization, negative, ← equality]⟩

theorem integral_equivalence_of_basisNormalization_signs
    [Fintype Column] [DecidableEq Column]
    (first second : Matrix Row Column ℤ) (basis_columns : Row → Column)
    (first_unit : IsUnit (first.submatrix id basis_columns).det)
    (second_unit : IsUnit (second.submatrix id basis_columns).det)
    (normalized_row_operation : (Matrix Row Row ℤ)ˣ) (column_sign : Column → ℤ)
    (normalized_equality : basisNormalization second basis_columns =
      (normalized_row_operation : Matrix Row Row ℤ) *
        basisNormalization first basis_columns * Matrix.diagonal column_sign) :
    ∃ row_operation : (Matrix Row Row ℤ)ˣ,
      second = (row_operation : Matrix Row Row ℤ) * first * Matrix.diagonal column_sign := by
  let first_block : (Matrix Row Row ℤ)ˣ :=
    ⟨first.submatrix id basis_columns, (first.submatrix id basis_columns)⁻¹,
      Matrix.mul_nonsing_inv _ first_unit, Matrix.nonsing_inv_mul _ first_unit⟩
  let second_block : (Matrix Row Row ℤ)ˣ :=
    ⟨second.submatrix id basis_columns, (second.submatrix id basis_columns)⁻¹,
      Matrix.mul_nonsing_inv _ second_unit, Matrix.nonsing_inv_mul _ second_unit⟩
  refine ⟨second_block * normalized_row_operation * first_block⁻¹, ?_⟩
  calc
    second = second.submatrix id basis_columns * basisNormalization second basis_columns :=
      (basisNormalization_undo second basis_columns second_unit).symm
    _ = second.submatrix id basis_columns *
        ((normalized_row_operation : Matrix Row Row ℤ) *
          basisNormalization first basis_columns * Matrix.diagonal column_sign) := by
      rw [normalized_equality]
    _ = _ := by simp [basisNormalization, first_block, second_block, Matrix.mul_assoc]

theorem basisNormalization_rayMatroid (matrix : Matrix Row Column ℤ)
    (basis_columns : Row → Column)
    (basis_unit : IsUnit (matrix.submatrix id basis_columns).det) :
    rayMatroid (Field := ℚ)
      (fun column row => (basisNormalization matrix basis_columns row column : ℚ)) =
      rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ)) := by
  let inverse : Matrix Row Row ℚ :=
    ((matrix.submatrix id basis_columns)⁻¹).map (Int.castRingHom ℚ)
  have inverse_integer_unit : IsUnit (matrix.submatrix id basis_columns)⁻¹.det :=
    Matrix.isUnit_det_of_left_inverse (Matrix.mul_nonsing_inv _ basis_unit)
  have inverse_unit : IsUnit inverse.det := by
    have determinant_cast :
        ((matrix.submatrix id basis_columns)⁻¹.det : ℚ) = inverse.det :=
      (Int.castRingHom ℚ).map_det _
    rw [← determinant_cast]
    exact inverse_integer_unit.map (Int.castRingHom ℚ)
  let change := Matrix.toLinearEquiv (Pi.basisFun ℚ Row) inverse inverse_unit
  have change_columns : (fun column => change (fun row => (matrix row column : ℚ))) =
      (fun column row => (basisNormalization matrix basis_columns row column : ℚ)) := by
    funext column row
    simp only [change, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, basisNormalization, Matrix.mul_apply,
      Int.cast_sum, Int.cast_mul, inverse, Matrix.map_apply]
    rfl
  rw [← change_columns]
  exact rayMatroid_map_linearEquiv _ change

theorem totallyUnimodular_exists_common_basis
    [Fintype Column]
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (first_full_rank : (first.map (Int.castRingHom ℚ)).rank = Fintype.card Row)
    (matroid_equality :
      rayMatroid (Field := ℚ) (fun column row => (first row column : ℚ)) =
        rayMatroid (Field := ℚ) (fun column row => (second row column : ℚ))) :
    ∃ basis_columns : Row → Column,
      IsUnit (first.submatrix id basis_columns).det ∧
        IsUnit (second.submatrix id basis_columns).det := by
  classical
  let rational : Matrix Row Column ℚ := first.map (Int.castRingHom ℚ)
  obtain ⟨selected, selected_rank⟩ :=
    Matrix.exists_submatrix_id_rank_eq rational (size := Fintype.card Row) first_full_rank.ge
  let basis_columns : Row → Column := selected ∘ Fintype.equivFin Row
  have block_rank : (rational.submatrix id basis_columns).rank = Fintype.card Row := by
    have reindex := Matrix.rank_submatrix (rational.submatrix id selected)
      (Equiv.refl Row) (Fintype.equivFin Row)
    simpa only [Matrix.submatrix_submatrix, Equiv.coe_refl, Function.comp_id,
      basis_columns] using reindex.trans selected_rank
  have rational_nonzero :=
    (Matrix.rank_eq_card_iff_det_ne_zero (rational.submatrix id basis_columns)).mp block_rank
  have first_independent : LinearIndependent ℚ
      (fun index row => (first row (basis_columns index) : ℚ)) :=
    Matrix.linearIndependent_cols_of_det_ne_zero rational_nonzero
  have basis_injective : Function.Injective basis_columns := by
    intro index other equality
    apply first_independent.injective
    funext row
    change (first row (basis_columns index) : ℚ) = (first row (basis_columns other) : ℚ)
    rw [equality]
  have first_range_independent : LinearIndepOn ℚ
      (fun column row => (first row column : ℚ)) (Set.range basis_columns) :=
    (linearIndepOn_range_iff basis_injective _).mpr first_independent
  have second_range_independent : LinearIndepOn ℚ
      (fun column row => (second row column : ℚ)) (Set.range basis_columns) := by
    rw [← rayMatroid_indep_iff, ← matroid_equality, rayMatroid_indep_iff]
    exact first_range_independent
  have second_independent : LinearIndependent ℚ
      ((second.map (Int.castRingHom ℚ)).submatrix id basis_columns).col :=
    (linearIndepOn_range_iff basis_injective _).mp second_range_independent
  have second_rational_nonzero :
      ((second.map (Int.castRingHom ℚ)).submatrix id basis_columns).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp second_independent)).ne_zero
  have first_integer_nonzero : (first.submatrix id basis_columns).det ≠ 0 := by
    intro zero
    have determinant_cast : ((first.submatrix id basis_columns).det : ℚ) =
        (rational.submatrix id basis_columns).det := (Int.castRingHom ℚ).map_det _
    apply rational_nonzero
    rw [← determinant_cast, zero, Int.cast_zero]
  have second_integer_nonzero : (second.submatrix id basis_columns).det ≠ 0 := by
    intro zero
    have determinant_cast : ((second.submatrix id basis_columns).det : ℚ) =
        ((second.map (Int.castRingHom ℚ)).submatrix id basis_columns).det :=
      (Int.castRingHom ℚ).map_det _
    apply second_rational_nonzero
    rw [← determinant_cast, zero, Int.cast_zero]
  exact ⟨basis_columns,
    totallyUnimodular_basis_det_isUnit first first_tu basis_columns first_integer_nonzero,
    totallyUnimodular_basis_det_isUnit second second_tu basis_columns second_integer_nonzero⟩

end BondalThomsen
