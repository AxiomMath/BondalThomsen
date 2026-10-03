module

public import BondalThomsen.Matroid.RootMatroid
public import BondalThomsen.Fan.FanoObstruction
public import BondalThomsen.Matroid.UnimodularEquivalence

@[expose] public section

namespace BondalThomsen

open Matrix Set

theorem normalized_k4_representation_signs (matrix : Matrix (Fin 3) (Fin 6) ℤ)
    (unimodular : matrix.IsTotallyUnimodular)
    (identity : matrix.submatrix id k4BasisEdges = 1)
    (matching : rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ)) =
      k4Matroid) :
    ∃ row_sign : Fin 3 → ℤ, ∃ column_sign : Fin 6 → ℤ,
      (∀ row, row_sign row = 1 ∨ row_sign row = -1) ∧
      (∀ column, column_sign column = 1 ∨ column_sign column = -1) ∧
      matrix = Matrix.diagonal row_sign * k4RootMatrix ℤ * Matrix.diagonal column_sign := by
  have rational_identity : (matrix.map (Int.castRingHom ℚ)).submatrix id k4BasisEdges = 1 := by
    ext row column
    have entry := congrFun (congrFun identity row) column
    change (matrix row (k4BasisEdges column) : ℚ) = _
    rw [show matrix row (k4BasisEdges column) =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) row column from entry]
    simp [Matrix.one_apply]
  have supports : ∀ row column, matrix row column = 0 ↔ k4RootMatrix ℚ row column = 0 := by
    intro row column
    have support := normalizedRepresentations_support_eq
      (matrix.map (Int.castRingHom ℚ)) (k4RootMatrix ℚ) k4BasisEdges rational_identity
      (k4RootMatrix_basis_block ℚ) matching row column
    change (matrix row column : ℚ) = 0 ↔ k4RootMatrix ℚ row column = 0 at support
    simpa only [Int.cast_eq_zero] using support
  have unit_entry : ∀ row column, k4RootMatrix ℚ row column ≠ 0 →
      IsUnit (matrix row column) := by
    intro row column nonzero
    exact signedInteger_isUnit _ (unimodular.apply row column)
      (fun zero => nonzero ((supports row column).mp zero))
  have unit03 := unit_entry 0 3 (by norm_num [k4RootMatrix])
  have unit13 := unit_entry 1 3 (by norm_num [k4RootMatrix])
  have unit04 := unit_entry 0 4 (by norm_num [k4RootMatrix])
  have unit24 := unit_entry 2 4 (by norm_num [k4RootMatrix])
  have unit15 := unit_entry 1 5 (by norm_num [k4RootMatrix])
  have unit25 := unit_entry 2 5 (by norm_num [k4RootMatrix])
  have zero23 : matrix 2 3 = 0 := (supports 2 3).mpr (by norm_num [k4RootMatrix])
  have zero14 : matrix 1 4 = 0 := (supports 1 4).mpr (by norm_num [k4RootMatrix])
  have zero05 : matrix 0 5 = 0 := (supports 0 5).mpr (by norm_num [k4RootMatrix])
  have triangle_zero : (matrix.submatrix id ![3, 4, 5]).det = 0 := by
    have rational_zero : ((matrix.map (Int.castRingHom ℚ)).submatrix id ![3, 4, 5]).det = 0 := by
      have root_zero : ((k4RootMatrix ℚ).submatrix id ![3, 4, 5]).det = 0 := by
        norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, k4RootMatrix]
      have vanishing := not_iff_not.mpr (show
          ((matrix.map (Int.castRingHom ℚ)).submatrix id ![3, 4, 5]).det ≠ 0 ↔
            ((k4RootMatrix ℚ).submatrix id ![3, 4, 5]).det ≠ 0 by
        rw [selectedColumns_det_ne_zero_iff_indep_injective,
          selectedColumns_det_ne_zero_iff_indep_injective]
        exact and_congr_left fun _ => by
          change (rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ))).Indep
            (Set.range ![3, 4, 5]) ↔ k4Matroid.Indep (Set.range ![3, 4, 5])
          rw [matching])
      exact not_ne_iff.mp (vanishing.mpr (not_ne_iff.mpr root_zero))
    have determinant_cast : ((matrix.submatrix id ![3, 4, 5]).det : ℚ) =
        ((matrix.map (Int.castRingHom ℚ)).submatrix id ![3, 4, 5]).det :=
      (Int.castRingHom ℚ).map_det _
    exact_mod_cast determinant_cast.trans rational_zero
  have triangle_relation : matrix 0 3 * matrix 2 4 * matrix 1 5 =
      -(matrix 0 4 * matrix 1 3 * matrix 2 5) := by
    simp [Matrix.det_fin_three, Matrix.submatrix_apply, zero23, zero14, zero05] at triangle_zero
    linarith
  let rows : Fin 3 → ℤ := ![1, -(matrix 0 3 * matrix 1 3), -(matrix 0 4 * matrix 2 4)]
  let columns : Fin 6 → ℤ :=
    ![1, rows 1, rows 2, -matrix 0 3, -matrix 0 4, -(rows 1 * matrix 1 5)]
  have row_signed : ∀ row, rows row = 1 ∨ rows row = -1 := by
    intro row
    fin_cases row
    · exact Or.inl rfl
    · exact Int.isUnit_iff.mp ((unit03.mul unit13).neg)
    · exact Int.isUnit_iff.mp ((unit04.mul unit24).neg)
  have column_signed : ∀ column, columns column = 1 ∨ columns column = -1 := by
    intro column
    fin_cases column
    · exact Or.inl rfl
    · exact row_signed 1
    · exact row_signed 2
    · exact Int.isUnit_iff.mp unit03.neg
    · exact Int.isUnit_iff.mp unit04.neg
    · exact Int.isUnit_iff.mp (((Int.isUnit_iff.mpr (row_signed 1)).mul unit15).neg)
  have square03 : matrix 0 3 * matrix 0 3 = 1 := by
    rcases Int.isUnit_iff.mp unit03 with equality | equality <;> simp [equality]
  have square13 : matrix 1 3 * matrix 1 3 = 1 := by
    rcases Int.isUnit_iff.mp unit13 with equality | equality <;> simp [equality]
  have square04 : matrix 0 4 * matrix 0 4 = 1 := by
    rcases Int.isUnit_iff.mp unit04 with equality | equality <;> simp [equality]
  have square24 : matrix 2 4 * matrix 2 4 = 1 := by
    rcases Int.isUnit_iff.mp unit24 with equality | equality <;> simp [equality]
  have square_rows : ∀ row, rows row * rows row = 1 := by
    intro row
    rcases row_signed row with equality | equality <;> simp [equality]
  have last_entry : rows 2 * columns 5 = matrix 2 5 := by
    rcases Int.isUnit_iff.mp unit03 with first | first <;>
      rcases Int.isUnit_iff.mp unit13 with second | second <;>
      rcases Int.isUnit_iff.mp unit04 with third | third <;>
      rcases Int.isUnit_iff.mp unit24 with fourth | fourth <;>
      simp_all [rows, columns]
  refine ⟨rows, columns, row_signed, column_signed, ?_⟩
  have basis_entries : ∀ row column : Fin 3, matrix row (k4BasisEdges column) =
      if row = column then 1 else 0 := by
    intro row column
    have entry := congrFun (congrFun identity row) column
    simpa [Matrix.one_apply] using entry
  ext row column
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have first_basis : matrix row 0 = if row = 0 then 1 else 0 := basis_entries row 0
  have second_basis : matrix row 1 = if row = 1 then 1 else 0 := basis_entries row 1
  have third_basis : matrix row 2 = if row = 2 then 1 else 0 := basis_entries row 2
  have entry13 : rows 1 * columns 3 = matrix 1 3 := by
    change -(matrix 0 3 * matrix 1 3) * -matrix 0 3 = _
    calc
      _ = (matrix 0 3 * matrix 0 3) * matrix 1 3 := by ring
      _ = _ := by rw [square03, one_mul]
  have entry24 : rows 2 * columns 4 = matrix 2 4 := by
    change -(matrix 0 4 * matrix 2 4) * -matrix 0 4 = _
    calc
      _ = (matrix 0 4 * matrix 0 4) * matrix 2 4 := by ring
      _ = _ := by rw [square04, one_mul]
  have entry15 : rows 1 * -columns 5 = matrix 1 5 := by
    change rows 1 * -(-(rows 1 * matrix 1 5)) = _
    rw [neg_neg, ← mul_assoc, square_rows, one_mul]
  have row_zero : rows 0 = 1 := rfl
  fin_cases row <;> fin_cases column <;>
    norm_num at first_basis second_basis third_basis <;>
    simp [k4RootMatrix, first_basis, second_basis, third_basis, zero23, zero14, zero05,
      row_zero, square_rows,
      show columns 0 = 1 from rfl, show columns 1 = rows 1 from rfl,
      show columns 2 = rows 2 from rfl] <;>
    first
    | exact entry13.symm
    | exact entry24.symm
    | simpa only [mul_neg] using entry15.symm
    | exact last_entry.symm
    | simp [columns]

theorem totallyUnimodular_k4_integral_equivalence
    (matrix : Matrix (Fin 3) (Fin 6) ℤ)
    (unimodular : matrix.IsTotallyUnimodular)
    (matching : rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ)) =
      k4Matroid) :
    ∃ operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ, ∃ signs : Fin 6 → ℤ,
      (∀ column, signs column = 1 ∨ signs column = -1) ∧
      matrix = (operation : Matrix (Fin 3) (Fin 3) ℤ) * k4RootMatrix ℤ *
        Matrix.diagonal signs := by
  have root_nonzero : ((k4RootMatrix ℚ).submatrix id k4BasisEdges).det ≠ 0 := by
    rw [k4RootMatrix_basis_block, Matrix.det_one]
    norm_num
  have rational_nonzero : ((matrix.map (Int.castRingHom ℚ)).submatrix id
      k4BasisEdges).det ≠ 0 := by
    rw [selectedColumns_det_ne_zero_iff_indep_injective] at root_nonzero ⊢
    change (rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ))).Indep
      (Set.range k4BasisEdges) ∧ Function.Injective k4BasisEdges
    rw [matching]
    exact root_nonzero
  have integer_nonzero : (matrix.submatrix id k4BasisEdges).det ≠ 0 := by
    intro zero
    apply rational_nonzero
    have casting := (Int.castRingHom ℚ).map_det (matrix.submatrix id k4BasisEdges)
    simpa [zero, Matrix.submatrix_map] using casting.symm
  have basis_unit := totallyUnimodular_basis_det_isUnit matrix unimodular k4BasisEdges
    integer_nonzero
  obtain ⟨rows, signs, row_signed, column_signed, normalized⟩ :=
    normalized_k4_representation_signs (basisNormalization matrix k4BasisEdges)
      (basisNormalization_totallyUnimodular matrix unimodular k4BasisEdges basis_unit)
      (basisNormalization_basis_block matrix k4BasisEdges basis_unit)
      ((basisNormalization_rayMatroid matrix k4BasisEdges basis_unit).trans matching)
  have row_square : Matrix.diagonal rows * Matrix.diagonal rows = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have square : (fun row => rows row * rows row) = fun _ => (1 : ℤ) := by
      funext row
      rcases row_signed row with equality | equality <;> simp [equality]
    rw [square, Matrix.diagonal_one]
  have row_unit : IsUnit (Matrix.diagonal rows) :=
    isUnit_iff_exists.mpr ⟨Matrix.diagonal rows, row_square, row_square⟩
  obtain ⟨row_operation, row_operation_value⟩ := row_unit
  let basis_operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ :=
    ⟨matrix.submatrix id k4BasisEdges, (matrix.submatrix id k4BasisEdges)⁻¹,
      Matrix.mul_nonsing_inv _ basis_unit, Matrix.nonsing_inv_mul _ basis_unit⟩
  refine ⟨basis_operation * row_operation, signs, column_signed, ?_⟩
  calc
    matrix = matrix.submatrix id k4BasisEdges * basisNormalization matrix k4BasisEdges :=
      (basisNormalization_undo matrix k4BasisEdges basis_unit).symm
    _ = _ := by rw [normalized, ← row_operation_value];
                simp [basis_operation, Matrix.mul_assoc]

end BondalThomsen
