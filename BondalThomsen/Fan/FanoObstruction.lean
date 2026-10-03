module

public import BondalThomsen.Matroid.UnimodularEquivalence
public import BondalThomsen.Ports.Matroid.ProjectiveBound
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace BondalThomsen

open Matrix

def fanoMatrix (Ring : Type*) [Zero Ring] [One Ring] : Matrix (Fin 3) (Fin 7) Ring :=
  !![1, 0, 0, 1, 1, 0, 1;
     0, 1, 0, 1, 0, 1, 1;
     0, 0, 1, 0, 1, 1, 1]

noncomputable def fanoMatroid : Matroid (Fin 7) :=
  rayMatroid (Field := ZMod 2) (fanoMatrix (ZMod 2)).col

def fanoBasisColumns : Fin 3 → Fin 7 := Fin.castAdd 4

theorem fanoMatrix_basis_block (Ring : Type*) [Semiring Ring] :
    (fanoMatrix Ring).submatrix id fanoBasisColumns = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [fanoMatrix, fanoBasisColumns]

theorem fanoMatrix_columns_nonzero (column : Fin 7) :
    (fanoMatrix (ZMod 2)).col column ≠ 0 := by
  intro equality
  have row0 := congrFun equality 0
  have row1 := congrFun equality 1
  have row2 := congrFun equality 2
  fin_cases column <;> simp_all [fanoMatrix]

theorem selectedColumns_det_ne_zero_iff {Index Label Field : Type*}
    [_root_.Field Field] [Fintype Index] [DecidableEq Index]
    (matrix : Matrix Index Label Field) (columns : Index → Label)
    (injective : Function.Injective columns) :
    (matrix.submatrix id columns).det ≠ 0 ↔
      (rayMatroid (Field := Field) matrix.col).Indep (Set.range columns) := by
  rw [rayMatroid_indep_iff, linearIndepOn_range_iff injective]
  have columns_eq : (matrix.submatrix id columns).col = matrix.col ∘ columns := rfl
  rw [← columns_eq, Matrix.linearIndependent_cols_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem selectedColumns_det_ne_zero_iff_indep_injective {Index Label Field : Type*}
    [_root_.Field Field] [Fintype Index] [DecidableEq Index]
    (matrix : Matrix Index Label Field) (columns : Index → Label) :
    (matrix.submatrix id columns).det ≠ 0 ↔
      (rayMatroid (Field := Field) matrix.col).Indep (Set.range columns) ∧
        Function.Injective columns := by
  constructor
  · intro nonzero
    have independent := Matrix.linearIndependent_cols_of_det_ne_zero nonzero
    have injective : Function.Injective columns := by
      intro index other equal
      apply independent.injective
      funext row
      change matrix row (columns index) = matrix row (columns other)
      rw [equal]
    exact ⟨(selectedColumns_det_ne_zero_iff matrix columns injective).mp nonzero, injective⟩
  · rintro ⟨independent, injective⟩
    exact (selectedColumns_det_ne_zero_iff matrix columns injective).mpr independent

theorem identityReplacement_det {Index Label Ring : Type*} [CommRing Ring]
    [Fintype Index] [DecidableEq Index]
    (matrix : Matrix Index Label Ring) (basis_columns : Index → Label)
    (identity : matrix.submatrix id basis_columns = 1) (row : Index) (column : Label) :
    (matrix.submatrix id (Function.update basis_columns row column)).det = matrix row column := by
  have updated : matrix.submatrix id (Function.update basis_columns row column) =
      (1 : Matrix Index Index Ring).updateCol row (matrix.col column) := by
    ext other index
    by_cases equal : index = row
    · subst index
      simp
    · have basis_entry := congrFun (congrFun identity other) index
      simpa [Matrix.updateCol_apply, Function.update_of_ne equal, equal] using basis_entry
  rw [updated, ← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

theorem normalizedRepresentations_support_eq {Index Label FirstField SecondField : Type*}
    [_root_.Field FirstField] [_root_.Field SecondField]
    [Fintype Index] [DecidableEq Index]
    (first : Matrix Index Label FirstField) (second : Matrix Index Label SecondField)
    (basis_columns : Index → Label)
    (first_identity : first.submatrix id basis_columns = 1)
    (second_identity : second.submatrix id basis_columns = 1)
    (matching : rayMatroid (Field := FirstField) first.col =
      rayMatroid (Field := SecondField) second.col) (row : Index) (column : Label) :
    first row column = 0 ↔ second row column = 0 := by
  have determinant_nonzero :
      (first.submatrix id (Function.update basis_columns row column)).det ≠ 0 ↔
        (second.submatrix id (Function.update basis_columns row column)).det ≠ 0 := by
    rw [selectedColumns_det_ne_zero_iff_indep_injective,
      selectedColumns_det_ne_zero_iff_indep_injective, matching]
  rw [identityReplacement_det first basis_columns first_identity,
    identityReplacement_det second basis_columns second_identity] at determinant_nonzero
  exact not_iff_not.mp determinant_nonzero

theorem signedInteger_bounds (entry : ℤ) (signed : entry ∈ Set.range SignType.cast) :
    -1 ≤ entry ∧ entry ≤ 1 := by
  obtain ⟨sign, rfl⟩ := signed
  cases sign <;> norm_num [SignType.cast]

theorem signedInteger_isUnit (entry : ℤ) (signed : entry ∈ Set.range SignType.cast)
    (nonzero : entry ≠ 0) : IsUnit entry := by
  obtain ⟨sign, equality⟩ := signed
  apply Int.isUnit_iff.mpr
  cases sign <;> simp_all [SignType.cast]

theorem unit_pair_products_eq_of_signed_difference {first second third fourth : ℤ}
    (first_unit : IsUnit first) (second_unit : IsUnit second)
    (third_unit : IsUnit third) (fourth_unit : IsUnit fourth)
    (signed : first * fourth - second * third ∈ Set.range SignType.cast) :
    first * fourth = second * third := by
  have bounds := signedInteger_bounds _ signed
  rcases Int.isUnit_iff.mp (first_unit.mul fourth_unit) with positive | negative <;>
    rcases Int.isUnit_iff.mp (second_unit.mul third_unit) with other_positive | other_negative <;>
    omega

theorem fano_support_not_totallyUnimodular (matrix : Matrix (Fin 3) (Fin 7) ℤ)
    (support : ∀ row column,
      matrix row column = 0 ↔ fanoMatrix (ZMod 2) row column = 0) :
    ¬ matrix.IsTotallyUnimodular := by
  intro unimodular
  have unit_entry : ∀ row column, fanoMatrix (ZMod 2) row column ≠ 0 →
      IsUnit (matrix row column) := by
    intro row column nonzero
    exact signedInteger_isUnit _ (unimodular.apply row column)
      (fun zero => nonzero ((support row column).mp zero))
  have unit03 := unit_entry 0 3 (by norm_num [fanoMatrix])
  have unit13 := unit_entry 1 3 (by norm_num [fanoMatrix])
  have unit04 := unit_entry 0 4 (by norm_num [fanoMatrix])
  have unit24 := unit_entry 2 4 (by norm_num [fanoMatrix])
  have unit15 := unit_entry 1 5 (by norm_num [fanoMatrix])
  have unit25 := unit_entry 2 5 (by norm_num [fanoMatrix])
  have unit06 := unit_entry 0 6 (by norm_num [fanoMatrix])
  have unit16 := unit_entry 1 6 (by norm_num [fanoMatrix])
  have unit26 := unit_entry 2 6 (by norm_num [fanoMatrix])
  have zero23 : matrix 2 3 = 0 := (support 2 3).mpr (by norm_num [fanoMatrix])
  have zero14 : matrix 1 4 = 0 := (support 1 4).mpr (by norm_num [fanoMatrix])
  have zero05 : matrix 0 5 = 0 := (support 0 5).mpr (by norm_num [fanoMatrix])
  have first_minor :=
    (Matrix.isTotallyUnimodular_iff_fintype matrix).mp unimodular (Fin 2) ![0, 1] ![3, 6]
  have second_minor :=
    (Matrix.isTotallyUnimodular_iff_fintype matrix).mp unimodular (Fin 2) ![0, 2] ![4, 6]
  have third_minor :=
    (Matrix.isTotallyUnimodular_iff_fintype matrix).mp unimodular (Fin 2) ![1, 2] ![5, 6]
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at first_minor second_minor third_minor
  have first_relation :=
    unit_pair_products_eq_of_signed_difference unit03 unit06 unit13 unit16 first_minor
  have second_relation :=
    unit_pair_products_eq_of_signed_difference unit04 unit06 unit24 unit26 second_minor
  have third_relation :=
    unit_pair_products_eq_of_signed_difference unit15 unit16 unit25 unit26 third_minor
  have products_equal : matrix 0 3 * matrix 2 4 * matrix 1 5 =
      matrix 0 4 * matrix 1 3 * matrix 2 5 := by
    apply mul_right_cancel₀ (unit06.mul unit26).ne_zero
    calc
      (matrix 0 3 * matrix 2 4 * matrix 1 5) * (matrix 0 6 * matrix 2 6) =
          matrix 0 3 * (matrix 0 6 * matrix 2 4) * (matrix 1 5 * matrix 2 6) := by ring
      _ = matrix 0 3 * (matrix 0 4 * matrix 2 6) * (matrix 1 6 * matrix 2 5) := by
        rw [← second_relation, third_relation]
      _ = (matrix 0 3 * matrix 1 6) * (matrix 0 4 * matrix 2 6) * matrix 2 5 := by ring
      _ = (matrix 0 6 * matrix 1 3) * (matrix 0 4 * matrix 2 6) * matrix 2 5 := by
        rw [first_relation]
      _ = (matrix 0 4 * matrix 1 3 * matrix 2 5) * (matrix 0 6 * matrix 2 6) := by ring
  have final_minor :=
    (Matrix.isTotallyUnimodular_iff_fintype matrix).mp unimodular (Fin 3) id ![3, 4, 5]
  have final_bound := signedInteger_bounds _ final_minor
  simp [Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    zero23, zero14, zero05] at final_bound
  rcases Int.isUnit_iff.mp ((unit03.mul unit24).mul unit15) with positive | negative <;>
    nlinarith [products_equal]

theorem fanoMatroid_not_totallyUnimodular_representation
    (matrix : Matrix (Fin 3) (Fin 7) ℤ)
    (matching : rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ)) =
      fanoMatroid) :
    ¬ matrix.IsTotallyUnimodular := by
  intro unimodular
  have basis_nonzero : ((matrix.map (Int.castRingHom ℚ)).submatrix id fanoBasisColumns).det ≠ 0 := by
    rw [selectedColumns_det_ne_zero_iff_indep_injective]
    have binary_basis_nonzero :
        ((fanoMatrix (ZMod 2)).submatrix id fanoBasisColumns).det ≠ 0 := by
      rw [fanoMatrix_basis_block, Matrix.det_one]
      exact one_ne_zero
    have binary_independence :=
      (selectedColumns_det_ne_zero_iff_indep_injective _ _).mp binary_basis_nonzero
    simpa only [fanoMatroid, Matrix.col_apply, Matrix.map_apply] using
      matching.symm ▸ binary_independence
  have integer_basis_nonzero : (matrix.submatrix id fanoBasisColumns).det ≠ 0 := by
    have determinant_cast : ((matrix.submatrix id fanoBasisColumns).det : ℚ) =
        ((matrix.map (Int.castRingHom ℚ)).submatrix id fanoBasisColumns).det :=
      (Int.castRingHom ℚ).map_det _
    intro zero
    apply basis_nonzero
    rw [← determinant_cast, zero, Int.cast_zero]
  have basis_unit :=
    totallyUnimodular_basis_det_isUnit matrix unimodular fanoBasisColumns integer_basis_nonzero
  let normalized := basisNormalization matrix fanoBasisColumns
  have normalized_tu :=
    basisNormalization_totallyUnimodular matrix unimodular fanoBasisColumns basis_unit
  have normalized_identity := basisNormalization_basis_block matrix fanoBasisColumns basis_unit
  have rational_identity : (normalized.map (Int.castRingHom ℚ)).submatrix id fanoBasisColumns = 1 := by
    ext row column
    have identity_entry := congrFun (congrFun normalized_identity row) column
    change (normalized row (fanoBasisColumns column) : ℚ) = (1 : Matrix (Fin 3) (Fin 3) ℚ) row column
    change basisNormalization matrix fanoBasisColumns row (fanoBasisColumns column) =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) row column at identity_entry
    change (basisNormalization matrix fanoBasisColumns row (fanoBasisColumns column) : ℚ) =
      (1 : Matrix (Fin 3) (Fin 3) ℚ) row column
    rw [identity_entry]
    simp [Matrix.one_apply]
  have normalized_matching :
      rayMatroid (Field := ℚ) (normalized.map (Int.castRingHom ℚ)).col =
        rayMatroid (Field := ZMod 2) (fanoMatrix (ZMod 2)).col := by
    change rayMatroid (Field := ℚ)
        (fun column row => (basisNormalization matrix fanoBasisColumns row column : ℚ)) =
      fanoMatroid
    rw [basisNormalization_rayMatroid matrix fanoBasisColumns basis_unit, matching]
  apply fano_support_not_totallyUnimodular normalized _ normalized_tu
  intro row column
  have support := normalizedRepresentations_support_eq
    (normalized.map (Int.castRingHom ℚ)) (fanoMatrix (ZMod 2)) fanoBasisColumns
    rational_identity (fanoMatrix_basis_block _) normalized_matching row column
  change (normalized row column : ℚ) = 0 ↔ _ at support
  simpa only [Int.cast_eq_zero] using support

theorem fanoMatroid_not_binary_totallyUnimodular_representation
    (matrix : Matrix (Fin 3) (Fin 7) ℤ)
    (matching : rayMatroid (Field := ZMod 2)
      (fun column row => (matrix row column : ZMod 2)) = fanoMatroid) :
    ¬ matrix.IsTotallyUnimodular := by
  intro unimodular
  have rational_matching :
      rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ)) = fanoMatroid := by
    rw [← totallyUnimodular_cast_rayMatroid (Field := ZMod 2) matrix unimodular, matching]
  exact fanoMatroid_not_totallyUnimodular_representation matrix rational_matching unimodular

theorem binaryThree_nonzero_card :
    Fintype.card {vector : Fin 3 → ZMod 2 // vector ≠ 0} = 7 := by
  rw [Fintype.card_subtype_compl (fun vector : Fin 3 → ZMod 2 => vector = 0)]
  norm_num [Fintype.card_pi, ZMod.card]

theorem totallyUnimodular_binary_columns_card_le_six {Column : Type*} [Fintype Column]
    (matrix : Matrix (Fin 3) Column ℤ) (unimodular : matrix.IsTotallyUnimodular)
    (nonzero : ∀ column, (matrix.map (Int.castRingHom (ZMod 2))).col column ≠ 0)
    (injective : Function.Injective (matrix.map (Int.castRingHom (ZMod 2))).col) :
    Fintype.card Column ≤ 6 := by
  classical
  let binary := matrix.map (Int.castRingHom (ZMod 2))
  let to_nonzero : Column → {vector : Fin 3 → ZMod 2 // vector ≠ 0} :=
    fun column => ⟨binary.col column, nonzero column⟩
  have to_nonzero_injective : Function.Injective to_nonzero := by
    intro first second equality
    exact injective (congrArg Subtype.val equality)
  have card_bound := Fintype.card_le_of_injective to_nonzero to_nonzero_injective
  rw [binaryThree_nonzero_card] at card_bound
  by_contra too_many
  have card_seven : Fintype.card Column = 7 := by omega
  have bijective : Function.Bijective to_nonzero :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨to_nonzero_injective, card_seven.trans binaryThree_nonzero_card.symm⟩
  let equivalence := Equiv.ofBijective to_nonzero bijective
  let selected : Fin 7 → Column := fun column =>
    equivalence.symm ⟨(fanoMatrix (ZMod 2)).col column, fanoMatrix_columns_nonzero column⟩
  have selected_binary : ∀ column, binary.col (selected column) =
      (fanoMatrix (ZMod 2)).col column := by
    intro column
    have evaluation := equivalence.apply_symm_apply
      ⟨(fanoMatrix (ZMod 2)).col column, fanoMatrix_columns_nonzero column⟩
    exact congrArg Subtype.val evaluation
  let selected_matrix := matrix.submatrix id selected
  have selected_matroid : rayMatroid (Field := ZMod 2)
      (fun column row => (selected_matrix row column : ZMod 2)) = fanoMatroid := by
    have columns_eq : (fun column row => (selected_matrix row column : ZMod 2)) =
        (fanoMatrix (ZMod 2)).col := by
      funext column row
      exact congrFun (selected_binary column) row
    rw [columns_eq]
    rfl
  exact fanoMatroid_not_binary_totallyUnimodular_representation selected_matrix
    selected_matroid (unimodular.submatrix _ _)

theorem totallyUnimodular_simple_binary_card_le_six {Column : Type*} [Fintype Column]
    (matrix : Matrix (Fin 3) Column ℤ) (unimodular : matrix.IsTotallyUnimodular)
    [simple : (rayMatroid (Field := ZMod 2)
      (fun column row => (matrix row column : ZMod 2))).Simple] :
    Fintype.card Column ≤ 6 := by
  let matroid := rayMatroid (Field := ZMod 2)
    (fun column row => (matrix row column : ZMod 2))
  let representation := Matroid.repOfRays
    (Field := ZMod 2) (fun column row => (matrix row column : ZMod 2))
  have nonzero : ∀ column, representation column ≠ 0 := by
    intro column
    exact (representation.ne_zero_iff_isNonloop column).mpr
      ((Matroid.Simple.parallel_iff_eq (by simp [matroid] : column ∈ matroid.E)).mpr rfl).1
  have injective : Function.Injective representation := by
    intro first second equality
    have parallel : matroid.Parallel first second := by
      rw [representation.parallel_iff_span_eq]
      exact ⟨nonzero first, nonzero second, by rw [equality]⟩
    exact (Matroid.Simple.parallel_iff_eq (by simp [matroid] : first ∈ matroid.E)).mp parallel
  exact totallyUnimodular_binary_columns_card_le_six matrix unimodular nonzero injective

theorem totallyUnimodular_simple_rational_card_le_six {Column : Type*} [Fintype Column]
    (matrix : Matrix (Fin 3) Column ℤ) (unimodular : matrix.IsTotallyUnimodular)
    [simple : (rayMatroid (Field := ℚ)
      (fun column row => (matrix row column : ℚ))).Simple] :
    Fintype.card Column ≤ 6 := by
  have binary_eq := totallyUnimodular_cast_rayMatroid (Field := ZMod 2) matrix unimodular
  let : (rayMatroid (Field := ZMod 2)
      (fun column row => (matrix row column : ZMod 2))).Simple := binary_eq.symm ▸ simple
  exact totallyUnimodular_simple_binary_card_le_six matrix unimodular

end BondalThomsen
