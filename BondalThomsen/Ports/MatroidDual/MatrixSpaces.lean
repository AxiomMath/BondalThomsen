module

public import BondalThomsen.Ports.MatroidDual.Orthogonality
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

open Set Submodule Matrix Module Function

namespace Matrix

variable {Row Column Field : Type*} [_root_.Field Field]

def rowSpace (matrix : Matrix Row Column Field) : Submodule Field (Column → Field) :=
  span Field (range matrix.row)

def colSpace (matrix : Matrix Row Column Field) : Submodule Field (Row → Field) :=
  matrix.transpose.rowSpace

def rowSubmatrix (matrix : Matrix Row Column Field) (selected : Set Row) :
    Matrix selected Column Field := matrix.submatrix Subtype.val id

def colSubmatrix (matrix : Matrix Row Column Field) (selected : Set Column) :
    Matrix Row selected Field := matrix.submatrix id Subtype.val

omit [_root_.Field Field] in
@[simp] theorem rowSubmatrix_apply (matrix : Matrix Row Column Field)
    (selected : Set Row) (row : selected) (column : Column) :
    matrix.rowSubmatrix selected row column = matrix row column := rfl

omit [_root_.Field Field] in
@[simp] theorem colSubmatrix_apply (matrix : Matrix Row Column Field)
    (selected : Set Column) (row : Row) (column : selected) :
    matrix.colSubmatrix selected row column = matrix row column := rfl

omit [_root_.Field Field] in
@[simp] theorem rowSubmatrix_transpose (matrix : Matrix Row Column Field) (selected : Set Row) :
    (matrix.rowSubmatrix selected).transpose = matrix.transpose.colSubmatrix selected := rfl

omit [_root_.Field Field] in
@[simp] theorem colSubmatrix_transpose (matrix : Matrix Row Column Field)
    (selected : Set Column) :
    (matrix.colSubmatrix selected).transpose = matrix.transpose.rowSubmatrix selected := rfl

@[simp] theorem rowSpace_transpose (matrix : Matrix Row Column Field) :
    matrix.transpose.rowSpace = matrix.colSpace := rfl

@[simp] theorem colSpace_transpose (matrix : Matrix Row Column Field) :
    matrix.transpose.colSpace = matrix.rowSpace := rfl

theorem rowSpace_eq_lin_range [Fintype Row] (matrix : Matrix Row Column Field) :
    matrix.rowSpace = LinearMap.range matrix.vecMulLinear :=
  (range_vecMulLinear matrix).symm

theorem rowSubmatrix_span (matrix : Matrix Row Column Field) (selected : Set Row) :
    (matrix.rowSubmatrix selected).rowSpace = span Field (matrix.row '' selected) := by
  unfold rowSpace rowSubmatrix
  congr 1
  ext vector
  constructor
  · rintro ⟨row, rfl⟩
    exact ⟨row.val, row.property, rfl⟩
  · rintro ⟨row, member, rfl⟩
    exact ⟨⟨row, member⟩, rfl⟩

def RowBasis (matrix : Matrix Row Column Field) (selected : Set Row) : Prop :=
  LinearIndependent Field (matrix.rowSubmatrix selected).row ∧
    (matrix.rowSubmatrix selected).rowSpace = matrix.rowSpace

def ColBasis (matrix : Matrix Row Column Field) (selected : Set Column) : Prop :=
  matrix.transpose.RowBasis selected

theorem RowBasis.linearIndependent {matrix : Matrix Row Column Field} {selected : Set Row}
    (basis : matrix.RowBasis selected) :
    LinearIndependent Field (matrix.rowSubmatrix selected).row := basis.1

theorem RowBasis.rowSpace_eq {matrix : Matrix Row Column Field} {selected : Set Row}
    (basis : matrix.RowBasis selected) :
    (matrix.rowSubmatrix selected).rowSpace = matrix.rowSpace := basis.2

theorem ColBasis.linearIndependent {matrix : Matrix Row Column Field} {selected : Set Column}
    (basis : matrix.ColBasis selected) :
    LinearIndependent Field (matrix.colSubmatrix selected).col := basis.1

theorem ColBasis.colSpace_eq {matrix : Matrix Row Column Field} {selected : Set Column}
    (basis : matrix.ColBasis selected) :
    (matrix.colSubmatrix selected).colSpace = matrix.colSpace := basis.2

theorem exists_rowBasis (matrix : Matrix Row Column Field) :
    ∃ selected, matrix.RowBasis selected := by
  have empty_independent : LinearIndepOn Field matrix.row ∅ := linearIndepOn_empty _ _
  let selected := empty_independent.extend (subset_univ ∅)
  refine ⟨selected, empty_independent.linearIndepOn_extend (subset_univ ∅), ?_⟩
  rw [rowSubmatrix_span]
  exact (empty_independent.span_image_extend_eq_span_image (subset_univ ∅)).trans
    (by simp [rowSpace])

theorem rowBasis_iff_maximal_linearIndependent (matrix : Matrix Row Column Field)
    (selected : Set Row) :
    matrix.RowBasis selected ↔ Maximal (LinearIndepOn Field matrix.row) selected := by
  rw [RowBasis, rowSubmatrix_span, maximal_iff]
  change (LinearIndepOn Field matrix.row selected ∧
      span Field (matrix.row '' selected) = span Field (range matrix.row)) ↔ _
  constructor
  · rintro ⟨independent, spanning⟩
    refine ⟨independent, ?_⟩
    intro larger larger_independent subset
    apply Set.Subset.antisymm subset ?_
    intro element member
    have vector_span : matrix.row element ∈ span Field (matrix.row '' selected) := by
      rw [spanning]
      exact subset_span (mem_range_self element)
    have inserted := larger_independent.mono (Set.insert_subset member subset)
    exact (linearIndepOn_insert_iff.mp inserted).2 vector_span
  · rintro ⟨independent, maximal⟩
    refine ⟨independent, (span_mono (image_subset_range _ _)).antisymm ?_⟩
    apply span_le.mpr
    rintro vector ⟨element, rfl⟩
    by_contra not_spanned
    have absent : element ∉ selected := fun member =>
      not_spanned (subset_span (mem_image_of_mem matrix.row member))
    have inserted := (linearIndepOn_insert absent).mpr ⟨independent, not_spanned⟩
    exact absent ((maximal inserted (subset_insert _ _)).symm.le (mem_insert _ _))

theorem colBasis_iff_maximal_linearIndependent (matrix : Matrix Row Column Field)
    (selected : Set Column) :
    matrix.ColBasis selected ↔ Maximal (LinearIndepOn Field matrix.col) selected :=
  rowBasis_iff_maximal_linearIndependent matrix.transpose selected

theorem rows_linearIndependent_iff [Fintype Row] (matrix : Matrix Row Column Field) :
    LinearIndependent Field matrix.row ↔ LinearMap.ker matrix.vecMulLinear = ⊥ := by
  rw [Fintype.linearIndependent_iff, Submodule.eq_bot_iff]
  constructor
  · intro independent vector member
    have zero : ∑ row, vector row • matrix.row row = 0 := by
      simpa only [LinearMap.mem_ker, vecMulLinear_apply, vecMul_eq_sum, Matrix.row] using member
    exact funext (independent vector zero)
  · intro injective vector zero row
    have member : vector ∈ LinearMap.ker matrix.vecMulLinear := by
      simpa only [LinearMap.mem_ker, vecMulLinear_apply, vecMul_eq_sum, Matrix.row] using zero
    exact congrFun (injective vector member) row

theorem cols_linearIndependent_iff [Fintype Column] (matrix : Matrix Row Column Field) :
    LinearIndependent Field matrix.col ↔ LinearMap.ker matrix.mulVecLin = ⊥ := by
  have maps : matrix.transpose.vecMulLinear = matrix.mulVecLin := by
    ext vector row
    simp only [vecMulLinear_apply, mulVecLin_apply, vecMul_transpose]
  simpa only [maps, Matrix.row, Matrix.col] using rows_linearIndependent_iff matrix.transpose

theorem dotProduct_eq_zero_of_mem_span [Fintype Column] {vector other : Column → Field}
    {selected : Set (Column → Field)} (member : other ∈ span Field selected)
    (vanishes : ∀ candidate ∈ selected, dotProduct vector candidate = 0) :
    dotProduct vector other = 0 := by
  have contains : span Field selected ≤ LinearMap.ker ((dotProductBilin Field Field) vector) :=
    span_le.mpr vanishes
  exact contains member

noncomputable def nullSpace [Fintype Column] (matrix : Matrix Row Column Field) :
    Submodule Field (Column → Field) := matrix.rowSpace.orthSpace

theorem mem_nullSpace_iff [Fintype Column] (matrix : Matrix Row Column Field)
    (vector : Column → Field) : vector ∈ matrix.nullSpace ↔ matrix.mulVec vector = 0 := by
  rw [nullSpace, Submodule.mem_orthSpace_iff]
  constructor
  · intro vanishes
    ext row
    have zero := vanishes (matrix.row row) (subset_span (mem_range_self row))
    simpa only [Matrix.row, dotProduct_comm, mulVec, Pi.zero_apply] using zero
  · intro zero other member
    apply dotProduct_eq_zero_of_mem_span member
    rintro candidate ⟨row, rfl⟩
    have equation := congrFun zero row
    simpa only [Matrix.row, dotProduct_comm, mulVec, Pi.zero_apply] using equation

theorem orthSpace_nullSpace_eq_rowSpace [Fintype Column] (matrix : Matrix Row Column Field) :
    matrix.nullSpace.orthSpace = matrix.rowSpace :=
  Submodule.orthSpace_orthSpace matrix.rowSpace

end Matrix
