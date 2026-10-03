module

public import BondalThomsen.Ports.MatroidDual.MatrixSpaces

@[expose] public section

open Set Submodule Matrix Module Function

namespace Matrix

variable {Row OtherRow Column Field : Type*} [_root_.Field Field]

theorem nullSpace_eq_ker_mulVecLin [Fintype Column] (matrix : Matrix Row Column Field) :
    matrix.nullSpace = LinearMap.ker matrix.mulVecLin := by
  ext vector
  simp only [mem_nullSpace_iff, LinearMap.mem_ker, mulVecLin_apply]

theorem colSpace_eq_top_iff_linearIndependent_rows [Fintype Row]
    (matrix : Matrix Row Column Field) :
    matrix.colSpace = ⊤ ↔ LinearIndependent Field matrix.row := by
  have orthogonal : matrix.colSpace.orthSpace = LinearMap.ker matrix.vecMulLinear := by
    rw [colSpace, ← nullSpace, nullSpace_eq_ker_mulVecLin]
    congr 1
    ext vector row
    simp only [mulVecLin_apply, vecMulLinear_apply, mulVec_transpose]
  rw [rows_linearIndependent_iff, ← orthogonal]
  constructor
  · intro top
    rw [top, Submodule.orthSpace_top]
  · intro bottom
    have double := Submodule.orthSpace_orthSpace matrix.colSpace
    rwa [bottom, Submodule.orthSpace_bot, eq_comm] at double

theorem ColBasis.rows_linearIndependent [Fintype Row]
    {matrix : Matrix Row Column Field} {selected : Set Column}
    (basis : matrix.ColBasis selected) (independent : LinearIndependent Field matrix.row) :
    LinearIndependent Field (matrix.colSubmatrix selected).row := by
  rw [← colSpace_eq_top_iff_linearIndependent_rows, basis.colSpace_eq]
  exact (colSpace_eq_top_iff_linearIndependent_rows matrix).mpr independent

theorem rowSpace_colSubmatrix (matrix : Matrix Row Column Field) (selected : Set Column) :
    (matrix.colSubmatrix selected).rowSpace =
      matrix.rowSpace.map (LinearMap.funLeft Field Field (Subtype.val : selected → Column)) := by
  rw [rowSpace, rowSpace, Submodule.map_span]
  congr 1
  ext vector
  constructor
  · rintro ⟨row, rfl⟩
    exact ⟨matrix.row row, mem_range_self row, rfl⟩
  · rintro ⟨other, ⟨row, rfl⟩, rfl⟩
    exact ⟨row, rfl⟩

theorem cols_linearIndependent_iff_of_rowSpaces_eq [Fintype Column]
    {first : Matrix Row Column Field} {second : Matrix OtherRow Column Field}
    (equal : first.rowSpace = second.rowSpace) (selected : Set Column) :
    LinearIndependent Field (first.colSubmatrix selected).col ↔
      LinearIndependent Field (second.colSubmatrix selected).col := by
  classical
  rw [cols_linearIndependent_iff, cols_linearIndependent_iff,
    ← nullSpace_eq_ker_mulVecLin, ← nullSpace_eq_ker_mulVecLin,
    nullSpace, nullSpace, rowSpace_colSubmatrix, rowSpace_colSubmatrix, equal]

theorem colBases_eq_of_rowSpaces_eq [Fintype Column]
    {first : Matrix Row Column Field} {second : Matrix OtherRow Column Field}
    (equal : first.rowSpace = second.rowSpace) : first.ColBasis = second.ColBasis := by
  have dependencies : LinearIndepOn Field first.col = LinearIndepOn Field second.col := by
    funext selected
    apply propext
    exact cols_linearIndependent_iff_of_rowSpaces_eq equal selected
  funext selected
  apply propext
  rw [colBasis_iff_maximal_linearIndependent, colBasis_iff_maximal_linearIndependent,
    dependencies]

theorem sum_subtype_eq_sum_of_zero [Fintype Column] (selected : Set Column)
    [DecidablePred (· ∈ selected)]
    (terms : Column → Field) (zero : ∀ column ∉ selected, terms column = 0) :
    ∑ column : selected, terms column = ∑ column, terms column := by
  have complement : (∑ column : ↥(selectedᶜ), terms column) = 0 := by
    apply Finset.sum_eq_zero
    intro column member
    exact zero column column.property
  have partition := Fintype.sum_subtype_add_sum_subtype (· ∈ selected) terms
  change (∑ column : selected, terms column) +
    (∑ column : ↥(selectedᶜ), terms column) = ∑ column, terms column at partition
  rwa [complement, add_zero] at partition

theorem colBasis_iff_aux [Fintype Column] [Fintype Row] [Fintype OtherRow]
    {first : Matrix Row Column Field} {second : Matrix OtherRow Column Field}
    {selected : Set Column} (orthogonal : first.rowSpace = second.nullSpace)
    (first_independent : LinearIndependent Field first.row)
    (second_independent : LinearIndependent Field second.row)
    (basis : first.ColBasis selected) : second.ColBasis selectedᶜ := by
  classical
  have second_space : second.rowSpace = first.nullSpace := by
    rw [nullSpace] at orthogonal ⊢
    exact Submodule.eq_orthSpace_comm.mp orthogonal
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro coefficients zero column
    let extended : Column → Field := fun index =>
      if member : index ∈ selectedᶜ then coefficients ⟨index, member⟩ else 0
    have outside : ∀ index ∉ selectedᶜ, extended index = 0 := by
      intro index absent
      simp only [extended, dite_eq_right absent]
    have null : extended ∈ second.nullSpace := by
      rw [mem_nullSpace_iff]
      ext row
      rw [mulVec, dotProduct, ← sum_subtype_eq_sum_of_zero selectedᶜ _
        (fun index absent => by rw [outside index absent, mul_zero])]
      have values : (∑ index : ↥(selectedᶜ), second row index * extended index) =
          ∑ index : ↥(selectedᶜ), coefficients index * second row index := by
        apply Finset.sum_congr rfl
        intro index member
        simp only [extended, dite_eq_left index.property, mul_comm]
      rw [values]
      have equation := congrFun zero row
      simpa [Matrix.col, Finset.sum_apply, smul_eq_mul] using equation
    rw [← orthogonal, rowSpace_eq_lin_range, LinearMap.mem_range] at null
    obtain ⟨row_coefficients, representation⟩ := null
    have kernel : row_coefficients ∈
        LinearMap.ker (first.colSubmatrix selected).vecMulLinear := by
      rw [LinearMap.mem_ker]
      ext index
      have coordinate := congrFun representation index
      simpa [vecMulLinear_apply, vecMul, dotProduct, extended, index.property] using coordinate
    rw [(rows_linearIndependent_iff _).mp (basis.rows_linearIndependent first_independent)]
      at kernel
    have row_zero : row_coefficients = 0 := kernel
    have extended_zero : extended = 0 := by
      rw [row_zero, map_zero] at representation
      exact representation.symm
    have coordinate := congrFun extended_zero column
    simpa only [extended, dite_eq_left column.property, Pi.zero_apply] using coordinate
  · change (second.colSubmatrix selectedᶜ).colSpace = second.colSpace
    rw [(colSpace_eq_top_iff_linearIndependent_rows second).mpr second_independent,
      colSpace_eq_top_iff_linearIndependent_rows, Fintype.linearIndependent_iff]
    intro coefficients zero row
    let vector := second.vecMulLinear coefficients
    have complement_zero : ∀ index ∉ selected, vector index = 0 := by
      intro index absent
      have equation := congrFun zero (⟨index, absent⟩ : ↥(selectedᶜ))
      simpa [vector, vecMulLinear_apply, vecMul_eq_sum, Matrix.row, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] using equation
    have null : vector ∈ first.nullSpace := by
      rw [← second_space, rowSpace_eq_lin_range]
      exact LinearMap.mem_range_self second.vecMulLinear coefficients
    have selected_zero : ∑ index : selected, vector index •
        (first.colSubmatrix selected).col index = 0 := by
      ext first_row
      have equation := congrFun ((mem_nullSpace_iff first vector).mp null) first_row
      rw [mulVec, dotProduct,
        ← sum_subtype_eq_sum_of_zero selected _
          (fun index absent => by rw [complement_zero index absent, mul_zero])] at equation
      simpa [Matrix.col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using equation
    have on_selected := Fintype.linearIndependent_iff.mp basis.linearIndependent
      (fun index => vector index) selected_zero
    have vector_zero : vector = 0 := by
      ext index
      by_cases member : index ∈ selected
      · exact on_selected ⟨index, member⟩
      · exact complement_zero index member
    have kernel : coefficients ∈ LinearMap.ker second.vecMulLinear := vector_zero
    rw [(rows_linearIndependent_iff second).mp second_independent] at kernel
    exact congrFun (show coefficients = 0 from kernel) row

theorem colBasis_iff_colBasis_compl_of_orth [Fintype Column]
    {first : Matrix Row Column Field} {second : Matrix OtherRow Column Field}
    {selected : Set Column} (orthogonal : first.rowSpace = second.nullSpace) :
    first.ColBasis selected ↔ second.ColBasis selectedᶜ := by
  classical
  obtain ⟨first_rows, first_basis⟩ := first.exists_rowBasis
  obtain ⟨second_rows, second_basis⟩ := second.exists_rowBasis
  let : Finite first_rows := first_basis.linearIndependent.finite
  let : Finite second_rows := second_basis.linearIndependent.finite
  let : Fintype first_rows := Fintype.ofFinite first_rows
  let : Fintype second_rows := Fintype.ofFinite second_rows
  have restricted : (first.rowSubmatrix first_rows).rowSpace =
      (second.rowSubmatrix second_rows).nullSpace := by
    rw [nullSpace, first_basis.rowSpace_eq, second_basis.rowSpace_eq]
    exact orthogonal
  rw [← colBases_eq_of_rowSpaces_eq first_basis.rowSpace_eq,
    ← colBases_eq_of_rowSpaces_eq second_basis.rowSpace_eq]
  constructor
  · exact colBasis_iff_aux restricted first_basis.linearIndependent second_basis.linearIndependent
  · intro basis
    have reverse : (second.rowSubmatrix second_rows).rowSpace =
        (first.rowSubmatrix first_rows).nullSpace := by
      rw [nullSpace] at restricted ⊢
      exact Submodule.eq_orthSpace_comm.mp restricted
    simpa only [compl_compl] using
      colBasis_iff_aux reverse second_basis.linearIndependent first_basis.linearIndependent basis

end Matrix

namespace Module.Basis

variable {Index Column Field : Type*} [_root_.Field Field]
    {space : Submodule Field (Column → Field)}

noncomputable def toRowMatrix (basis : Basis Index Field space) : Matrix Index Column Field :=
  fun index column => (basis index : Column → Field) column

theorem toRowMatrix_rowSpace (basis : Basis Index Field space) :
    basis.toRowMatrix.rowSpace = space := by
  have spanning := congrArg (Submodule.map space.subtype) basis.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at spanning
  change span Field (range fun index => (basis index : Column → Field)) = space
  simpa only [← Set.range_comp, Function.comp_def, Submodule.coe_subtype] using spanning

end Module.Basis
