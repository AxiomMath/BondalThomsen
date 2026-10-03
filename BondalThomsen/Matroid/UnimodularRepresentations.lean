module

public import BondalThomsen.Ports.RankMinors
public import BondalThomsen.Ports.Matroid.StandardRepresentation
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

@[expose] public section

namespace BondalThomsen

open Matrix

variable {Row Column Field : Type*} [_root_.Field Field]

theorem signedEntry_cast_ne_zero_iff (entry : ℤ) (signed : entry ∈ Set.range SignType.cast) :
    (entry : Field) ≠ 0 ↔ entry ≠ 0 := by
  obtain ⟨sign, rfl⟩ := signed
  cases sign <;> simp [SignType.cast]

theorem totallyUnimodular_minor_cast_ne_zero_iff (matrix : Matrix Row Column ℤ)
    (unimodular : matrix.IsTotallyUnimodular) (size : ℕ)
    (rows : Fin size → Row) (columns : Fin size → Column) :
    ((matrix.map (fun entry => (entry : Field))).submatrix rows columns).det ≠ 0 ↔
      (matrix.submatrix rows columns).det ≠ 0 := by
  have signed := (Matrix.isTotallyUnimodular_iff matrix).mp unimodular size rows columns
  have determinant_cast : ((matrix.submatrix rows columns).det : Field) =
      ((matrix.map (fun entry => (entry : Field))).submatrix rows columns).det :=
    (Int.castRingHom Field).map_det (matrix.submatrix rows columns)
  rw [← determinant_cast]
  exact signedEntry_cast_ne_zero_iff _ signed

theorem totallyUnimodular_cast_rank [Fintype Row] [Fintype Column]
    (matrix : Matrix Row Column ℤ) (unimodular : matrix.IsTotallyUnimodular) :
    (matrix.map (fun entry => (entry : Field))).rank =
      (matrix.map (fun entry => (entry : ℚ))).rank := by
  have minor_equivalence : ∀ (size : ℕ) (rows : Fin size → Row) (columns : Fin size → Column),
      ((matrix.map (fun entry => (entry : Field))).submatrix rows columns).det ≠ 0 ↔
        ((matrix.map (fun entry => (entry : ℚ))).submatrix rows columns).det ≠ 0 := by
    intro size rows columns
    exact (totallyUnimodular_minor_cast_ne_zero_iff (Field := Field) matrix unimodular
      size rows columns).trans
      (totallyUnimodular_minor_cast_ne_zero_iff (Field := ℚ) matrix unimodular
        size rows columns).symm
  apply Nat.le_antisymm
  · obtain ⟨rows, columns, nonzero⟩ :=
      Matrix.exists_submatrix_det_ne_zero_of_le_rank
        (matrix.map (fun entry => (entry : Field))) le_rfl
    exact Matrix.le_rank_of_submatrix_det_ne_zero _ rows columns
      ((minor_equivalence _ rows columns).mp nonzero)
  · obtain ⟨rows, columns, nonzero⟩ :=
      Matrix.exists_submatrix_det_ne_zero_of_le_rank
        (matrix.map (fun entry => (entry : ℚ))) le_rfl
    exact Matrix.le_rank_of_submatrix_det_ne_zero _ rows columns
      ((minor_equivalence _ rows columns).mpr nonzero)

theorem totallyUnimodular_cast_linearIndependent_iff [Fintype Row] [Fintype Column]
    (matrix : Matrix Row Column ℤ) (unimodular : matrix.IsTotallyUnimodular) :
    LinearIndependent Field (fun column row => (matrix row column : Field)) ↔
      LinearIndependent ℚ (fun column row => (matrix row column : ℚ)) := by
  have rank_eq := totallyUnimodular_cast_rank (Field := Field) matrix unimodular
  rw [linearIndependent_iff_card_eq_finrank_span, linearIndependent_iff_card_eq_finrank_span]
  have equivalence : Fintype.card Column = (matrix.map (fun entry => (entry : Field))).rank ↔
      Fintype.card Column = (matrix.map (fun entry => (entry : ℚ))).rank := by rw [rank_eq]
  have field_columns : (matrix.map (fun entry => (entry : Field))).col =
      fun column row => (matrix row column : Field) := by ext column row; rfl
  have rational_columns : (matrix.map (fun entry => (entry : ℚ))).col =
      fun column row => (matrix row column : ℚ) := by ext column row; rfl
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols,
    field_columns, rational_columns] at equivalence
  exact equivalence

theorem totallyUnimodular_cast_rayMatroid [Fintype Row] [Finite Column]
    (matrix : Matrix Row Column ℤ) (unimodular : matrix.IsTotallyUnimodular) :
    rayMatroid (Field := Field) (fun column row => (matrix row column : Field)) =
      rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ)) := by
  apply Matroid.ext_indep (by simp)
  intro subset _
  rw [rayMatroid_indep_iff, rayMatroid_indep_iff]
  let := Fintype.ofFinite subset
  exact totallyUnimodular_cast_linearIndependent_iff (Field := Field)
    (matrix.submatrix id ((↑) : subset → Column)) (unimodular.submatrix _ _)

theorem totallyUnimodular_representable [Fintype Row] [Finite Column]
    (matrix : Matrix Row Column ℤ) (unimodular : matrix.IsTotallyUnimodular) :
    (rayMatroid (Field := ℚ) (fun column row => (matrix row column : ℚ))).Representable Field := by
  rw [← totallyUnimodular_cast_rayMatroid (Field := Field) matrix unimodular]
  exact (Matroid.repOfRays (fun column row => (matrix row column : Field))).representable

end BondalThomsen
