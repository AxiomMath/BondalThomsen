module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic

@[expose] public section

namespace Matrix

open Module

variable {Row Column Field : Type*} [_root_.Field Field]

theorem rank_eq_card_iff_det_ne_zero [Fintype Column] [DecidableEq Column]
    (matrix : Matrix Column Column Field) :
    matrix.rank = Fintype.card Column ↔ matrix.det ≠ 0 := by
  constructor
  · intro rank_full determinant_zero
    have range_top : LinearMap.range matrix.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_pi (R := Field)]
      exact rank_full
    have surjective : Function.Surjective matrix.mulVecLin := LinearMap.range_eq_top.mp range_top
    have injective : Function.Injective matrix.mulVecLin :=
      LinearMap.injective_iff_surjective.mpr surjective
    obtain ⟨vector, nonzero, image_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr determinant_zero
    apply nonzero
    apply injective
    rw [matrix.mulVecLin.map_zero, Matrix.mulVecLin_apply, image_zero]
  · exact Matrix.rank_of_det_ne_zero

theorem exists_submatrix_id_rank_eq [Finite Row] [Fintype Column] {size : ℕ}
    (matrix : Matrix Row Column Field) (rank_bound : size ≤ matrix.rank) :
    ∃ selection : Fin size → Column, (matrix.submatrix id selection).rank = size := by
  classical
  let := Fintype.ofFinite Row
  obtain ⟨Index, selected, selected_injective, span_eq, independent⟩ :=
    exists_linearIndependent' Field matrix.col
  have : Finite Index := Finite.of_injective selected selected_injective
  cases nonempty_fintype Index
  have selected_card : Fintype.card Index = matrix.rank := by
    have span_rank : finrank Field (Submodule.span Field (Set.range (matrix.col ∘ selected))) =
        Fintype.card Index := finrank_span_eq_card independent
    rw [span_eq, ← rank_eq_finrank_span_cols] at span_rank
    exact span_rank.symm
  have size_le : size ≤ Fintype.card Index := selected_card ▸ rank_bound
  obtain ⟨inclusion⟩ : Nonempty (Fin size ↪ Index) :=
    Function.Embedding.nonempty_of_card_le (by simpa using size_le)
  refine ⟨selected ∘ inclusion, ?_⟩
  have restricted_independent : LinearIndependent Field
      (matrix.col ∘ (selected ∘ ⇑inclusion)) := by
    have restricted := independent.comp inclusion inclusion.injective
    simpa only [Function.comp_assoc] using restricted
  have columns_eq : (matrix.submatrix id (selected ∘ inclusion)).col =
      matrix.col ∘ (selected ∘ inclusion) := by
    funext column row
    rfl
  rw [rank_eq_finrank_span_cols, columns_eq, finrank_span_eq_card restricted_independent,
    Fintype.card_fin]

theorem exists_submatrix_det_ne_zero_of_le_rank [Finite Row] [Fintype Column] {size : ℕ}
    (matrix : Matrix Row Column Field) (rank_bound : size ≤ matrix.rank) :
    ∃ rows : Fin size → Row, ∃ columns : Fin size → Column,
      (matrix.submatrix rows columns).det ≠ 0 := by
  classical
  let := Fintype.ofFinite Row
  obtain ⟨columns, columns_rank⟩ := exists_submatrix_id_rank_eq matrix rank_bound
  let selected : Matrix Row (Fin size) Field := matrix.submatrix id columns
  have transpose_rank : selected.transpose.rank = size := by
    rw [rank_transpose]
    exact columns_rank
  obtain ⟨rows, rows_rank⟩ := exists_submatrix_id_rank_eq selected.transpose transpose_rank.ge
  have square_eq : selected.transpose.submatrix id rows =
      (matrix.submatrix rows columns).transpose := rfl
  rw [square_eq] at rows_rank
  refine ⟨rows, columns, ?_⟩
  have determinant_nonzero := (rank_eq_card_iff_det_ne_zero
    (matrix.submatrix rows columns).transpose).mp (by rw [rows_rank, Fintype.card_fin])
  simpa only [det_transpose] using determinant_nonzero

theorem le_rank_of_submatrix_det_ne_zero [Fintype Row] [Fintype Column] {size : ℕ}
    (matrix : Matrix Row Column Field) (rows : Fin size → Row) (columns : Fin size → Column)
    (nonzero : (matrix.submatrix rows columns).det ≠ 0) : size ≤ matrix.rank := by
  have full_rank : (matrix.submatrix rows columns).rank = size := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero nonzero
  exact full_rank ▸ rank_submatrix_le matrix rows columns

end Matrix
