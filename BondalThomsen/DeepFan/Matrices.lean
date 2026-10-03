module

public import BondalThomsen.DeepFan.Coordinates
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

@[expose] public section

namespace BondalThomsen

open Finset Matrix

def DeepMatrix {Row Column : Type*} [Fintype Row] (matrix : Matrix Row Column ℤ) : Prop :=
  (∀ column, DeepCoordinates (fun row => matrix row column)) ∧
  (∀ row column, -1 ≤ matrix row column)

def PositiveCombination {Row Column : Type*} [Fintype Column]
    (matrix : Matrix Row Column ℤ) (weights : Column → ℝ) : Prop :=
  (∀ column, 0 < weights column) ∧
  (∀ row, 0 < ∑ column, (matrix row column : ℝ) * weights column)

theorem DeepMatrix.entry_trichotomy {Row Column : Type*} [Fintype Row]
    {matrix : Matrix Row Column ℤ} (deep : DeepMatrix matrix) (row : Row) (column : Column) :
    matrix row column = -1 ∨ matrix row column = 0 ∨ matrix row column = 1 := by
  have upper := (deep.1 column).coordinate_le_one row
  have lower := deep.2 row column
  omega

theorem positiveCombination_row_has_one {Row Column : Type*} [Fintype Row] [Fintype Column]
    {matrix : Matrix Row Column ℤ} {weights : Column → ℝ} (deep : DeepMatrix matrix)
    (positive : PositiveCombination matrix weights) (row : Row) :
    ∃ column, matrix row column = 1 := by
  by_contra contrary
  have nonpositive : ∀ column, matrix row column ≤ 0 := by
    intro column
    have upper := (deep.1 column).coordinate_le_one row
    have not_one : matrix row column ≠ 1 := fun equality => contrary ⟨column, equality⟩
    omega
  have bound : ∑ column, (matrix row column : ℝ) * weights column ≤ 0 := by
    apply sum_nonpos
    intro column _
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast nonpositive column)
      (positive.1 column).le
  exact (not_lt_of_ge bound) (positive.2 row)

theorem positiveCombination_matching {Index : Type*} [Fintype Index]
    {matrix : Matrix Index Index ℤ} {weights : Index → ℝ} (deep : DeepMatrix matrix)
    (positive : PositiveCombination matrix weights) :
    ∃ matching : Equiv.Perm Index, ∀ row, matrix row (matching row) = 1 := by
  classical
  choose matching matching_one using positiveCombination_row_has_one deep positive
  have injective : Function.Injective matching := by
    intro first second same
    have first_one := matching_one first
    have second_one := matching_one second
    rw [← same] at second_one
    exact (deep.1 (matching first)).unique_positive (by omega) (by omega)
  exact ⟨Equiv.ofBijective matching ((Finite.injective_iff_bijective).mp injective), matching_one⟩

theorem negative_entry_decreases_weight {Index : Type*} [Fintype Index] [DecidableEq Index]
    {matrix : Matrix Index Index ℤ} {weights : Index → ℝ}
    (deep : DeepMatrix matrix) (positive : PositiveCombination matrix weights)
    (diagonal : ∀ index, matrix index index = 1) {row column : Index}
    (negative : matrix row column = -1) : weights column < weights row := by
  have different : column ≠ row := by
    intro same
    subst column
    rw [diagonal row] at negative
    omega
  have off_diagonal : ∀ index, index ≠ row → matrix row index ≤ 0 := by
    intro index distinct
    have upper := (deep.1 index).coordinate_le_one row
    by_contra contrary
    have same := (deep.1 index).unique_positive (first := row) (second := index) (by omega)
      (show 0 < matrix index index by rw [diagonal]; omega)
    exact distinct same.symm
  have remainder : ∑ index ∈ univ.erase row, (matrix row index : ℝ) * weights index ≤
      (matrix row column : ℝ) * weights column := by
    exact sum_le_sum_of_subset_of_nonpos
      (show ({column} : Finset Index) ⊆ univ.erase row by simp [different])
      (fun index member _ => mul_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast off_diagonal index (mem_erase.mp member).1)
        (positive.1 index).le)
      |>.trans_eq (by simp)
  have split := sum_erase_add univ (fun index => (matrix row index : ℝ) * weights index)
    (mem_univ row)
  have strict := positive.2 row
  rw [diagonal row] at split
  rw [negative] at remainder
  norm_num at split remainder
  linarith

theorem deepMatrix_det_eq_one {Index : Type*} [Fintype Index] [DecidableEq Index]
    {matrix : Matrix Index Index ℤ} {weights : Index → ℝ}
    (deep : DeepMatrix matrix) (positive : PositiveCombination matrix weights)
    (diagonal : ∀ index, matrix index index = 1) : matrix.det = 1 := by
  have permutation_product_zero : ∀ permutation : Equiv.Perm Index,
      permutation ≠ 1 → ∏ index, matrix (permutation index) index = 0 := by
    intro permutation nonidentity
    by_contra nonzero
    have entries := prod_ne_zero_iff.mp nonzero
    have comparison : ∀ index, weights index ≤ weights (permutation index) := by
      intro index
      by_cases fixed : permutation index = index
      · rw [fixed]
      · have not_one : matrix (permutation index) index ≠ 1 := by
          intro one
          exact fixed ((deep.1 index).unique_positive (by omega)
            (show 0 < matrix index index by rw [diagonal]; omega))
        have negative : matrix (permutation index) index = -1 := by
          have cases := deep.entry_trichotomy (permutation index) index
          have not_zero := entries index (mem_univ index)
          omega
        exact (negative_entry_decreases_weight deep positive diagonal negative).le
    have moved : ∃ index, permutation index ≠ index := by
      by_contra contrary
      apply nonidentity
      ext index
      by_contra moved
      exact contrary ⟨index, moved⟩
    obtain ⟨index, moved⟩ := moved
    have not_one : matrix (permutation index) index ≠ 1 := by
      intro one
      exact moved ((deep.1 index).unique_positive (by omega)
        (show 0 < matrix index index by rw [diagonal]; omega))
    have negative : matrix (permutation index) index = -1 := by
      have cases := deep.entry_trichotomy (permutation index) index
      have not_zero := entries index (mem_univ index)
      omega
    have strict_sum := sum_lt_sum (fun index _ => comparison index)
      ⟨index, mem_univ index, negative_entry_decreases_weight deep positive diagonal negative⟩
    rw [Equiv.sum_comp permutation weights] at strict_sum
    exact (lt_irrefl _) strict_sum
  rw [det_apply', sum_eq_single (1 : Equiv.Perm Index)]
  · simp [diagonal]
  · intro permutation _ nonidentity
    rw [permutation_product_zero permutation nonidentity, mul_zero]
  · simp

theorem deepMatrix_det_eq_one_or_neg_one {Index : Type*} [Fintype Index] [DecidableEq Index]
    {matrix : Matrix Index Index ℤ} {weights : Index → ℝ}
    (deep : DeepMatrix matrix) (positive : PositiveCombination matrix weights) :
    matrix.det = 1 ∨ matrix.det = -1 := by
  obtain ⟨matching, matched⟩ := positiveCombination_matching deep positive
  let normalized := matrix.submatrix id matching
  let normalized_weights := fun index => weights (matching index)
  have normalized_deep : DeepMatrix normalized := by
    exact ⟨fun column => deep.1 (matching column), fun row column => deep.2 row (matching column)⟩
  have normalized_positive : PositiveCombination normalized normalized_weights := by
    refine ⟨fun column => positive.1 (matching column), fun row => ?_⟩
    change 0 < ∑ index, (matrix row (matching index) : ℝ) * weights (matching index)
    rw [Equiv.sum_comp matching (fun index => (matrix row index : ℝ) * weights index)]
    exact positive.2 row
  have determinant := deepMatrix_det_eq_one normalized_deep normalized_positive matched
  change (matrix.submatrix id matching).det = 1 at determinant
  rw [Matrix.det_permute'] at determinant
  have sign := Int.units_eq_one_or (Equiv.Perm.sign matching)
  rcases sign with sign | sign
  · simp [sign] at determinant
    exact Or.inl determinant
  · simp [sign] at determinant
    exact Or.inr (by omega)

end BondalThomsen
