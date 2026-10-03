module

public import BondalThomsen.Matroid.TURepresentationUniqueness
public import Mathlib.GroupTheory.Perm.Cycle.Basic

@[expose] public section

namespace BondalThomsen

open Equiv Equiv.Perm Finset

theorem permutation_eq_one_or_cycle {Index : Type*} [Finite Index]
    (cycle permutation : Equiv.Perm Index) (cyclic : cycle.IsCycle)
    (no_fixed : ∀ index, cycle index ≠ index)
    (choices : ∀ index, permutation index = index ∨ permutation index = cycle index) :
    permutation = 1 ∨ permutation = cycle := by
  classical
  by_cases all_fixed : ∀ index, permutation index = index
  · left
    ext index
    exact all_fixed index
  · right
    obtain ⟨start, moved⟩ := not_forall.mp all_fixed
    have start_shifted : permutation start = cycle start := (choices start).resolve_left moved
    have propagate (index : Index) (shifted : permutation index = cycle index) :
        permutation (cycle index) = cycle (cycle index) := by
      rcases choices (cycle index) with fixed | next
      · have same : permutation index = permutation (cycle index) := shifted.trans fixed.symm
        exact (no_fixed index (permutation.injective same).symm).elim
      · exact next
    have all_powers : ∀ power : ℕ, permutation ((cycle ^ power) start) =
        cycle ((cycle ^ power) start) := by
      intro power
      induction power with
      | zero => simpa using start_shifted
      | succ power induction =>
          simpa only [pow_succ', Equiv.Perm.mul_apply] using
            propagate ((cycle ^ power) start) induction
    ext index
    obtain ⟨power, power_eq⟩ :=
      (cyclic.sameCycle (no_fixed start) (no_fixed index)).exists_nat_pow_eq
    simpa only [power_eq] using all_powers power

def HasCycleSupport {Index Ring : Type*} [Zero Ring]
    (matrix : Matrix Index Index Ring) (cycle : Equiv.Perm Index) : Prop :=
  ∀ row column, row ≠ column → row ≠ cycle column → matrix row column = 0

theorem cycleSupport_permutation_product_zero {Index Ring : Type*}
    [Fintype Index] [DecidableEq Index] [CommRing Ring]
    (matrix : Matrix Index Index Ring) (cycle permutation : Equiv.Perm Index)
    (cyclic : cycle.IsCycle) (no_fixed : ∀ index, cycle index ≠ index)
    (support : HasCycleSupport matrix cycle)
    (not_identity : permutation ≠ 1) (not_cycle : permutation ≠ cycle) :
    (∏ index, matrix (permutation index) index) = 0 := by
  classical
  have not_choices : ¬∀ index, permutation index = index ∨ permutation index = cycle index := by
    intro choices
    rcases permutation_eq_one_or_cycle cycle permutation cyclic no_fixed choices with identity | same
    · exact not_identity identity
    · exact not_cycle same
  obtain ⟨index, neither⟩ := not_forall.mp not_choices
  have first : permutation index ≠ index := fun same => neither (Or.inl same)
  have second : permutation index ≠ cycle index := fun same => neither (Or.inr same)
  exact Finset.prod_eq_zero (Finset.mem_univ index) (support _ _ first second)

theorem cycleSupport_det_two_terms {Index Ring : Type*}
    [Fintype Index] [DecidableEq Index] [CommRing Ring]
    (matrix : Matrix Index Index Ring) (cycle : Equiv.Perm Index)
    (cyclic : cycle.IsCycle) (no_fixed : ∀ index, cycle index ≠ index)
    (support : HasCycleSupport matrix cycle) :
    matrix.det = (∏ index, matrix index index) +
      ((Equiv.Perm.sign cycle : ℤ) : Ring) * ∏ index, matrix (cycle index) index := by
  classical
  rw [Matrix.det_apply']
  have restrict_sum := Finset.sum_subset
    (show ({1, cycle} : Finset (Equiv.Perm Index)) ⊆ Finset.univ from Finset.subset_univ _)
    (f := fun permutation => ((Equiv.Perm.sign permutation : ℤ) : Ring) *
      ∏ index, matrix (permutation index) index) ?_
  · rw [← restrict_sum]
    rw [Finset.sum_pair cyclic.ne_one.symm]
    simp
  · intro permutation _ absent
    have not_identity : permutation ≠ 1 := by
      intro equality
      exact absent (by simp [equality])
    have not_cycle : permutation ≠ cycle := by
      intro equality
      exact absent (by simp [equality])
    rw [cycleSupport_permutation_product_zero matrix cycle permutation cyclic no_fixed
      support not_identity not_cycle, mul_zero]

theorem totallyUnimodular_cycle_matching_products_cancel {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (matrix : Matrix Index Index ℤ) (unimodular : matrix.IsTotallyUnimodular)
    (cycle : Equiv.Perm Index) (cyclic : cycle.IsCycle)
    (no_fixed : ∀ index, cycle index ≠ index) (support : HasCycleSupport matrix cycle)
    (diagonal_nonzero : ∀ index, matrix index index ≠ 0)
    (cycle_nonzero : ∀ index, matrix (cycle index) index ≠ 0) :
    (∏ index, matrix index index) +
      (Equiv.Perm.sign cycle : ℤ) * (∏ index, matrix (cycle index) index) = 0 := by
  have first_unit : IsUnit (∏ index, matrix index index) :=
    IsUnit.prod_univ_iff.mpr (fun index =>
      signedInteger_isUnit _ (unimodular.apply _ _) (diagonal_nonzero index))
  have cycle_unit : IsUnit (∏ index, matrix (cycle index) index) :=
    IsUnit.prod_univ_iff.mpr (fun index =>
      signedInteger_isUnit _ (unimodular.apply _ _) (cycle_nonzero index))
  have determinant_signed := (Matrix.isTotallyUnimodular_iff_fintype matrix).mp
    unimodular Index id id
  simp only [Matrix.submatrix_id_id] at determinant_signed
  rw [cycleSupport_det_two_terms matrix cycle cyclic no_fixed support] at determinant_signed
  exact unit_sum_eq_zero_of_signed first_unit
    ((Equiv.Perm.sign cycle).isUnit.mul cycle_unit) determinant_signed

theorem totallyUnimodular_cycle_edge_product {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (matrix : Matrix Index Index ℤ) (unimodular : matrix.IsTotallyUnimodular)
    (cycle : Equiv.Perm Index) (cyclic : cycle.IsCycle)
    (no_fixed : ∀ index, cycle index ≠ index) (support : HasCycleSupport matrix cycle)
    (diagonal_nonzero : ∀ index, matrix index index ≠ 0)
    (cycle_nonzero : ∀ index, matrix (cycle index) index ≠ 0) :
    (∏ index, matrix index index) * (∏ index, matrix (cycle index) index) =
      -(Equiv.Perm.sign cycle : ℤ) := by
  have cancellation := totallyUnimodular_cycle_matching_products_cancel matrix unimodular
    cycle cyclic no_fixed support diagonal_nonzero cycle_nonzero
  have cycle_unit : IsUnit (∏ index, matrix (cycle index) index) :=
    IsUnit.prod_univ_iff.mpr (fun index =>
      signedInteger_isUnit _ (unimodular.apply _ _) (cycle_nonzero index))
  have square : (∏ index, matrix (cycle index) index) *
      (∏ index, matrix (cycle index) index) = 1 := by
    rcases Int.isUnit_iff.mp cycle_unit with equality | equality <;> simp [equality]
  have relation : (∏ index, matrix index index) =
      -((Equiv.Perm.sign cycle : ℤ) * (∏ index, matrix (cycle index) index)) := by
    linarith
  rw [relation]
  calc
    _ = -(Equiv.Perm.sign cycle : ℤ) *
        ((∏ index, matrix (cycle index) index) * (∏ index, matrix (cycle index) index)) := by ring
    _ = _ := by rw [square, mul_one]

theorem tuRelativeSign_cycle_product {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (first second : Matrix Index Index ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (matching_support : ∀ row column, first row column = 0 ↔ second row column = 0)
    (cycle : Equiv.Perm Index) (cyclic : cycle.IsCycle)
    (no_fixed : ∀ index, cycle index ≠ index) (support : HasCycleSupport first cycle)
    (diagonal_nonzero : ∀ index, first index index ≠ 0)
    (cycle_nonzero : ∀ index, first (cycle index) index ≠ 0) :
    (∏ index, tuRelativeSign first second index index) *
      (∏ index, tuRelativeSign first second (cycle index) index) = 1 := by
  have second_support : HasCycleSupport second cycle := by
    intro row column not_diagonal not_cycle
    exact (matching_support row column).mp (support row column not_diagonal not_cycle)
  have second_diagonal : ∀ index, second index index ≠ 0 :=
    fun index zero => diagonal_nonzero index ((matching_support _ _).mpr zero)
  have second_cycle : ∀ index, second (cycle index) index ≠ 0 :=
    fun index zero => cycle_nonzero index ((matching_support _ _).mpr zero)
  have first_product := totallyUnimodular_cycle_edge_product first first_tu cycle
    cyclic no_fixed support diagonal_nonzero cycle_nonzero
  have second_product := totallyUnimodular_cycle_edge_product second second_tu cycle
    cyclic no_fixed second_support second_diagonal second_cycle
  simp only [tuRelativeSign, Finset.prod_mul_distrib]
  calc
    _ = ((∏ index, first index index) * (∏ index, first (cycle index) index)) *
        ((∏ index, second index index) * (∏ index, second (cycle index) index)) := by ring
    _ = _ := by rw [first_product, second_product]; simp

theorem tuRelativeSign_submatrix_cycle_product {Row Column Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (matching_support : ∀ row column, first row column = 0 ↔ second row column = 0)
    (rows : Index → Row) (columns : Index → Column)
    (cycle : Equiv.Perm Index) (cyclic : cycle.IsCycle)
    (no_fixed : ∀ index, cycle index ≠ index)
    (chordless : ∀ row column, row ≠ column → row ≠ cycle column →
      first (rows row) (columns column) = 0)
    (diagonal_nonzero : ∀ index, first (rows index) (columns index) ≠ 0)
    (cycle_nonzero : ∀ index, first (rows (cycle index)) (columns index) ≠ 0) :
    (∏ index, tuRelativeSign first second (rows index) (columns index)) *
      (∏ index, tuRelativeSign first second (rows (cycle index)) (columns index)) = 1 := by
  exact tuRelativeSign_cycle_product (first.submatrix rows columns) (second.submatrix rows columns)
    (first_tu.submatrix _ _) (second_tu.submatrix _ _)
    (fun row column => matching_support (rows row) (columns column))
    cycle cyclic no_fixed chordless diagonal_nonzero cycle_nonzero

theorem finRotate_no_fixed_of_two_le {length : ℕ} (lower : 2 ≤ length) :
    ∀ index : Fin length, finRotate length index ≠ index := by
  intro index
  apply Equiv.Perm.mem_support.mp
  rw [support_finRotate_of_le lower]
  exact Finset.mem_univ _

theorem tuRelativeSign_chordlessCycle_product {Row Column : Type*} {length : ℕ}
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (matching_support : ∀ row column, first row column = 0 ↔ second row column = 0)
    (lower : 2 ≤ length) (rows : Fin length → Row) (columns : Fin length → Column)
    (chordless : ∀ row column, row ≠ column → row ≠ finRotate length column →
      first (rows row) (columns column) = 0)
    (diagonal_nonzero : ∀ index, first (rows index) (columns index) ≠ 0)
    (cycle_nonzero : ∀ index, first (rows (finRotate length index)) (columns index) ≠ 0) :
    (∏ index, tuRelativeSign first second (rows index) (columns index)) *
      (∏ index, tuRelativeSign first second (rows (finRotate length index)) (columns index)) = 1 :=
  tuRelativeSign_submatrix_cycle_product first second first_tu second_tu matching_support
    rows columns (finRotate length) (isCycle_finRotate_of_le lower)
    (finRotate_no_fixed_of_two_le lower) chordless diagonal_nonzero cycle_nonzero

end BondalThomsen
