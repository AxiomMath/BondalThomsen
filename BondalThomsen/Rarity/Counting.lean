module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section

namespace BondalThomsen

open Finset

def markedTreeCount (internal : ℕ) : ℕ := 3 ^ internal * catalan internal

theorem catalan_le_four_pow (internal : ℕ) : catalan internal ≤ 4 ^ internal := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow internal)

theorem markedTreeCount_le (internal : ℕ) : markedTreeCount internal ≤ 12 ^ internal := by
  calc
    markedTreeCount internal ≤ 3 ^ internal * 4 ^ internal :=
      Nat.mul_le_mul_left _ (catalan_le_four_pow internal)
    _ = 12 ^ internal := by rw [← mul_pow]; norm_num

def signedTreeCount (elements : ℕ) : ℕ := 2 ^ elements * markedTreeCount (elements - 1)

theorem signedTreeCount_le (elements : ℕ) : signedTreeCount elements ≤ 24 ^ elements := by
  calc
    signedTreeCount elements ≤ 2 ^ elements * 12 ^ (elements - 1) :=
      Nat.mul_le_mul_left _ (markedTreeCount_le _)
    _ ≤ 2 ^ elements * 12 ^ elements :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))
    _ = 24 ^ elements := by rw [← mul_pow]; norm_num

theorem successor_le_two_pow (number : ℕ) : number + 1 ≤ 2 ^ number := by
  exact Nat.succ_le_of_lt Nat.lt_two_pow_self

theorem signedTreeCount_sum_le (dimension : ℕ) :
    ∑ elements ∈ range (4 * dimension + 1), signedTreeCount elements ≤
      48 ^ (4 * dimension) := by
  calc
    ∑ elements ∈ range (4 * dimension + 1), signedTreeCount elements ≤
        ∑ _elements ∈ range (4 * dimension + 1), 24 ^ (4 * dimension) := by
      apply sum_le_sum
      intro elements member
      exact (signedTreeCount_le elements).trans
        (Nat.pow_le_pow_right (by omega) (by have := mem_range.mp member; omega))
    _ = (4 * dimension + 1) * 24 ^ (4 * dimension) := by simp
    _ ≤ 2 ^ (4 * dimension) * 24 ^ (4 * dimension) :=
      Nat.mul_le_mul_right _ (successor_le_two_pow (4 * dimension))
    _ = 48 ^ (4 * dimension) := by rw [← mul_pow]; norm_num

def fixedWeightRows (columns ones : ℕ) : Finset (Finset (Fin columns)) :=
  univ.powersetCard ones

theorem fixedWeightRows_card (columns ones : ℕ) :
    (fixedWeightRows columns ones).card = columns.choose ones := by
  simp [fixedWeightRows]

abbrev FixedWeightMatrix (rows columns ones : ℕ) :=
  Fin rows → ↥(fixedWeightRows columns ones)

theorem fixedWeightMatrix_card (rows columns ones : ℕ) :
    Fintype.card (FixedWeightMatrix rows columns ones) = (columns.choose ones) ^ rows := by
  simp [FixedWeightMatrix, fixedWeightRows_card]

theorem fixedWeightMatrix_row_card {rows columns ones : ℕ}
    (matrix : FixedWeightMatrix rows columns ones) (row : Fin rows) :
    (matrix row).val.card = ones :=
  (mem_powersetCard.mp (matrix row).property).2

theorem finite_fiber_count {Source Target : Type*} [Fintype Source] [Fintype Target]
    [DecidableEq Target]
    (classify : Source → Target) (multiplicity : ℕ)
    (fiber_bound : ∀ target, (univ.filter (fun source => classify source = target)).card ≤
      multiplicity) : Fintype.card Source ≤ multiplicity * Fintype.card Target := by
  classical
  exact card_le_mul_card_image_of_maps_to
    (s := univ) (t := univ) (f := classify) (fun _ _ => mem_univ _) multiplicity
    (fun target _ => fiber_bound target)

theorem projective_bundle_family_count {Classes : Type*} [Fintype Classes] [DecidableEq Classes]
    (rows columns ones : ℕ) (classify : FixedWeightMatrix rows columns ones → Classes)
    (fiber_bound : ∀ target,
      (univ.filter (fun matrix => classify matrix = target)).card ≤
        rows.factorial * (columns + 1).factorial) :
    (columns.choose ones) ^ rows ≤
      rows.factorial * (columns + 1).factorial * Fintype.card Classes := by
  rw [← fixedWeightMatrix_card]
  exact finite_fiber_count classify _ fiber_bound

end BondalThomsen
