module

public import BondalThomsen.DeepFan.Coordinates
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace BondalThomsen

open Finset

noncomputable def primitiveIntersection {Left Right : Type*} [Fintype Left] [Fintype Right]
    (left_values : Left → ℝ) (right_values : Right → ℝ) (coefficients : Right → ℕ) : ℤ :=
  -(∑ index, ⌊left_values index⌋) + ∑ index, (coefficients index : ℤ) * ⌊right_values index⌋

theorem primitiveIntersection_eq_fract {Left Right : Type*} [Fintype Left] [Fintype Right]
    (left_values : Left → ℝ) (right_values : Right → ℝ) (coefficients : Right → ℕ)
    (relation : ∑ index, left_values index = ∑ index, (coefficients index : ℝ) * right_values index) :
    (primitiveIntersection left_values right_values coefficients : ℝ) =
      ∑ index, Int.fract (left_values index) -
        ∑ index, (coefficients index : ℝ) * Int.fract (right_values index) := by
  simp only [primitiveIntersection, Int.cast_add, Int.cast_neg, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast, Int.fract, mul_sub, sum_sub_distrib]
  linarith

theorem primitiveIntersection_nonnegative {Left Right : Type*} [Fintype Left] [Fintype Right]
    (left_values : Left → ℝ) (right_values : Right → ℝ) (coefficients : Right → ℕ)
    (relation : ∑ index, left_values index = ∑ index, (coefficients index : ℝ) * right_values index)
    (small_right : ∑ index, coefficients index ≤ 1) :
    0 ≤ primitiveIntersection left_values right_values coefficients := by
  have left_nonnegative : 0 ≤ ∑ index, Int.fract (left_values index) :=
    sum_nonneg (fun index _ => Int.fract_nonneg _)
  have right_lt_one : ∑ index, (coefficients index : ℝ) * Int.fract (right_values index) < 1 := by
    by_cases all_zero : ∀ index, coefficients index = 0
    · simp [all_zero]
    · push Not at all_zero
      obtain ⟨chosen, nonzero⟩ := all_zero
      have comparison : ∀ index, (coefficients index : ℝ) * Int.fract (right_values index) ≤
          coefficients index := by
        intro index
        nlinarith [Int.fract_lt_one (right_values index),
          show (0 : ℝ) ≤ coefficients index by positivity]
      have strict : (coefficients chosen : ℝ) * Int.fract (right_values chosen) <
          coefficients chosen := by
        exact mul_lt_of_lt_one_right (by exact_mod_cast Nat.pos_of_ne_zero nonzero)
          (Int.fract_lt_one _)
      have strict_sum := sum_lt_sum (fun index _ => comparison index)
        ⟨chosen, mem_univ chosen, strict⟩
      have bound : (∑ index, (coefficients index : ℝ)) ≤ 1 := by exact_mod_cast small_right
      exact strict_sum.trans_le bound
  have intersection_gt : (-1 : ℝ) < primitiveIntersection left_values right_values coefficients := by
    rw [primitiveIntersection_eq_fract left_values right_values coefficients relation]
    linarith
  have integer_gt : (-1 : ℤ) < primitiveIntersection left_values right_values coefficients := by
    exact_mod_cast intersection_gt
  omega

theorem bad_relation_parameters {Right : Type*} [Fintype Right]
    (coefficients : Right → ℕ) (large_right : 2 ≤ ∑ index, coefficients index) :
    ∃ parameters : Right → ℚ,
      (∀ index, 0 < parameters index ∧ parameters index < 1) ∧
      ∑ index, (coefficients index : ℚ) * parameters index = 1 := by
  let total : ℚ := ∑ index, (coefficients index : ℚ)
  have large : 2 ≤ total := by
    dsimp [total]
    exact_mod_cast large_right
  refine ⟨fun _ => 1 / total, fun _ => ⟨by positivity, ?_⟩, ?_⟩
  · exact (div_lt_one (by positivity)).mpr (by linarith)
  · rw [← sum_mul]
    change total * (1 / total) = 1
    field_simp

theorem primitive_span_sum_nonpositive {Index : Type*} [Fintype Index]
    (coefficients : Index → ℝ) (degree : ℝ) (_degree_positive : 0 < degree)
    (degree_small : degree < Fintype.card Index)
    (inequalities : ∀ index, (∑ other, coefficients other) - degree * coefficients index ≤ 0) :
    ∑ index, coefficients index ≤ 0 := by
  by_contra contrary
  have positive : 0 < ∑ index, coefficients index := by linarith
  have summed := sum_le_sum (fun index (_ : index ∈ (univ : Finset Index)) => inequalities index)
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum] at summed
  nlinarith

end BondalThomsen
