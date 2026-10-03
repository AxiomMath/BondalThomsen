module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic

@[expose] public section

namespace BondalThomsen

theorem rational_floor_eq_of_close {value nearby : ℚ}
    (close : |value - nearby| < min (Int.fract value) (1 - Int.fract value)) :
    ⌊nearby⌋ = ⌊value⌋ := by
  have lower : value - nearby < Int.fract value :=
    (le_abs_self _).trans_lt (close.trans_le (min_le_left _ _))
  have upper : nearby - value < 1 - Int.fract value := by
    have bound : nearby - value ≤ |value - nearby| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact bound.trans_lt (close.trans_le (min_le_right _ _))
  have decomposition := Int.floor_add_fract value
  exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩

theorem exists_rational_floor_step (value velocity : ℚ) :
    ∃ radius : ℚ, 0 < radius ∧ ∀ parameter : ℚ, 0 < parameter → parameter < radius →
      ⌊value + parameter * velocity⌋ =
        ⌊value⌋ + if Int.fract value = 0 ∧ velocity < 0 then -1 else 0 := by
  have denominator_positive : 0 < |velocity| + 1 := by positivity
  by_cases integral : Int.fract value = 0
  · have value_eq : value = (⌊value⌋ : ℚ) := by
      have decomposition := Int.floor_add_fract value
      rw [integral, add_zero] at decomposition
      exact decomposition.symm
    refine ⟨1 / (|velocity| + 1), by positivity, ?_⟩
    intro parameter parameter_positive parameter_small
    have bounded : parameter * (|velocity| + 1) < 1 :=
      (lt_div_iff₀ denominator_positive).mp parameter_small
    have absolute_bound : |parameter * velocity| < 1 := by
      rw [abs_mul, abs_of_pos parameter_positive]
      nlinarith
    have magnitude := abs_lt.mp absolute_bound
    by_cases negative : velocity < 0
    · have motion_negative : parameter * velocity < 0 :=
        mul_neg_of_pos_of_neg parameter_positive negative
      rw [ite_eq_left ⟨integral, negative⟩]
      apply Int.floor_eq_iff.mpr
      rw [Int.cast_add, Int.cast_neg, Int.cast_one]
      constructor <;> linarith
    · have motion_nonnegative : 0 ≤ parameter * velocity :=
        mul_nonneg parameter_positive.le (le_of_not_gt negative)
      rw [ite_eq_right (by simp [negative]), add_zero]
      exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  · have fraction_positive : 0 < Int.fract value :=
      lt_of_le_of_ne (Int.fract_nonneg value) (Ne.symm integral)
    have margin_positive : 0 < min (Int.fract value) (1 - Int.fract value) :=
      lt_min fraction_positive (sub_pos.mpr (Int.fract_lt_one value))
    refine ⟨min (Int.fract value) (1 - Int.fract value) / (|velocity| + 1),
      div_pos margin_positive denominator_positive, ?_⟩
    intro parameter parameter_positive parameter_small
    rw [ite_eq_right (by simp [integral]), add_zero]
    apply rational_floor_eq_of_close
    have bounded := (lt_div_iff₀ denominator_positive).mp parameter_small
    have distance : |value - (value + parameter * velocity)| = parameter * |velocity| := by
      rw [sub_add_cancel_left, abs_neg, abs_mul, abs_of_pos parameter_positive]
    rw [distance]
    nlinarith

theorem exists_simultaneous_rational_floor_step {Ray : Type*}
    (rays : Finset Ray) (values velocities : Ray → ℚ) :
    ∃ radius : ℚ, 0 < radius ∧ ∀ parameter : ℚ, 0 < parameter → parameter < radius →
      ∀ ray ∈ rays, ⌊values ray + parameter * velocities ray⌋ =
        ⌊values ray⌋ + if Int.fract (values ray) = 0 ∧ velocities ray < 0 then -1 else 0 := by
  classical
  induction rays using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert ray rays absent induction =>
    obtain ⟨first_radius, first_positive, first_step⟩ :=
      exists_rational_floor_step (values ray) (velocities ray)
    obtain ⟨remaining_radius, remaining_positive, remaining_step⟩ := induction
    refine ⟨min first_radius remaining_radius, lt_min first_positive remaining_positive, ?_⟩
    intro parameter parameter_positive parameter_small chosen member
    rcases Finset.mem_insert.mp member with rfl | remaining_member
    · exact first_step parameter parameter_positive
        (parameter_small.trans_le (min_le_left _ _))
    · exact remaining_step parameter parameter_positive
        (parameter_small.trans_le (min_le_right _ _)) chosen remaining_member

theorem exists_prescribed_rational_floor_drop {Ray : Type*} [Fintype Ray]
    (values velocities : Ray → ℚ) (prescribed : Set Ray)
    [DecidablePred (fun ray => ray ∈ prescribed)]
    (prescribed_integral : ∀ ray ∈ prescribed, Int.fract (values ray) = 0)
    (prescribed_velocity : ∀ ray ∈ prescribed, velocities ray = -1)
    (other_velocity : ∀ ray ∉ prescribed, Int.fract (values ray) = 0 → 0 ≤ velocities ray) :
    ∃ parameter : ℚ, 0 < parameter ∧ ∀ ray,
      ⌊values ray + parameter * velocities ray⌋ - ⌊values ray⌋ =
        if ray ∈ prescribed then -1 else 0 := by
  classical
  obtain ⟨radius, radius_positive, step⟩ :=
    exists_simultaneous_rational_floor_step Finset.univ values velocities
  refine ⟨radius / 2, by positivity, ?_⟩
  intro ray
  have formula := step (radius / 2) (by positivity) (by linarith) ray (Finset.mem_univ _)
  by_cases member : ray ∈ prescribed
  · rw [prescribed_velocity ray member,
      ite_eq_left ⟨prescribed_integral ray member, by norm_num⟩] at formula
    rw [ite_eq_left member, prescribed_velocity ray member, formula]
    omega
  · have no_drop : ¬ (Int.fract (values ray) = 0 ∧ velocities ray < 0) := by
      rintro ⟨integral, negative⟩
      exact (not_lt_of_ge (other_velocity ray member integral)) negative
    rw [ite_eq_right no_drop, add_zero] at formula
    rw [ite_eq_right member, formula, sub_self]

end BondalThomsen
