module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic

@[expose] public section

namespace BondalThomsen

theorem descFactorial_ratio_le (smaller larger length : ℕ)
    (ordered : smaller ≤ larger) (length_le : length ≤ smaller) :
    (smaller.descFactorial length : ℝ) / (larger.descFactorial length : ℝ) ≤
      ((smaller : ℝ) / larger) ^ length := by
  induction length with
  | zero => norm_num [Nat.descFactorial]
  | succ length induction_hypothesis =>
    simp_all +decide only [Nat.descFactorial_succ, Nat.cast_mul]
    rw [pow_succ']
    refine le_trans ?_
      (mul_le_mul_of_nonneg_left
        (induction_hypothesis (Nat.le_of_succ_le length_le)) (by positivity))
    rw [mul_div_mul_comm]
    exact mul_le_mul_of_nonneg_right
      (by
        rw [div_le_div_iff₀] <;> norm_cast <;>
          nlinarith [Nat.sub_add_cancel (Nat.le_of_succ_le length_le),
            Nat.sub_add_cancel (by omega : length ≤ larger)])
      (by positivity)

theorem choose_ratio_le_pow (smaller larger length : ℕ)
    (ordered : smaller ≤ larger) (length_le : length ≤ smaller) :
    (smaller.choose length : ℝ) / (larger.choose length : ℝ) ≤
      ((smaller : ℝ) / larger) ^ length := by
  have descending_bound := descFactorial_ratio_le smaller larger length ordered length_le
  have factorial_positive : (0 : ℝ) < (length.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos length
  have smaller_choose : (smaller.choose length : ℝ) =
      (smaller.descFactorial length : ℝ) / (length.factorial : ℝ) := by
    have equality := Nat.descFactorial_eq_factorial_mul_choose smaller length
    have cast_equality : (smaller.descFactorial length : ℝ) =
        (length.factorial : ℝ) * (smaller.choose length : ℝ) := by
      exact_mod_cast equality
    rw [cast_equality]
    field_simp [factorial_positive.ne']
  have larger_choose : (larger.choose length : ℝ) =
      (larger.descFactorial length : ℝ) / (length.factorial : ℝ) := by
    have equality := Nat.descFactorial_eq_factorial_mul_choose larger length
    have cast_equality : (larger.descFactorial length : ℝ) =
        (length.factorial : ℝ) * (larger.choose length : ℝ) := by
      exact_mod_cast equality
    rw [cast_equality]
    field_simp [factorial_positive.ne']
  rw [smaller_choose, larger_choose]
  field_simp [factorial_positive.ne']
  exact descending_bound

end BondalThomsen
