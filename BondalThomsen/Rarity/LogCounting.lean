module

public import BondalThomsen.Rarity.Counting
public import BondalThomsen.Ports.BinomialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace BondalThomsen

open Real

theorem pow_div_le_choose (columns ones : ℕ) (positive : 0 < ones)
    (ones_le : ones ≤ columns) :
    ((columns : ℝ) / ones) ^ ones ≤ (columns.choose ones : ℝ) := by
  have ratio := choose_ratio_le_pow ones columns ones ones_le le_rfl
  have ones_positive : (0 : ℝ) < ones := by exact_mod_cast positive
  have columns_positive : (0 : ℝ) < columns := by exact_mod_cast positive.trans_le ones_le
  have choose_positive : (0 : ℝ) < columns.choose ones := by
    exact_mod_cast Nat.choose_pos ones_le
  simp only [Nat.choose_self, Nat.cast_one] at ratio
  rw [div_pow] at ratio ⊢
  apply (div_le_iff₀ (pow_pos ones_positive _)).mpr
  have multiplied := (div_le_iff₀ choose_positive).mp ratio
  rw [div_mul_eq_mul_div] at multiplied
  have rearranged := (le_div_iff₀ (pow_pos columns_positive _)).mp multiplied
  nlinarith

theorem log_choose_lower (columns ones : ℕ) (positive : 0 < ones)
    (ones_le : ones ≤ columns) :
    ones * (log columns - log ones) ≤ log (columns.choose ones : ℝ) := by
  have ones_positive : (0 : ℝ) < ones := by exact_mod_cast positive
  have columns_positive : (0 : ℝ) < columns := by exact_mod_cast positive.trans_le ones_le
  have bound := log_le_log (pow_pos (div_pos columns_positive ones_positive) ones)
    (pow_div_le_choose columns ones positive ones_le)
  simpa only [log_pow, log_div columns_positive.ne' ones_positive.ne'] using bound

theorem log_factorial_upper (number : ℕ) :
    log (number.factorial : ℝ) ≤ number * log number := by
  have positive : (0 : ℝ) < number.factorial := by exact_mod_cast Nat.factorial_pos number
  have bound : (number.factorial : ℝ) ≤ (number : ℝ) ^ number := by
    exact_mod_cast Nat.factorial_le_pow number
  simpa only [log_pow] using log_le_log positive bound

theorem projective_bundle_family_log_lower {Classes : Type*} [Fintype Classes]
    [DecidableEq Classes] (rows columns ones : ℕ) (positive : 0 < ones)
    (ones_le : ones ≤ columns)
    (classify : FixedWeightMatrix rows columns ones → Classes)
    (fiber_bound : ∀ target,
      (Finset.univ.filter (fun matrix => classify matrix = target)).card ≤
        rows.factorial * (columns + 1).factorial) :
    (rows * ones : ℝ) * (log columns - log ones) - rows * log rows -
      (columns + 1) * log (columns + 1) ≤ log (Fintype.card Classes : ℝ) := by
  have choose_positive : (0 : ℝ) < columns.choose ones := by
    exact_mod_cast Nat.choose_pos ones_le
  have rows_factorial_positive : (0 : ℝ) < rows.factorial := by
    exact_mod_cast Nat.factorial_pos rows
  have columns_factorial_positive : (0 : ℝ) < (columns + 1).factorial := by
    exact_mod_cast Nat.factorial_pos (columns + 1)
  have counting : (columns.choose ones : ℝ) ^ rows ≤
      rows.factorial * (columns + 1).factorial * (Fintype.card Classes : ℝ) := by
    exact_mod_cast projective_bundle_family_count rows columns ones classify fiber_bound
  have classes_positive : (0 : ℝ) < Fintype.card Classes := by
    have product_positive := (pow_pos choose_positive rows).trans_le counting
    nlinarith [mul_pos rows_factorial_positive columns_factorial_positive]
  have logarithmic := log_le_log (pow_pos choose_positive rows) counting
  rw [log_pow, log_mul (mul_pos rows_factorial_positive columns_factorial_positive).ne'
    classes_positive.ne', log_mul rows_factorial_positive.ne' columns_factorial_positive.ne']
    at logarithmic
  have binomial := mul_le_mul_of_nonneg_left (log_choose_lower columns ones positive ones_le)
    (Nat.cast_nonneg rows : (0 : ℝ) ≤ rows)
  have first_factorial := log_factorial_upper rows
  have second_factorial := log_factorial_upper (columns + 1)
  push_cast at second_factorial
  nlinarith

end BondalThomsen
