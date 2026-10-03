module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

@[expose] public section

namespace BondalThomsen

open Filter Real
open scoped Topology

noncomputable def rarityExponent (constant argument : ℝ) : ℝ :=
  -argument * log argument + 2 * argument * log (log argument) + 2 * constant * argument

theorem rarityExponent_tendsto_atBot (constant : ℝ) :
    Tendsto (rarityExponent constant) atTop atBot := by
  have logarithmic_ratio : Tendsto (fun argument : ℝ => log (log argument) / log argument)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have constant_ratio : Tendsto (fun argument : ℝ => constant / log argument) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop constant
  have normalized : Tendsto (fun argument : ℝ =>
      -1 + 2 * (log (log argument) / log argument) + 2 * (constant / log argument))
      atTop (𝓝 (-1)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul logarithmic_ratio)).add
      (tendsto_const_nhds.mul constant_ratio)
  have scale : Tendsto (fun argument : ℝ => argument * log argument) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have product := normalized.neg_mul_atTop (by norm_num : (-1 : ℝ) < 0) scale
  apply product.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with argument positive
  unfold rarityExponent
  field_simp

theorem rarity_bound_tendsto_zero (constant : ℝ) :
    Tendsto (fun argument : ℝ => exp (rarityExponent constant argument)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (rarityExponent_tendsto_atBot constant)

theorem asymptotic_rarity_of_bounds (good total : ℕ → ℝ) (constant : ℝ)
    (good_nonnegative : ∀ number, 0 ≤ good number)
    (upper : ∀ᶠ number in atTop, good number ≤ exp (constant * number))
    (lower : ∀ᶠ (number : ℕ) in atTop,
      exp ((number : ℝ) * log number - 2 * number * log (log number) - constant * number) ≤
        total number) :
    Tendsto (fun number => good number / total number) atTop (𝓝 0) := by
  have ratio_bound : ∀ᶠ number in atTop,
      good number / total number ≤ exp (rarityExponent constant number) := by
    filter_upwards [upper, lower] with number upper lower
    have total_positive : 0 < total number := (exp_pos _).trans_le lower
    calc
      good number / total number ≤ exp (constant * number) / total number :=
        div_le_div_of_nonneg_right upper total_positive.le
      _ ≤ exp (constant * number) /
          exp ((number : ℝ) * log number - 2 * number * log (log number) - constant * number) :=
        div_le_div_of_nonneg_left (exp_pos _).le (exp_pos _) lower
      _ = exp (rarityExponent constant number) := by
        rw [← exp_sub]
        congr 1
        unfold rarityExponent
        ring
  have nonnegative : ∀ᶠ number in atTop, 0 ≤ good number / total number := by
    filter_upwards [lower] with number lower
    exact div_nonneg (good_nonnegative number) ((exp_pos _).trans_le lower).le
  exact squeeze_zero' nonnegative ratio_bound
    ((rarity_bound_tendsto_zero constant).comp tendsto_natCast_atTop_atTop)

end BondalThomsen
