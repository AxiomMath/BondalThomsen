module

public import BondalThomsen.Rarity.DeepToricFanoIntegralFanClasses
public import BondalThomsen.ProjectiveBundle.IntegralFanRigidity

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Set Filter Real
open BondalThomsen.ToricTransport BondalThomsen.ProjectiveBundle
open scoped Classical Topology

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

theorem smoothProjectiveToricFanoIntegralFanClasses_exp_lower_eventually
    (fanoFinite : ∀ dimension, (smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension).Finite) :
    ∀ᶠ dimension : ℕ in atTop,
      exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
        10 * dimension) ≤
          (Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) : ℝ) := by
  filter_upwards [parameterIntegralFanClasses_exp_lower_eventually,
    parameterFanClass_mem_smoothProjectiveToricFanoIntegralFanClasses_eventually 𝕜]
    with dimension bound membership
  let := (fanoFinite dimension).fintype
  have subset : parameterIntegralFanClasses dimension ⊆
      smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension := by
    rintro _ ⟨matrix, rfl⟩
    exact membership matrix
  have cardinality : Nat.card ↥(parameterIntegralFanClasses dimension) ≤
      Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) :=
    Nat.card_le_card_of_injective (Set.inclusion subset) (Set.inclusion_injective subset)
  exact bound.trans (by exact_mod_cast cardinality)

theorem deepIntegralFanClasses_exp_upper_eventually :
    ∀ᶠ dimension : ℕ in atTop,
      (Nat.card ↥(deepIntegralFanClasses dimension) : ℝ) ≤ exp ((4 * log 48) * dimension) := by
  filter_upwards [eventually_gt_atTop 0] with dimension positive
  have bound := (deepIntegralFanClasses_finite_and_card_le_tree_bound dimension positive).2
  have realBound : (Nat.card ↥(deepIntegralFanClasses dimension) : ℝ) ≤
      (48 : ℝ) ^ (4 * dimension) := by exact_mod_cast bound
  have exponential : (48 : ℝ) ^ (4 * dimension) = exp ((4 * log 48) * dimension) := by
    conv_lhs => rw [← exp_log (by norm_num : (0 : ℝ) < 48)]
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  exact realBound.trans_eq exponential

theorem theorem_1_3_deepFanoIntegralFanClasses
    (fanoFinite : ∀ dimension, (smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension).Finite) :
    ∃ constant : ℝ, 0 < constant ∧
      (∀ᶠ dimension : ℕ in atTop,
        (Nat.card ↥(deepIntegralFanClasses dimension) : ℝ) ≤ exp (constant * dimension) ∧
        exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
          constant * dimension) ≤
            (Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) : ℝ)) ∧
      Tendsto (fun dimension => (Nat.card ↥(deepIntegralFanClasses dimension) : ℝ) /
        Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension)) atTop (𝓝 0) := by
  let constant : ℝ := 10 + 4 * log 48
  have logarithmNonnegative : (0 : ℝ) ≤ log 48 := log_nonneg (by norm_num)
  have constantGeTen : 10 ≤ constant := by dsimp [constant]; linarith
  have constantGeTree : 4 * log 48 ≤ constant := by dsimp [constant]; linarith
  have upper : ∀ᶠ dimension : ℕ in atTop,
      (Nat.card ↥(deepIntegralFanClasses dimension) : ℝ) ≤ exp (constant * dimension) := by
    filter_upwards [deepIntegralFanClasses_exp_upper_eventually] with dimension bound
    exact bound.trans (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right constantGeTree (Nat.cast_nonneg dimension)))
  have lower : ∀ᶠ dimension : ℕ in atTop,
      exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
        constant * dimension) ≤
          (Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) : ℝ) := by
    filter_upwards [smoothProjectiveToricFanoIntegralFanClasses_exp_lower_eventually 𝕜 fanoFinite]
      with dimension bound
    apply le_trans (exp_le_exp.mpr ?_) bound
    nlinarith [mul_le_mul_of_nonneg_right constantGeTen
      (Nat.cast_nonneg dimension : (0 : ℝ) ≤ dimension)]
  refine ⟨constant, by dsimp [constant]; linarith, ?_, ?_⟩
  · filter_upwards [upper, lower] with dimension upperBound lowerBound
    exact ⟨upperBound, lowerBound⟩
  · exact asymptotic_rarity_of_bounds _ _ constant (fun dimension => Nat.cast_nonneg _)
      upper lower

end BondalThomsen
