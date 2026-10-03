module

public import BondalThomsen.Rarity.LogCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace BondalThomsen

open Real Filter
open scoped Topology

noncomputable def familyWeight (dimension : ℕ) : ℕ := ⌊log dimension⌋₊

noncomputable def familyRows (dimension : ℕ) : ℕ := dimension / (familyWeight dimension + 1)

noncomputable def familyColumns (dimension : ℕ) : ℕ :=
  dimension - familyRows dimension * familyWeight dimension

theorem familyColumns_eq_rows_add_remainder (dimension : ℕ) :
    familyColumns dimension = familyRows dimension + dimension % (familyWeight dimension + 1) := by
  have division := Nat.div_add_mod' dimension (familyWeight dimension + 1)
  change familyRows dimension * (familyWeight dimension + 1) +
    dimension % (familyWeight dimension + 1) = dimension at division
  unfold familyColumns
  simp only [Nat.mul_add, Nat.mul_one] at division
  omega

theorem family_dimension_eq (dimension : ℕ) :
    familyRows dimension * familyWeight dimension + familyColumns dimension = dimension := by
  rw [familyColumns_eq_rows_add_remainder]
  have division := Nat.div_add_mod' dimension (familyWeight dimension + 1)
  change familyRows dimension * (familyWeight dimension + 1) +
    dimension % (familyWeight dimension + 1) = dimension at division
  nlinarith

theorem family_parameter_bounds (dimension : ℕ)
    (log_large : 2 ≤ log dimension) (dimension_large : 16 * (log dimension) ^ 2 ≤ dimension) :
    0 < familyWeight dimension ∧ familyWeight dimension ≤ familyColumns dimension ∧
      (dimension : ℝ) / (4 * log dimension) ≤ familyRows dimension ∧
      (familyRows dimension : ℝ) * log dimension ≤ dimension ∧
      (familyColumns dimension : ℝ) * log dimension ≤ 2 * dimension ∧
      ((familyColumns dimension : ℝ) + 1) * log dimension ≤ 3 * dimension ∧
      familyRows dimension ≤ dimension ∧ familyColumns dimension + 1 ≤ dimension := by
  let weight := familyWeight dimension
  let rows := familyRows dimension
  let columns := familyColumns dimension
  let logarithm := log (dimension : ℝ)
  have log_positive : 0 < logarithm := by dsimp [logarithm]; linarith
  have weight_le : (weight : ℝ) ≤ logarithm := Nat.floor_le log_positive.le
  have log_lt : logarithm < (weight : ℝ) + 1 := Nat.lt_floor_add_one logarithm
  have weight_positive : 0 < weight := by
    have floor_le : 1 ≤ Nat.floor logarithm :=
      (Nat.le_floor_iff log_positive.le).mpr (by norm_num; dsimp [logarithm]; linarith)
    exact floor_le
  have remainder_le : dimension % (weight + 1) ≤ weight := by
    exact Nat.le_of_lt_succ (Nat.mod_lt dimension (Nat.succ_pos weight))
  have division : rows * (weight + 1) + dimension % (weight + 1) = dimension :=
    Nat.div_add_mod' dimension (weight + 1)
  have columns_eq : columns = rows + dimension % (weight + 1) :=
    familyColumns_eq_rows_add_remainder dimension
  have dimension_eq : rows * weight + columns = dimension := family_dimension_eq dimension
  have division_real : (rows : ℝ) * ((weight : ℝ) + 1) +
      ((dimension % (weight + 1) : ℕ) : ℝ) = dimension := by exact_mod_cast division
  have columns_real : (columns : ℝ) = rows + ((dimension % (weight + 1) : ℕ) : ℝ) := by
    exact_mod_cast columns_eq
  have remainder_real : ((dimension % (weight + 1) : ℕ) : ℝ) ≤ weight := by
    exact_mod_cast remainder_le
  have dimension_eq_real : (rows : ℝ) * weight + columns = dimension := by
    exact_mod_cast dimension_eq
  have dimension_nonnegative : (0 : ℝ) ≤ dimension := Nat.cast_nonneg _
  have rows_nonnegative : (0 : ℝ) ≤ rows := Nat.cast_nonneg _
  have columns_nonnegative : (0 : ℝ) ≤ columns := Nat.cast_nonneg _
  have large : 16 * logarithm ^ 2 ≤ dimension := dimension_large
  have log_at_least_two : 2 ≤ logarithm := log_large
  have log_le_dimension : logarithm ≤ dimension := by nlinarith
  have rows_log_upper : (rows : ℝ) * logarithm ≤ dimension := by
    nlinarith [show (0 : ℝ) ≤ ((dimension % (weight + 1) : ℕ) : ℝ) from Nat.cast_nonneg _]
  have columns_log_upper : (columns : ℝ) * logarithm ≤ 2 * dimension := by
    nlinarith [mul_le_mul_of_nonneg_right remainder_real log_positive.le]
  have columns_succ_log_upper : ((columns : ℝ) + 1) * logarithm ≤ 3 * dimension := by
    nlinarith
  have rows_lower : (dimension : ℝ) / (4 * logarithm) ≤ rows := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * logarithm)).mpr
    nlinarith [mul_nonneg rows_nonnegative (show 0 ≤ logarithm - 1 by linarith)]
  have weight_columns : weight ≤ columns := by
    have dimension_le_rows : (dimension : ℝ) ≤ rows * (4 * logarithm) :=
      (div_le_iff₀ (by positivity : 0 < 4 * logarithm)).mp rows_lower
    have columns_ge_rows : (rows : ℝ) ≤ columns := by
      exact_mod_cast (show rows ≤ columns by omega)
    have weight_le_rows : (weight : ℝ) ≤ rows := by
      nlinarith [mul_le_mul_of_nonneg_right weight_le log_positive.le]
    exact_mod_cast weight_le_rows.trans columns_ge_rows
  have rows_positive : 0 < rows := by
    have : (0 : ℝ) < rows := (div_pos (by nlinarith : (0 : ℝ) < dimension)
      (by positivity : 0 < 4 * logarithm)).trans_le rows_lower
    exact_mod_cast this
  have rows_le_dimension : rows ≤ dimension := by nlinarith
  have columns_succ_le : columns + 1 ≤ dimension := by nlinarith
  exact ⟨weight_positive, weight_columns, rows_lower, rows_log_upper,
    columns_log_upper, columns_succ_log_upper, rows_le_dimension, columns_succ_le⟩

theorem family_parameter_bounds_eventually : ∀ᶠ dimension : ℕ in atTop,
    2 ≤ log dimension ∧ 16 * (log dimension) ^ 2 ≤ dimension := by
  have log_limit : Tendsto (fun dimension : ℕ => log dimension) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ratio_limit : Tendsto (fun dimension : ℕ => (log dimension) ^ 2 / dimension)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, one_mul, add_zero] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [log_limit.eventually (eventually_ge_atTop 2),
    ratio_limit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    eventually_ge_atTop (1 : ℕ)] with dimension log_large ratio_small dimension_positive
  have positive : (0 : ℝ) < dimension := by exact_mod_cast dimension_positive
  have scaled := (div_lt_iff₀ positive).mp ratio_small
  exact ⟨log_large, by linarith⟩

theorem family_log_exponent_lower (dimension : ℕ)
    (log_large : 2 ≤ log dimension) (dimension_large : 16 * (log dimension) ^ 2 ≤ dimension) :
    (dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) - 10 * dimension ≤
      (familyRows dimension * familyWeight dimension : ℝ) *
        (log (familyColumns dimension) - log (familyWeight dimension)) -
        familyRows dimension * log (familyRows dimension) -
        (familyColumns dimension + 1) * log (familyColumns dimension + 1) := by
  obtain ⟨weight_positive, weight_le_columns, rows_lower, rows_log_upper,
    columns_log_upper, columns_succ_log_upper, rows_le, columns_succ_le⟩ :=
      family_parameter_bounds dimension log_large dimension_large
  have log_positive : 0 < log (dimension : ℝ) := by linarith
  have dimension_positive : (0 : ℝ) < dimension := by
    have square_positive : 0 < (log (dimension : ℝ)) ^ 2 := sq_pos_of_pos log_positive
    nlinarith
  have weight_positive_real : (0 : ℝ) < familyWeight dimension := by
    exact_mod_cast weight_positive
  have rows_positive_real : (0 : ℝ) < familyRows dimension :=
    (div_pos dimension_positive (by positivity)).trans_le rows_lower
  have columns_positive_real : (0 : ℝ) < familyColumns dimension := by
    exact_mod_cast weight_positive.trans_le weight_le_columns
  have rows_le_columns : familyRows dimension ≤ familyColumns dimension := by
    rw [familyColumns_eq_rows_add_remainder]
    omega
  have columns_lower : (dimension : ℝ) / (4 * log dimension) ≤ familyColumns dimension :=
    rows_lower.trans (by exact_mod_cast rows_le_columns)
  have columns_log_lower := log_le_log (div_pos dimension_positive (by positivity)) columns_lower
  rw [log_div dimension_positive.ne' (by positivity),
    log_mul (by norm_num : (4 : ℝ) ≠ 0) log_positive.ne'] at columns_log_lower
  have weight_upper : (familyWeight dimension : ℝ) ≤ log dimension :=
    Nat.floor_le log_positive.le
  have weight_log_upper := log_le_log weight_positive_real weight_upper
  have rows_log_le := log_le_log rows_positive_real (by
    exact_mod_cast rows_le : (familyRows dimension : ℝ) ≤ dimension)
  have columns_succ_log_le := log_le_log
    (by positivity : (0 : ℝ) < (familyColumns dimension : ℝ) + 1)
    (by exact_mod_cast columns_succ_le : (familyColumns dimension : ℝ) + 1 ≤ dimension)
  have row_cost := mul_le_mul_of_nonneg_left rows_log_le
    (Nat.cast_nonneg (familyRows dimension) : (0 : ℝ) ≤ familyRows dimension)
  have column_cost := mul_le_mul_of_nonneg_left columns_succ_log_le
    (by positivity : (0 : ℝ) ≤ (familyColumns dimension : ℝ) + 1)
  have difference_lower : log dimension - 2 * log (log dimension) - log 4 ≤
      log (familyColumns dimension) - log (familyWeight dimension) := by linarith
  have main_term := mul_le_mul_of_nonneg_left difference_lower
    (by positivity : (0 : ℝ) ≤ familyRows dimension * familyWeight dimension)
  have dimension_eq : (familyRows dimension : ℝ) * familyWeight dimension +
      familyColumns dimension = dimension := by exact_mod_cast family_dimension_eq dimension
  have iterated_log_nonnegative : 0 ≤ log (log (dimension : ℝ)) :=
    log_nonneg (by linarith)
  have log_four_nonnegative : (0 : ℝ) ≤ log 4 := log_nonneg (by norm_num)
  have log_four_le : log (4 : ℝ) ≤ 4 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  nlinarith [mul_nonneg (Nat.cast_nonneg (familyColumns dimension) :
      (0 : ℝ) ≤ familyColumns dimension) iterated_log_nonnegative,
    mul_nonneg (Nat.cast_nonneg (familyColumns dimension) :
      (0 : ℝ) ≤ familyColumns dimension) log_four_nonnegative,
    mul_le_mul_of_nonneg_right log_four_le dimension_positive.le]

theorem projective_bundle_family_exp_lower {Classes : Type*} [Fintype Classes]
    [DecidableEq Classes] (dimension : ℕ)
    (log_large : 2 ≤ log dimension) (dimension_large : 16 * (log dimension) ^ 2 ≤ dimension)
    (classify : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension) → Classes)
    (fiber_bound : ∀ target,
      (Finset.univ.filter (fun matrix => classify matrix = target)).card ≤
        (familyRows dimension).factorial * (familyColumns dimension + 1).factorial) :
    exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
      10 * dimension) ≤ (Fintype.card Classes : ℝ) := by
  obtain ⟨weight_positive, weight_le, _⟩ :=
    family_parameter_bounds dimension log_large dimension_large
  have logarithmic := (family_log_exponent_lower dimension log_large dimension_large).trans
    (projective_bundle_family_log_lower _ _ _ weight_positive weight_le classify fiber_bound)
  have classes_positive : (0 : ℝ) < Fintype.card Classes := by
    have counting := projective_bundle_family_count _ _ _ classify fiber_bound
    have choose_positive : 0 < (familyColumns dimension).choose (familyWeight dimension) :=
      Nat.choose_pos weight_le
    have card_positive : 0 < Fintype.card Classes := by
      by_contra not_positive
      have zero : Fintype.card Classes = 0 := by omega
      rw [zero, mul_zero] at counting
      exact (Nat.pow_pos choose_positive).not_ge counting
    exact_mod_cast card_positive
  simpa only [exp_log classes_positive] using exp_le_exp.mpr logarithmic

end BondalThomsen
