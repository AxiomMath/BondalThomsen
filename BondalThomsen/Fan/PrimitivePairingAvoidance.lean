module

public import BondalThomsen.Fan.PrimitiveNefArithmetic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Algebra.Ring.Basic

@[expose] public section

namespace BondalThomsen.PrimitivePairingAvoidance

open Set Finset Filter
open scoped Topology

theorem finite_integer_levels_in_interval (offset slope lower upper : ℚ)
    (nonzero : slope ≠ 0) :
    {parameter : ℚ | parameter ∈ Ioo lower upper ∧
      ∃ level : ℤ, offset + slope * parameter = level}.Finite := by
  let bottom := min (offset + slope * lower) (offset + slope * upper)
  let top := max (offset + slope * lower) (offset + slope * upper)
  let integer_values : Set ℚ := (fun level : ℤ => (level : ℚ)) '' Set.Icc ⌈bottom⌉ ⌊top⌋
  have integer_values_finite : integer_values.Finite :=
    (Set.finite_Icc _ _).image _
  have injective : Function.Injective (fun parameter : ℚ => offset + slope * parameter) := by
    intro first second equality
    exact mul_left_cancel₀ nonzero (add_left_cancel equality)
  apply (integer_values_finite.preimage injective.injOn).subset
  rintro parameter ⟨between, level, equality⟩
  have bounded : bottom ≤ offset + slope * parameter ∧ offset + slope * parameter ≤ top := by
    dsimp [bottom, top]
    by_cases nonnegative : 0 ≤ slope
    · refine ⟨(min_le_left _ _).trans ?_, le_trans ?_ (le_max_right _ _)⟩ <;> nlinarith [between.1, between.2]
    · have negative : slope ≤ 0 := le_of_lt (lt_of_not_ge nonnegative)
      refine ⟨(min_le_right _ _).trans ?_, le_trans ?_ (le_max_left _ _)⟩ <;> nlinarith [between.1, between.2]
  refine ⟨level, ⟨?_, ?_⟩, equality.symm⟩
  · have comparison := Int.ceil_le_ceil (bounded.1.trans_eq equality)
    simpa only [Int.ceil_intCast] using comparison
  · have comparison := Int.floor_le_floor (equality.symm.trans_le bounded.2)
    simpa only [Int.floor_intCast] using comparison

theorem exists_parameter_avoiding_integers {Index : Type*} [Finite Index]
    (offset slope : Index → ℚ) (nonzero : ∀ index, slope index ≠ 0)
    {lower upper : ℚ} (nonempty : lower < upper) :
    ∃ parameter ∈ Ioo lower upper,
      ∀ index (level : ℤ), offset index + slope index * parameter ≠ level := by
  let forbidden : Index → Set ℚ := fun index =>
    {parameter | parameter ∈ Ioo lower upper ∧
      ∃ level : ℤ, offset index + slope index * parameter = level}
  have forbidden_finite : (⋃ index, forbidden index).Finite :=
    Set.finite_iUnion fun index =>
      finite_integer_levels_in_interval (offset index) (slope index) lower upper (nonzero index)
  obtain ⟨parameter, between, outside⟩ :=
    (Set.Ioo_infinite nonempty).exists_notMem_finite forbidden_finite
  refine ⟨parameter, between, ?_⟩
  intro index level equality
  exact outside (Set.mem_iUnion.mpr ⟨index, between, level, equality⟩)

variable {Lattice : Type*} [AddCommGroup Lattice] [Module ℤ Lattice]

theorem exists_common_nonzero_direction {Index : Type*} [Finite Index]
    (directions : Submodule ℚ (Lattice →ₗ[ℤ] ℚ)) (vectors : Index → Lattice)
    (nonconstant : ∀ index, ∃ variation : directions, variation.1 (vectors index) ≠ 0) :
    ∃ variation : directions, ∀ index, variation.1 (vectors index) ≠ 0 := by
  let evaluations : Index → directions →ₗ[ℚ] ℚ := fun index =>
    ((LinearMap.applyₗ' ℚ) (vectors index)).comp directions.subtype
  have proper : ∀ index, (evaluations index).ker ≠ ⊤ := by
    intro index top_kernel
    obtain ⟨variation, nonzero⟩ := nonconstant index
    have member : variation ∈ (evaluations index).ker := top_kernel.symm ▸ Submodule.mem_top
    exact nonzero member
  obtain ⟨variation, outside⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (fun index => (evaluations index).ker) proper
  exact ⟨variation, outside⟩

theorem exists_pairing_in_fiber_avoiding_integers {Index Control : Type*}
    [Finite Index] [Finite Control]
    (center : Lattice →ₗ[ℤ] ℚ) (directions : Submodule ℚ (Lattice →ₗ[ℤ] ℚ))
    (vectors : Index → Lattice)
    (nonconstant : ∀ index, ∃ variation : directions, variation.1 (vectors index) ≠ 0)
    (controlled : Control → Lattice) (lower upper : Control → ℚ)
    (center_interval : ∀ index, lower index < center (controlled index) ∧
      center (controlled index) < upper index) :
    ∃ pairing : Lattice →ₗ[ℤ] ℚ,
      pairing - center ∈ directions ∧
      (∀ index, lower index < pairing (controlled index) ∧ pairing (controlled index) < upper index) ∧
      (∀ index (level : ℤ), pairing (vectors index) ≠ level) := by
  obtain ⟨variation, nonzero⟩ := exists_common_nonzero_direction directions vectors nonconstant
  have nearby : ∀ᶠ parameter : ℚ in 𝓝 0, ∀ index,
      lower index < center (controlled index) + parameter * variation.1 (controlled index) ∧
      center (controlled index) + parameter * variation.1 (controlled index) < upper index := by
    rw [Filter.eventually_all]
    intro index
    have continuous : Continuous (fun parameter : ℚ =>
        center (controlled index) + parameter * variation.1 (controlled index)) :=
      continuous_const.add (continuous_id.mul continuous_const)
    have interval_mem : Ioo (lower index) (upper index) ∈
        𝓝 (center (controlled index) + (0 : ℚ) * variation.1 (controlled index)) := by
      simpa only [zero_mul, add_zero] using isOpen_Ioo.mem_nhds (center_interval index)
    exact continuous.continuousAt.preimage_mem_nhds interval_mem
  obtain ⟨start, stop, contains_zero, controlled_interval⟩ := nearby.exists_Ioo_subset
  obtain ⟨parameter, between, avoids⟩ := exists_parameter_avoiding_integers
    (fun index => center (vectors index)) (fun index => variation.1 (vectors index)) nonzero
      (contains_zero.1.trans contains_zero.2)
  refine ⟨center + parameter • variation.1, ?_, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using directions.smul_mem parameter variation.property
  · have intervals := controlled_interval between
    change ∀ index, lower index < center (controlled index) + parameter * variation.1 (controlled index) ∧
      center (controlled index) + parameter * variation.1 (controlled index) < upper index at intervals
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using intervals
  · intro index level
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm] using avoids index level

noncomputable def vanishingDirections {Index : Type*} (vectors : Index → Lattice) :
    Submodule ℚ (Lattice →ₗ[ℤ] ℚ) :=
  ⨅ index, (((LinearMap.applyₗ' ℚ) (vectors index)).ker)

@[simp] theorem mem_vanishingDirections {Index : Type*} (vectors : Index → Lattice)
    (variation : Lattice →ₗ[ℤ] ℚ) :
    variation ∈ vanishingDirections vectors ↔ ∀ index, variation (vectors index) = 0 := by
  simp [vanishingDirections, Submodule.mem_iInf, LinearMap.mem_ker]

end BondalThomsen.PrimitivePairingAvoidance
