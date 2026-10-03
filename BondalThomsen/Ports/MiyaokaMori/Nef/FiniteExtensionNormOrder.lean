module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LatticeDeterminantOrder
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Algebraic.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

noncomputable section

open Submodule

namespace Ring

variable {baseRing extensionRing baseField extensionField : Type*} [CommRing baseRing] [IsDomain baseRing] [IsNoetherianRing baseRing]
  [Ring.KrullDimLE 1 baseRing] [CommRing extensionRing] [IsDomain extensionRing] [Algebra baseRing extensionRing] [FaithfulSMul baseRing extensionRing]
  [Module.Finite baseRing extensionRing] [Field baseField] [Algebra baseRing baseField] [IsFractionRing baseRing baseField]
  [Field extensionField] [Algebra extensionRing extensionField] [IsFractionRing extensionRing extensionField] [Algebra baseField extensionField] [Algebra baseRing extensionField]
  [IsScalarTower baseRing baseField extensionField] [IsScalarTower baseRing extensionRing extensionField]

variable (baseRing extensionRing extensionField) in

def toFracLin : extensionRing →ₗ[baseRing] extensionField := (IsScalarTower.toAlgHom baseRing extensionRing extensionField).toLinearMap

lemma toFracLin_apply (coefficients : extensionRing) : toFracLin baseRing extensionRing extensionField coefficients = algebraMap extensionRing extensionField coefficients := rfl

lemma toFracLin_injective : Function.Injective (toFracLin baseRing extensionRing extensionField) :=
  IsFractionRing.injective extensionRing extensionField

variable (baseRing extensionRing baseField extensionField) in
theorem isLattice_range : IsLattice baseField ((⊤ : Submodule baseRing extensionRing).map (toFracLin baseRing extensionRing extensionField)) where
  fg := (Module.Finite.fg_top (R := baseRing) (M := extensionRing)).map _
  span_eq_top := by
    rw [eq_top_iff]
    intro fraction _
    obtain ⟨⟨coefficients, finiteSet⟩, hs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid extensionRing (nonZeroDivisors baseRing)) fraction
    obtain ⟨element, ha, has⟩ := finiteSet.2
    have ha0 : algebraMap baseRing baseField element ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective baseRing baseField)).mpr (nonZeroDivisors.ne_zero ha)
    have h1 : algebraMap extensionRing extensionField (finiteSet : extensionRing) = algebraMap baseField extensionField (algebraMap baseRing baseField element) := by
      rw [← has, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have : fraction = (algebraMap baseRing baseField element)⁻¹ • algebraMap extensionRing extensionField coefficients := by
      rw [← hs, h1, Algebra.smul_def, map_inv₀, mul_comm fraction, ← mul_assoc,
        inv_mul_cancel₀ ((map_ne_zero _).mpr ha0), one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨coefficients, trivial, rfl⟩)

lemma map_mulLeft_range (multiplier : extensionRing) :
    ((⊤ : Submodule baseRing extensionRing).map (toFracLin baseRing extensionRing extensionField)).map
        ((LinearMap.mulLeft baseField (algebraMap extensionRing extensionField multiplier)).restrictScalars baseRing) =
      ((Ideal.span {multiplier} : Ideal extensionRing).restrictScalars baseRing).map (toFracLin baseRing extensionRing extensionField) := by
  ext element
  constructor
  · rintro ⟨_, ⟨coefficients, -, rfl⟩, rfl⟩
    refine ⟨multiplier * coefficients, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self multiplier), ?_⟩
    simp [toFracLin_apply]
  · rintro ⟨scalar, hc, rfl⟩
    obtain ⟨coefficients, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    exact ⟨algebraMap extensionRing extensionField coefficients, ⟨coefficients, trivial, rfl⟩, by simp [toFracLin_apply, mul_comm]⟩

lemma relLength_range_eq (multiplier : extensionRing) :
    relLength ((⊤ : Submodule baseRing extensionRing).map (toFracLin baseRing extensionRing extensionField))
        (((⊤ : Submodule baseRing extensionRing).map (toFracLin baseRing extensionRing extensionField)).map
          ((LinearMap.mulLeft baseField (algebraMap extensionRing extensionField multiplier)).restrictScalars baseRing)) =
      Module.length baseRing (extensionRing ⧸ Ideal.span {multiplier}) := by
  rw [map_mulLeft_range, relLength_map _ toFracLin_injective, relLength_top]
  exact (Submodule.Quotient.restrictScalarsEquiv baseRing (Ideal.span {multiplier} : Ideal extensionRing)).length_eq

omit [Field baseField] [Algebra baseRing baseField] [IsFractionRing baseRing baseField] [Field extensionField] [Algebra extensionRing extensionField] [IsFractionRing extensionRing extensionField]
  [Algebra baseField extensionField] [Algebra baseRing extensionField] [IsScalarTower baseRing baseField extensionField] [IsScalarTower baseRing extensionRing extensionField] in
variable (baseRing) in

theorem length_quotient_span_singleton_ne_top {multiplier : extensionRing} (hy : multiplier ≠ 0) :
    Module.length baseRing (extensionRing ⧸ Ideal.span {multiplier}) ≠ ⊤ := by
  let baseField := FractionRing baseRing
  let extensionField := FractionRing extensionRing
  let _ : Algebra baseField extensionField := FractionRing.liftAlgebra baseRing extensionField
  have h1 := isLattice_range baseRing extensionRing baseField extensionField
  have hbij : Function.Surjective (LinearMap.mulLeft baseField (algebraMap extensionRing extensionField multiplier)) := by
    have hy' : algebraMap extensionRing extensionField multiplier ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective extensionRing extensionField)).mpr hy
    intro fraction
    exact ⟨(algebraMap extensionRing extensionField multiplier)⁻¹ * fraction, by
      rw [LinearMap.mulLeft_apply, ← mul_assoc, mul_inv_cancel₀ hy', one_mul]⟩
  have h2 := IsLattice.map' (baseRing := baseRing) _ hbij ((⊤ : Submodule baseRing extensionRing).map (toFracLin baseRing extensionRing extensionField))
  rw [← relLength_range_eq (baseField := baseField) (extensionField := extensionField) multiplier]
  exact IsLattice.relLength_ne_top (baseField := baseField) _ _

theorem ordFrac_norm_eq_exp_length {multiplier : extensionRing} (hy : multiplier ≠ 0) :
    Ring.ordFrac baseRing (Algebra.norm baseField (algebraMap extensionRing extensionField multiplier)) =
      WithZero.exp ((Module.length baseRing (extensionRing ⧸ Ideal.span {multiplier})).toNat : ℤ) := by
  have : Module.Finite baseField extensionField := Module.Finite.of_isLocalization baseRing extensionRing (nonZeroDivisors baseRing)
  have h1 := isLattice_range baseRing extensionRing baseField extensionField
  have hy' : algebraMap extensionRing extensionField multiplier ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective extensionRing extensionField)).mpr hy
  have hdet : LinearMap.det (LinearMap.mulLeft baseField (algebraMap extensionRing extensionField multiplier)) ≠ 0 := by
    have := (Algebra.norm_ne_zero_iff (R := baseField)).mpr hy'
    rwa [Algebra.norm_apply] at this
  have hle : ((⊤ : Submodule baseRing extensionRing).map (toFracLin baseRing extensionRing extensionField)).map
      ((LinearMap.mulLeft baseField (algebraMap extensionRing extensionField multiplier)).restrictScalars baseRing) ≤
      (⊤ : Submodule baseRing extensionRing).map (toFracLin baseRing extensionRing extensionField) := by
    rw [map_mulLeft_range]; exact Submodule.map_mono le_top
  have key := ordFrac_det_eq_exp_relLength (baseRing := baseRing) (baseField := baseField) _ _ hdet hle
  rw [relLength_range_eq] at key
  rw [Algebra.norm_apply]
  exact key

end Ring

end
