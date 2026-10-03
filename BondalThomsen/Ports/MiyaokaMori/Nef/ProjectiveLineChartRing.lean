module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Classical

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveChartRing

theorem X_mem (dimension : ℕ) (baseField : Type u) [Field baseField] (chart : Fin (dimension + 1)) :
    (MvPolynomial.X chart : MvPolynomial (Fin (dimension + 1)) baseField) ∈
      MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField 1 :=
  MvPolynomial.isHomogeneous_X baseField chart

def dehomogenize (dimension : ℕ) (baseField : Type u) [Field baseField] (chart : Fin (dimension + 1)) :
    MvPolynomial (Fin (dimension + 1)) baseField →ₐ[baseField]
      MvPolynomial {index : Fin (dimension + 1) // index ≠ chart} baseField :=
  MvPolynomial.aeval fun index => if equality : index = chart then 1 else MvPolynomial.X ⟨index, equality⟩

def chartToPoly (dimension : ℕ) (baseField : Type u) [Field baseField] (chart : Fin (dimension + 1)) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField)
      (MvPolynomial.X chart) →+* MvPolynomial {index : Fin (dimension + 1) // index ≠ chart} baseField :=
  (IsLocalization.Away.lift (MvPolynomial.X chart : MvPolynomial (Fin (dimension + 1)) baseField)
    (g := (dehomogenize dimension baseField chart).toRingHom)
    (by simp [dehomogenize])).comp
      (algebraMap _ (Localization.Away (MvPolynomial.X chart : MvPolynomial (Fin (dimension + 1)) baseField)))

def polyToChart (dimension : ℕ) (baseField : Type u) [Field baseField] (chart : Fin (dimension + 1)) :
    MvPolynomial {index : Fin (dimension + 1) // index ≠ chart} baseField →+*
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField)
        (MvPolynomial.X chart) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField 0) _).comp
      (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField 0)))
    (fun index => HomogeneousLocalization.Away.mk _ (X_mem dimension baseField chart) 1 (MvPolynomial.X index.1)
      (by simpa using MvPolynomial.isHomogeneous_X baseField index.1))

variable (dimension : ℕ) (baseField : Type u) [Field baseField] (chart : Fin (dimension + 1))

@[simp] theorem dehomogenize_X_self : dehomogenize dimension baseField chart (MvPolynomial.X chart) = 1 := by
  simp [dehomogenize]

theorem dehomogenize_X_of_ne {index : Fin (dimension + 1)} (distinct : index ≠ chart) :
    dehomogenize dimension baseField chart (MvPolynomial.X index) = MvPolynomial.X ⟨index, distinct⟩ := by
  simp [dehomogenize, distinct]

@[simp] theorem dehomogenize_C (scalar : baseField) :
    dehomogenize dimension baseField chart (MvPolynomial.C scalar) = MvPolynomial.C scalar := by
  simp [dehomogenize, MvPolynomial.algebraMap_eq]

theorem chartToPoly_mk (exponent : ℕ) (polynomial : MvPolynomial (Fin (dimension + 1)) baseField)
    (homogeneous : polynomial ∈ MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField (exponent • 1)) :
    chartToPoly dimension baseField chart
        (HomogeneousLocalization.Away.mk _ (X_mem dimension baseField chart) exponent polynomial homogeneous) =
      dehomogenize dimension baseField chart polynomial := by
  unfold chartToPoly IsLocalization.Away.lift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  simp

theorem mk_X_pow_zero (polynomial : MvPolynomial (Fin (dimension + 1)) baseField)
    (member : MvPolynomial.X chart ^ 0 ∈ Submonoid.powers (MvPolynomial.X chart :
      MvPolynomial (Fin (dimension + 1)) baseField)) :
    Localization.mk polynomial ⟨MvPolynomial.X chart ^ 0, member⟩ =
      algebraMap _ (Localization.Away (MvPolynomial.X chart :
        MvPolynomial (Fin (dimension + 1)) baseField)) polynomial := by
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1

theorem mk_X_pow_one (polynomial : MvPolynomial (Fin (dimension + 1)) baseField)
    (member : MvPolynomial.X chart ^ 1 ∈ Submonoid.powers (MvPolynomial.X chart :
      MvPolynomial (Fin (dimension + 1)) baseField)) :
    Localization.mk polynomial ⟨MvPolynomial.X chart ^ 1, member⟩ =
      Localization.mk polynomial ⟨MvPolynomial.X chart, Submonoid.mem_powers _⟩ := by
  congr 1
  exact Subtype.ext (pow_one _)

theorem polyToChart_X (index : {index : Fin (dimension + 1) // index ≠ chart}) :
    polyToChart dimension baseField chart (MvPolynomial.X index) =
      HomogeneousLocalization.Away.mk _ (X_mem dimension baseField chart) 1 (MvPolynomial.X index.1)
        (by simpa using MvPolynomial.isHomogeneous_X baseField index.1) :=
  MvPolynomial.eval₂Hom_X' _ _ _

theorem polyToChart_C (scalar : baseField) :
    polyToChart dimension baseField chart (MvPolynomial.C scalar) =
      algebraMap (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField 0) _
        (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField 0) scalar) :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem algebraMap_zero_eq_mk (constant : MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField 0) :
    algebraMap (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField 0)
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField)
        (MvPolynomial.X chart)) constant =
      HomogeneousLocalization.Away.mk _ (X_mem dimension baseField chart) 0 constant.1
        (by simpa using constant.2) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, mk_X_pow_zero, ← Localization.mk_one_eq_algebraMap]
  rfl

theorem chartToPoly_comp_polyToChart :
    (chartToPoly dimension baseField chart).comp (polyToChart dimension baseField chart) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro scalar
    rw [RingHom.comp_apply, RingHom.id_apply, polyToChart_C, algebraMap_zero_eq_mk, chartToPoly_mk]
    simp [MvPolynomial.algebraMap_eq]
  · intro index
    rw [RingHom.comp_apply, RingHom.id_apply, polyToChart_X, chartToPoly_mk,
      dehomogenize_X_of_ne dimension baseField chart index.2]

def awayScale : MvPolynomial (Fin (dimension + 1)) baseField →ₐ[baseField]
    Localization.Away (MvPolynomial.X chart : MvPolynomial (Fin (dimension + 1)) baseField) :=
  MvPolynomial.aeval fun index => Localization.mk (MvPolynomial.X index)
    ⟨MvPolynomial.X chart, Submonoid.mem_powers _⟩

theorem val_polyToChart_dehomogenize (polynomial : MvPolynomial (Fin (dimension + 1)) baseField) :
    (polyToChart dimension baseField chart (dehomogenize dimension baseField chart polynomial)).val =
      awayScale dimension baseField chart polynomial := by
  have equality : (algebraMap _ (Localization.Away (MvPolynomial.X chart :
      MvPolynomial (Fin (dimension + 1)) baseField))).comp
      ((polyToChart dimension baseField chart).comp (dehomogenize dimension baseField chart).toRingHom) =
      (awayScale dimension baseField chart).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro scalar
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehomogenize_C,
        polyToChart_C, HomogeneousLocalization.algebraMap_apply, algebraMap_zero_eq_mk,
        HomogeneousLocalization.Away.val_mk, awayScale, MvPolynomial.aeval_C, mk_X_pow_zero]
      simp [MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply baseField
        (MvPolynomial (Fin (dimension + 1)) baseField)
        (Localization.Away (MvPolynomial.X chart : MvPolynomial (Fin (dimension + 1)) baseField))]
    · intro index
      by_cases same : index = chart
      · subst same
        simp [awayScale]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          dehomogenize_X_of_ne dimension baseField chart same, polyToChart_X,
          HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
          awayScale, MvPolynomial.aeval_X, mk_X_pow_one]
  exact RingHom.congr_fun equality polynomial

theorem awayScale_monomial (powers : Fin (dimension + 1) →₀ ℕ) (scalar : baseField) :
    awayScale dimension baseField chart (MvPolynomial.monomial powers scalar) =
      Localization.mk (MvPolynomial.monomial powers scalar)
        ⟨MvPolynomial.X chart ^ powers.degree, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  induction powers using Finsupp.induction with
  | zero =>
    simp only [map_zero]
    rw [mk_X_pow_zero]
    simp [awayScale, IsScalarTower.algebraMap_apply baseField
      (MvPolynomial (Fin (dimension + 1)) baseField)
      (Localization.Away (MvPolynomial.X chart : MvPolynomial (Fin (dimension + 1)) baseField)),
      MvPolynomial.algebraMap_eq]
  | single_add index exponent remaining _ _ inductionHypothesis =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, inductionHypothesis]
    simp only [awayScale, MvPolynomial.aeval_X]
    rw [Localization.mk_pow, Localization.mk_mul]
    congr 1
    exact Subtype.ext (by simp [pow_add])

theorem awayScale_of_isHomogeneous {polynomial : MvPolynomial (Fin (dimension + 1)) baseField} {exponent : ℕ}
    (homogeneous : polynomial.IsHomogeneous exponent) :
    awayScale dimension baseField chart polynomial = Localization.mk polynomial
      ⟨MvPolynomial.X chart ^ exponent, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  conv_lhs => rw [polynomial.as_sum]
  conv_rhs => rw [polynomial.as_sum]
  rw [map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun powers member => ?_
  have degree : powers.degree = exponent := by
    rw [Finsupp.degree_eq_weight_one]
    exact homogeneous (MvPolynomial.mem_support_iff.mp member)
  subst degree
  exact awayScale_monomial dimension baseField chart powers _

theorem polyToChart_comp_chartToPoly :
    (polyToChart dimension baseField chart).comp (chartToPoly dimension baseField chart) = RingHom.id _ := by
  refine RingHom.ext fun fraction => ?_
  obtain ⟨exponent, numerator, homogeneous, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (X_mem dimension baseField chart) fraction
  rw [RingHom.comp_apply, RingHom.id_apply, chartToPoly_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_polyToChart_dehomogenize, HomogeneousLocalization.Away.val_mk,
    awayScale_of_isHomogeneous dimension baseField chart (exponent := exponent)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp (by simpa using homogeneous))]

def chartRingEquiv :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) baseField)
      (MvPolynomial.X chart) ≃+* MvPolynomial {index : Fin (dimension + 1) // index ≠ chart} baseField :=
  RingEquiv.ofRingHom (chartToPoly dimension baseField chart) (polyToChart dimension baseField chart)
    (chartToPoly_comp_polyToChart dimension baseField chart) (polyToChart_comp_chartToPoly dimension baseField chart)

end AlgebraicGeometry.ProjectiveChartRing
