module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Representation
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace BondalThomsen.CartierDivisorPrincipalKernel

universe schemeUniverse

variable {scheme : Scheme.{schemeUniverse}} [IsIntegral scheme]

open TauCeti.AlgebraicGeometry.Scheme

theorem unitIso_app_bijective
    (divisor : CartierDivisor scheme)
    (trivialization : @Iso scheme.Modules _ (SheafOfModules.unit scheme.ringCatSheaf) divisor.sheaf)
    (open_subset : scheme.Opens) :
    Function.Bijective (Scheme.Modules.Hom.app trivialization.hom open_subset) := by
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf scheme).mapIso trivialization).app (op open_subset)).hom

theorem trivialization_rationalGenerator_ne_zero
    (divisor : CartierDivisor scheme)
    (trivialization : @Iso scheme.Modules _ (SheafOfModules.unit scheme.ringCatSheaf) divisor.sheaf) :
    rationalFunctionsEquiv ⊤
      (Scheme.Modules.Hom.app (trivialization.hom ≫ divisor.sheafι) ⊤ (1 : Γ(scheme, ⊤))) ≠ 0 := by
  intro zero_generator
  have zero_section :
      Scheme.Modules.Hom.app (trivialization.hom ≫ divisor.sheafι) ⊤ (1 : Γ(scheme, ⊤)) = 0 :=
    (rationalFunctionsEquiv ⊤).injective (zero_generator.trans (map_zero _).symm)
  have zero_trivialization : Scheme.Modules.Hom.app trivialization.hom ⊤ (1 : Γ(scheme, ⊤)) = 0 := by
    apply divisor.sheafι_app_injective ⊤
    change Scheme.Modules.Hom.app (trivialization.hom ≫ divisor.sheafι) ⊤ (1 : Γ(scheme, ⊤)) =
      Scheme.Modules.Hom.app divisor.sheafι ⊤ 0
    simpa only [map_zero] using zero_section
  have impossible : (1 : Γ(scheme, ⊤)) = 0 :=
    (unitIso_app_bijective divisor trivialization ⊤).injective
      (zero_trivialization.trans (map_zero _).symm)
  exact one_ne_zero impossible

theorem localEquation_class_of_unitIso
    (divisor : CartierDivisor scheme)
    (trivialization : @Iso scheme.Modules _ (SheafOfModules.unit scheme.ringCatSheaf) divisor.sheaf)
    (open_subset : scheme.Opens) [Nonempty open_subset]
    (equation : scheme.functionFieldˣ)
    (local_equation : rationalUnitClass scheme open_subset (Additive.ofMul equation) =
      divisor |_ open_subset) :
    rationalUnitClass scheme open_subset (Additive.ofMul equation) =
      rationalUnitClass scheme open_subset
        (Additive.ofMul (Units.mk0
          (rationalFunctionsEquiv ⊤
            (Scheme.Modules.Hom.app (trivialization.hom ≫ divisor.sheafι) ⊤ (1 : Γ(scheme, ⊤))))
          (trivialization_rationalGenerator_ne_zero divisor trivialization))⁻¹) := by
  let generator := rationalFunctionsEquiv ⊤
    (Scheme.Modules.Hom.app (trivialization.hom ≫ divisor.sheafι) ⊤ (1 : Γ(scheme, ⊤)))
  let generator_unit : scheme.functionFieldˣ := Units.mk0 generator
    (trivialization_rationalGenerator_ne_zero divisor trivialization)
  obtain ⟨coefficient, coefficient_value⟩ :=
    (divisor.mem_sections_iff_of_rationalUnitClass_eq le_rfl local_equation).mp
      (divisor.sheafι_app_mem open_subset
        (Scheme.Modules.Hom.app trivialization.hom open_subset (1 : Γ(scheme, open_subset))))
  have coefficient_value' : scheme.germToFunctionField open_subset coefficient =
      (equation : scheme.functionField) * generator := by
    change scheme.germToFunctionField open_subset coefficient =
      (equation : scheme.functionField) * rationalFunctionsEquiv open_subset
        (Scheme.Modules.Hom.app (trivialization.hom ≫ divisor.sheafι) open_subset
          (1 : Γ(scheme, open_subset)))
      at coefficient_value
    rw [Scheme.Modules.Hom.rationalFunctionsEquiv_app_unit] at coefficient_value
    simpa only [map_one, one_mul] using coefficient_value
  let inverse_section : Γ(rationalFunctions scheme, open_subset) :=
    (rationalFunctionsEquiv open_subset).symm (equation⁻¹ : scheme.functionFieldˣ)
  have inverse_member : inverse_section ∈ divisor.sections open_subset := by
    apply (divisor.mem_sections_iff_of_rationalUnitClass_eq le_rfl local_equation).mpr
    refine ⟨1, ?_⟩
    simp [inverse_section]
  have surjective : ∀ local_section : Γ(divisor.sheaf, open_subset),
      ∃ coefficient : Γ(scheme, open_subset),
        Scheme.Modules.Hom.app trivialization.hom open_subset coefficient = local_section :=
    (unitIso_app_bijective divisor trivialization open_subset).surjective
  obtain ⟨inverse_coefficient, inverse_coefficient_value⟩ :=
    surjective (divisor.sectionMk inverse_section inverse_member)
  have inverse_value : scheme.germToFunctionField open_subset inverse_coefficient * generator =
      (equation⁻¹ : scheme.functionFieldˣ) := by
    have included := congrArg
      (fun local_section => rationalFunctionsEquiv open_subset
        (Scheme.Modules.Hom.app divisor.sheafι open_subset local_section)) inverse_coefficient_value
    change rationalFunctionsEquiv open_subset
      (Scheme.Modules.Hom.app (trivialization.hom ≫ divisor.sheafι) open_subset
        inverse_coefficient) = rationalFunctionsEquiv open_subset inverse_section at included
    rw [Scheme.Modules.Hom.rationalFunctionsEquiv_app_unit] at included
    simpa only [inverse_section, LinearEquiv.apply_symm_apply] using included
  have coefficients_inverse : coefficient * inverse_coefficient = 1 := by
    apply scheme.germToFunctionField_injective open_subset
    simp only [map_mul, map_one]
    calc
      _ = (equation : scheme.functionField) *
          (scheme.germToFunctionField open_subset inverse_coefficient * generator) := by
        rw [coefficient_value']
        ring
      _ = 1 := by rw [inverse_value, Units.mul_inv]
  let coefficient_unit : Γ(scheme, open_subset)ˣ :=
    ⟨coefficient, inverse_coefficient, coefficients_inverse,
      (mul_comm _ _).trans coefficients_inverse⟩
  apply (rationalUnitClass_eq_rationalUnitClass_iff scheme open_subset equation
    generator_unit⁻¹).mpr
  refine ⟨coefficient_unit, Units.ext ?_⟩
  change scheme.germToFunctionField open_subset coefficient *
    (generator_unit⁻¹ : scheme.functionFieldˣ) = (equation : scheme.functionField)
  rw [coefficient_value']
  change (equation : scheme.functionField) * (generator_unit : scheme.functionField) *
    (generator_unit⁻¹ : scheme.functionFieldˣ) = _
  rw [mul_assoc, Units.mul_inv, mul_one]

theorem exists_principal_of_unitIso
    (divisor : CartierDivisor scheme)
    (trivialization : @Iso scheme.Modules _ (SheafOfModules.unit scheme.ringCatSheaf) divisor.sheaf) :
    ∃ equation : scheme.functionFieldˣ,
      divisor = principalCartierDivisor scheme equation := by
  let generator_unit : scheme.functionFieldˣ := Units.mk0
    (rationalFunctionsEquiv ⊤
      (Scheme.Modules.Hom.app (trivialization.hom ≫ divisor.sheafι) ⊤ (1 : Γ(scheme, ⊤))))
    (trivialization_rationalGenerator_ne_zero divisor trivialization)
  refine ⟨generator_unit⁻¹, ?_⟩
  choose chart chart_le point_member equation local_equation using
    fun point : scheme => divisor.exists_localEquation_le ⊤ (Opens.mem_top point)
  apply (cartierDivisorSheaf scheme).eq_of_locally_eq' chart ⊤
    (fun point => homOfLE (chart_le point))
    (fun point _ => Opens.mem_iSup.mpr ⟨point, point_member point⟩)
  intro point
  let : Nonempty (chart point) := ⟨⟨point, point_member point⟩⟩
  change divisor |_ chart point =
    (principalCartierDivisor scheme generator_unit⁻¹) |_ chart point
  rw [principalCartierDivisor_restrict, ← local_equation point]
  exact localEquation_class_of_unitIso divisor trivialization (chart point)
    (equation point) (local_equation point)

theorem toLineBundleClass_eq_one_iff (divisor : CartierDivisor scheme) :
    divisor.toLineBundleClass = 1 ↔
      ∃ equation : scheme.functionFieldˣ,
        divisor = principalCartierDivisor scheme equation := by
  constructor
  · intro trivial_class
    rw [← TauCeti.AlgebraicGeometry.LineBundleClass.mk_trivial,
      divisor.toLineBundleClass_eq_mk_iff] at trivial_class
    obtain ⟨trivialization⟩ := trivial_class
    exact exists_principal_of_unitIso divisor
      ((TauCeti.SheafOfModules.freePUnitIsoUnit scheme.ringCatSheaf).symm ≪≫
        trivialization.symm)
  · rintro ⟨equation, rfl⟩
    exact CartierDivisor.toLineBundleClass_principalCartierDivisor equation

end BondalThomsen.CartierDivisorPrincipalKernel
