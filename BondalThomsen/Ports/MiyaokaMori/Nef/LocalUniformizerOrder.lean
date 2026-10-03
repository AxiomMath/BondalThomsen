module

public import BondalThomsen.Ports.MiyaokaMori.Nef.PrincipalCartierDivisor
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Intersection
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]

theorem ord_one_eq_zero (point : scheme) : scheme.ord (1 : scheme.functionField) point = 0 := by
  simpa only [Units.val_one, principalCartierData_coefficient] using
    principalCartierData_coefficient_one (scheme := scheme) point

theorem ord_inv_eq_neg {rational : scheme.functionField} (nonzero : rational ≠ 0) (point : scheme) :
    scheme.ord rational⁻¹ point = -scheme.ord rational point := by
  have additive := Scheme.ord_mul (X := scheme) (x := point) nonzero (inv_ne_zero nonzero)
  rw [mul_inv_cancel₀ nonzero, ord_one_eq_zero] at additive
  omega

theorem ord_div_eq_sub {first second : scheme.functionField}
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0) (point : scheme) :
    scheme.ord (first / second) point = scheme.ord first point - scheme.ord second point := by
  rw [div_eq_mul_inv, Scheme.ord_mul firstNonzero (inv_ne_zero secondNonzero),
    ord_inv_eq_neg secondNonzero, sub_eq_add_neg]

theorem ord_germToFunctionField_eq_one_of_span_germ_eq_maximalIdeal {region : scheme.Opens}
    [Nonempty region] {point : scheme} (contains : point ∈ region)
    (coheightOne : Order.coheight point = 1) [IsDiscreteValuationRing (scheme.presheaf.stalk point)]
    (sectionValue : Γ(scheme, region))
    (generates : Ideal.span {scheme.presheaf.germ region point contains sectionValue} =
      IsLocalRing.maximalIdeal (scheme.presheaf.stalk point)) :
    scheme.ord (scheme.germToFunctionField region sectionValue) point = 1 := by
  have : Ring.KrullDimLE 1 (scheme.presheaf.stalk point) := krullDimLE_of_coheight_le coheightOne.le
  have irreducible : Irreducible (scheme.presheaf.germ region point contains sectionValue) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr generates.symm
  have nonzero : scheme.germToFunctionField region sectionValue ≠ 0 := by
    intro zero
    apply irreducible.ne_zero
    apply IsFractionRing.injective (scheme.presheaf.stalk point) scheme.functionField
    rw [map_zero]
    exact (scheme.algebraMap_germ_eq_germToFunctionField contains sectionValue).trans zero
  rw [Scheme.ord_eq_iff coheightOne nonzero]
  change Ring.ordFrac (scheme.presheaf.stalk point) (scheme.germToFunctionField region sectionValue) = _
  rw [← scheme.algebraMap_germ_eq_germToFunctionField contains sectionValue]
  exact Ring.ordFrac_irreducible irreducible

end AlgebraicGeometry.Scheme
