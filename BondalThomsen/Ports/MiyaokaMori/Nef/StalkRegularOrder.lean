module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Divisors.StalkRegularOrder

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]

theorem ord_algebraMap_nonneg (point : scheme) {regular : scheme.presheaf.stalk point}
    (nonzero : regular ≠ 0) :
    0 ≤ scheme.ord (algebraMap (scheme.presheaf.stalk point) scheme.functionField regular) point := by
  by_cases coheightOne : Order.coheight point = 1
  · have : Ring.KrullDimLE 1 (scheme.presheaf.stalk point) :=
      krullDimLE_of_coheight_le coheightOne.le
    have imageNonzero : algebraMap (scheme.presheaf.stalk point) scheme.functionField regular ≠ 0 := by
      intro zero
      apply nonzero
      exact IsFractionRing.injective (scheme.presheaf.stalk point) scheme.functionField
        (zero.trans (map_zero _).symm)
    apply (Scheme.le_ord_iff coheightOne imageNonzero).2
    change 1 ≤ Ring.ordFrac (scheme.presheaf.stalk point)
      (algebraMap (scheme.presheaf.stalk point) scheme.functionField regular)
    exact Ring.ordFrac_ge_one_of_ne_zero nonzero
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one coheightOne]

theorem ord_germToFunctionField_nonneg {region : scheme.Opens} [Nonempty region]
    {sectionValue : Γ(scheme, region)} (nonzero : sectionValue ≠ 0)
    {point : scheme} (contains : point ∈ region) :
    0 ≤ scheme.ord (scheme.germToFunctionField region sectionValue) point := by
  rw [← scheme.algebraMap_germ_eq_germToFunctionField contains sectionValue]
  apply ord_algebraMap_nonneg point
  intro zero
  apply nonzero
  exact germ_injective_of_isIntegral scheme point contains (zero.trans (map_zero _).symm)

end AlgebraicGeometry.Divisors.StalkRegularOrder
