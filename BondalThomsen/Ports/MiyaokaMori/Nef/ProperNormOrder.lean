module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperFiniteLocalModel
public import BondalThomsen.Ports.MiyaokaMori.Nef.LocalNormOrderFormula
public import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Classical BigOperators AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

theorem proper_norm_order_eq_fiber_sum
    {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    [IsLocallyNoetherian source] [IsLocallyNoetherian target]
    (morphism : source ⟶ target) [IsProper morphism]
    (genericEquality : morphism.base (genericPoint source) = genericPoint target)
    (genericFinite : (morphism.residueFieldMap (genericPoint source)).hom.Finite)
    (targetPoint : target) (targetCoheight : Order.coheight targetPoint = 1)
    (rational : source.functionField) (rationalNonzero : rational ≠ 0) :
    letI := functionFieldAlgebra morphism genericEquality
    target.ord (Algebra.norm target.functionField rational) targetPoint =
      ∑ᶠ point ∈ morphism.base ⁻¹' {targetPoint},
        source.ord rational point * (morphism.residueDegree point : ℤ) := by
  classical
  let := functionFieldAlgebra morphism genericEquality
  let := stalkToFunctionFieldAlgebraOfHom morphism genericEquality targetPoint
  obtain ⟨modelRing, _, _, _, _, _, _, _, _, fiberEquivalence, modelComparison⟩ :=
    exists_finite_local_model morphism genericEquality genericFinite targetPoint targetCoheight
  have : IsScalarTower (target.presheaf.stalk targetPoint) target.functionField
      source.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Ring.KrullDimLE 1 (target.presheaf.stalk targetPoint) :=
    krullDimLE_of_coheight_le targetCoheight.le
  have : Finite (MaximalSpectrum modelRing) :=
    Ring.finite_maximalSpectrum_of_finite (baseRing := target.presheaf.stalk targetPoint)
  have fiberFinite : (morphism.base ⁻¹' {targetPoint}).Finite := by
    have fiberTypeFinite : Finite {point : source // morphism.base point = targetPoint} :=
      Finite.of_equiv _ fiberEquivalence
    exact Set.finite_coe_iff.mp fiberTypeFinite
  have : Module.Finite target.functionField source.functionField :=
    Module.Finite.of_isLocalization (target.presheaf.stalk targetPoint) modelRing
      (nonZeroDivisors (target.presheaf.stalk targetPoint))
  let fiberOrder : source.functionField → ℤ := fun element =>
    ∑ᶠ point ∈ morphism.base ⁻¹' {targetPoint},
      source.ord element point * (morphism.residueDegree point : ℤ)
  have fiberOrderMul : ∀ first second : source.functionField, first ≠ 0 → second ≠ 0 →
      fiberOrder (first * second) = fiberOrder first + fiberOrder second := by
    intro first second firstNonzero secondNonzero
    dsimp only [fiberOrder]
    rw [← finsum_mem_add_distrib fiberFinite]
    refine finsum_mem_congr rfl fun point _ => ?_
    rw [Scheme.ord_mul firstNonzero secondNonzero, add_mul]
  have normNonzero : ∀ element : source.functionField, element ≠ 0 →
      Algebra.norm target.functionField element ≠ 0 := fun element elementNonzero =>
    (Algebra.norm_ne_zero_iff (R := target.functionField)).mpr elementNonzero
  have normOrderMul : ∀ first second : source.functionField, first ≠ 0 → second ≠ 0 →
      target.ord (Algebra.norm target.functionField (first * second)) targetPoint =
        target.ord (Algebra.norm target.functionField first) targetPoint +
          target.ord (Algebra.norm target.functionField second) targetPoint := by
    intro first second firstNonzero secondNonzero
    rw [map_mul, Scheme.ord_mul (normNonzero first firstNonzero)
      (normNonzero second secondNonzero)]
  have integralOrder : ∀ element : modelRing, element ≠ 0 →
      fiberOrder (algebraMap modelRing source.functionField element) =
        target.ord (Algebra.norm target.functionField
          (algebraMap modelRing source.functionField element)) targetPoint := by
    intro element elementNonzero
    have imageNonzero : algebraMap modelRing source.functionField element ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective modelRing source.functionField)).mpr
        elementNonzero
    symm
    rw [Scheme.ord_eq_iff targetCoheight (normNonzero _ imageNonzero)]
    change Ring.ordFrac (target.presheaf.stalk targetPoint) _ = _
    rw [Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord element elementNonzero]
    change WithZero.exp _ = WithZero.exp _
    congr 1
    dsimp only [fiberOrder]
    have fiberSum :
        (∑ᶠ point ∈ morphism.base ⁻¹' {targetPoint},
          source.ord (algebraMap modelRing source.functionField element) point *
            (morphism.residueDegree point : ℤ)) =
        ∑ᶠ point : {point : source // morphism.base point = targetPoint},
          source.ord (algebraMap modelRing source.functionField element) point.1 *
            (morphism.residueDegree point.1 : ℤ) :=
      (finsum_subtype_eq_finsum_cond
        (fun point : source => morphism.base point = targetPoint)).symm
    rw [fiberSum, ← finsum_comp_equiv fiberEquivalence]
    refine finsum_congr fun maximalPoint => ?_
    obtain ⟨_, residueComparison, orderComparison⟩ := modelComparison maximalPoint
    rw [orderComparison element elementNonzero, ← residueComparison, mul_comm]
  symm
  exact Ring.eq_of_mul_of_eq_on_algebraMap (extensionRing := modelRing)
    (firstOrder := fiberOrder)
    (secondOrder := fun element => target.ord (Algebra.norm target.functionField element) targetPoint)
    fiberOrderMul normOrderMul integralOrder rationalNonzero

end AlgebraicGeometry
