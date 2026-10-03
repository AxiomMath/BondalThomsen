module

public import BondalThomsen.Ports.MiyaokaMori.Nef.PrincipalCartierDivisor
public import BondalThomsen.Ports.MiyaokaMori.Nef.StalkRegularOrder

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Intersection
open scoped Classical BigOperators

universe u

noncomputable section

namespace AlgebraicGeometry.Intersection.CartierLocalData

section Local

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]

def IsRegular (datum : CartierLocalData scheme) : Prop :=
  ∀ chart, ∀ (nonempty : Nonempty (datum.opens chart)),
    letI : Nonempty (datum.opens chart) := nonempty
    ∃ sectionValue : Γ(scheme, datum.opens chart),
      scheme.germToFunctionField (datum.opens chart) sectionValue = datum.equation chart

theorem IsRegular.coefficient_nonneg {datum : CartierLocalData scheme}
    (regular : datum.IsRegular) (point : scheme) : 0 ≤ datum.coefficient point := by
  let chart := datum.indexAt point
  have contains : point ∈ datum.opens chart := datum.indexAt_mem point
  let : Nonempty (datum.opens chart) := ⟨⟨point, contains⟩⟩
  obtain ⟨sectionValue, equation⟩ := regular chart inferInstance
  have sectionNonzero : sectionValue ≠ 0 := by
    intro zero
    apply datum.equation_ne_zero chart
    rw [← equation, zero, map_zero]
  rw [datum.coefficient_eq_ord_of_mem point chart contains, ← equation]
  exact AlgebraicGeometry.Divisors.StalkRegularOrder.ord_germToFunctionField_nonneg
    sectionNonzero contains

theorem coefficient_eq_of_unit_related_local_equations (first second : CartierLocalData scheme)
    (related : ∀ point : scheme, ∃ firstChart : first.index, ∃ secondChart : second.index,
      point ∈ first.opens firstChart ∧ point ∈ second.opens secondChart ∧
        IsUnitRatioOn (first.opens firstChart ⊓ second.opens secondChart)
          (first.equation firstChart) (second.equation secondChart)) :
    first.coefficient = second.coefficient := by
  funext point
  obtain ⟨firstChart, secondChart, firstContains, secondContains, unitRatio⟩ := related point
  let : Nonempty ↑(first.opens firstChart ⊓ second.opens secondChart) :=
    ⟨⟨point, firstContains, secondContains⟩⟩
  obtain ⟨unitSection, unitProof, ratioEquation⟩ := unitRatio inferInstance
  have unitOrder : scheme.ord (first.equation firstChart / second.equation secondChart) point = 0 := by
    rw [← ratioEquation]
    exact Scheme.ord_of_isUnit unitProof ⟨firstContains, secondContains⟩
  rw [first.coefficient_eq_ord_of_mem point firstChart firstContains,
    second.coefficient_eq_ord_of_mem point secondChart secondContains]
  calc
    scheme.ord (first.equation firstChart) point =
        scheme.ord ((first.equation firstChart / second.equation secondChart) *
          second.equation secondChart) point := by
      rw [div_mul_cancel₀ _ (second.equation_ne_zero secondChart)]
    _ = scheme.ord (first.equation firstChart / second.equation secondChart) point +
        scheme.ord (second.equation secondChart) point :=
      Scheme.ord_mul (div_ne_zero (first.equation_ne_zero firstChart)
        (second.equation_ne_zero secondChart)) (second.equation_ne_zero secondChart)
    _ = scheme.ord (second.equation secondChart) point := by rw [unitOrder, zero_add]

end Local

variable {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
  [IsIntegral scheme] [IsNoetherian scheme]

def degreeOver (datum : CartierLocalData scheme)
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) : ℤ :=
  rawZeroCycleDegree structureMap (datum.zeroCycle dimensionBound)

theorem degreeOver_nonneg_of_regular (datum : CartierLocalData scheme)
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (regular : datum.IsRegular) :
    0 ≤ datum.degreeOver structureMap dimensionBound :=
  rawZeroCycleDegree_nonneg_of_nonneg structureMap (datum.zeroCycle dimensionBound)
    regular.coefficient_nonneg

end AlgebraicGeometry.Intersection.CartierLocalData

namespace IntegralCurve

variable {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
  [scheme.Over (Spec (CommRingCat.of baseField))]

instance noetherianCarrier (curve : IntegralCurve baseField scheme) : IsNoetherian curve.carrier :=
  curve.carrier_isNoetherian

end IntegralCurve
