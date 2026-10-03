module

public import BondalThomsen.Ports.MiyaokaMori.Nef.IntegralCurve
public import BondalThomsen.Ports.MiyaokaMori.Nef.ZeroCycleDegreePositivity

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Intersection

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicCycle

def degreeAddHom {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    [scheme.Over (Spec (CommRingCat.of baseField))]
    [IsProper (scheme ↘ Spec (CommRingCat.of baseField))] :
    AlgebraicCycle scheme ℤ →+ ℤ where
  toFun := degree (baseField := baseField)
  map_zero' := degree_zero
  map_add' := degree_add

@[simp] theorem degreeAddHom_apply {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    [scheme.Over (Spec (CommRingCat.of baseField))]
    [IsProper (scheme ↘ Spec (CommRingCat.of baseField))] (cycle : AlgebraicCycle scheme ℤ) :
    degreeAddHom (baseField := baseField) cycle = degree (baseField := baseField) cycle :=
  rfl

end AlgebraicGeometry.AlgebraicCycle

namespace IntegralCurve

variable {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
  [scheme.Over (Spec (CommRingCat.of baseField))]

instance properStructureMap (curve : IntegralCurve baseField scheme) :
    IsProper (curve.carrier ↘ Spec (CommRingCat.of baseField)) :=
  curve.isProperOver

theorem carrier_isNoetherian (curve : IntegralCurve baseField scheme) :
    IsNoetherian curve.carrier :=
  properFieldScheme_isNoetherian (curve.carrier ↘ Spec (CommRingCat.of baseField))

theorem cycle_finiteSupport (curve : IntegralCurve baseField scheme)
    (cycle : AlgebraicCycle curve.carrier ℤ) : (Function.support cycle).Finite :=
  properCycle_finiteSupport (curve.carrier ↘ Spec (CommRingCat.of baseField)) cycle

end IntegralCurve
