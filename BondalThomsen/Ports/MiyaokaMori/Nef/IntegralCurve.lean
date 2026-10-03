module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

def SchemeIsOneDimensional (scheme : Scheme.{u}) : Prop :=
  topologicalKrullDim scheme = 1

abbrev IsProperOver (baseField : Type u) [Field baseField] (scheme : Scheme.{u})
    [scheme.Over (Spec (CommRingCat.of baseField))] : Prop :=
  IsProper (scheme ↘ Spec (CommRingCat.of baseField))

structure IntegralCurve (baseField : Type u) [Field baseField] (scheme : Scheme.{u})
    [scheme.Over (Spec (CommRingCat.of baseField))] where
  carrier : Scheme.{u}
  ι : carrier ⟶ scheme
  [isClosedImmersion : IsClosedImmersion ι]
  [isIntegral : IsIntegral carrier]
  [isProper : IsProper (ι ≫ (scheme ↘ Spec (CommRingCat.of baseField)))]
  dim_eq_one : SchemeIsOneDimensional carrier

attribute [instance] IntegralCurve.isClosedImmersion IntegralCurve.isIntegral
  IntegralCurve.isProper

instance IntegralCurve.over {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    [scheme.Over (Spec (CommRingCat.of baseField))] (curve : IntegralCurve baseField scheme) :
    curve.carrier.Over (Spec (CommRingCat.of baseField)) :=
  ⟨curve.ι ≫ (scheme ↘ Spec (CommRingCat.of baseField))⟩

theorem IntegralCurve.isProperOver {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} [scheme.Over (Spec (CommRingCat.of baseField))]
    (curve : IntegralCurve baseField scheme) : IsProperOver baseField curve.carrier := by
  exact curve.isProper
