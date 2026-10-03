module

public import BondalThomsen.Toric.Positivity.GenericStarDichotomy
public import BondalThomsen.Toric.Scheme.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Multiplicative

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

section ArbitraryValuationTorus

variable {ValuationRing FractionField : Type} [CommRing ValuationRing] [IsDomain ValuationRing]
    [_root_.ValuationRing ValuationRing] [Field FractionField]
    [Algebra ValuationRing FractionField] [IsFractionRing ValuationRing FractionField]

noncomputable def valuationChartCharacterLift (fan : Fan embedding)
    (characters : Multiplicative (Lattice →+ ℤ) →* FractionField) (cone : fan.cones)
    (integral : ∀ character : dualSemigroup fan.lattice cone.val,
      IsLocalization.IsInteger ValuationRing (characters (ofAdd character.val))) :
    Multiplicative (dualSemigroup fan.lattice cone.val) →* ValuationRing where
  toFun exponent := (integral (toAdd exponent)).choose
  map_one' := by
    apply IsFractionRing.injective ValuationRing FractionField
    rw [(integral 0).choose_spec, map_one]
    exact characters.map_one
  map_mul' first second := by
    apply IsFractionRing.injective ValuationRing FractionField
    change algebraMap ValuationRing FractionField (integral (toAdd first + toAdd second)).choose =
      algebraMap ValuationRing FractionField
        ((integral (toAdd first)).choose * (integral (toAdd second)).choose)
    rw [(integral (toAdd first + toAdd second)).choose_spec, map_mul,
      (integral (toAdd first)).choose_spec, (integral (toAdd second)).choose_spec]
    exact characters.map_mul _ _

omit [IsDomain ValuationRing] [_root_.ValuationRing ValuationRing] in
theorem valuationChartCharacterLift_algebraMap (fan : Fan embedding)
    (characters : Multiplicative (Lattice →+ ℤ) →* FractionField) (cone : fan.cones)
    (integral : ∀ character : dualSemigroup fan.lattice cone.val,
      IsLocalization.IsInteger ValuationRing (characters (ofAdd character.val)))
    (exponent : Multiplicative (dualSemigroup fan.lattice cone.val)) :
    algebraMap ValuationRing FractionField
      (fan.valuationChartCharacterLift characters cone integral exponent) =
        characters (ofAdd (toAdd exponent).val) :=
  (integral (toAdd exponent)).choose_spec

end ArbitraryValuationTorus

end TauCeti.Toric.Fan
