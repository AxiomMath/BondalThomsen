module

public import BondalThomsen.Toric.RankOne.NefCriterion
public import BondalThomsen.Toric.Positivity.SemiampleClassCriterion

@[expose] public section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module
open TauCeti.Toric
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

theorem hasGloballyGeneratedPower_iff_invertibleSheafSemiample {scheme : Scheme}
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    HasGloballyGeneratedPower bundle ↔ InvertibleSheafSemiample bundle := by
  constructor
  · rintro ⟨exponent, positive, powerBundle, same_class, generators⟩
    refine ⟨exponent, positive, ?_⟩
    have actual_class : TauCeti.AlgebraicGeometry.LineBundleClass.mk powerBundle =
        TauCeti.AlgebraicGeometry.LineBundleClass.mk (invertibleSheafTensorPower bundle exponent) :=
      same_class.trans (invertibleSheafTensorPower_class bundle exponent).symm
    obtain ⟨comparison⟩ := TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mp actual_class
    exact (SheafOfModules.GeneratingSections.equivOfIso comparison).nonempty_congr.mp generators
  · rintro ⟨exponent, positive, generators⟩
    exact ⟨exponent, positive, invertibleSheafTensorPower bundle exponent,
      invertibleSheafTensorPower_class bundle exponent, generators⟩

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem rankOne_invariantDivisorLineBundleSemiample_iff_coefficientDegree_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    BondalThomsen.InvertibleSheafSemiample (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) ↔
      0 ≤ fan.rankOneDivisorCoefficientDegree complete regular basis divisor :=
  (BondalThomsen.hasGloballyGeneratedPower_iff_invertibleSheafSemiample _).symm.trans
    (fan.rankOne_invariantDivisor_hasGloballyGeneratedPower_iff_coefficientDegree_nonnegative 𝕜
      complete regular basis divisor)

end TauCeti.Toric.Fan
