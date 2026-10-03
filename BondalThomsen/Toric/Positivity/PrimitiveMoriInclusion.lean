module

public import BondalThomsen.Toric.Positivity.RealPrimitivePairings
public import BondalThomsen.Toric.Positivity.PrimitiveConeMoriCriterion

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

noncomputable section

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance primitiveInclusionRayFintype (fan : Fan embedding) : Fintype fan.Ray :=
  Fintype.ofFinite fan.Ray

variable {𝕜} in
local instance primitiveInclusionBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

theorem PrimitiveLatticeRelation.realRayNumericalEvaluation_eq
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    fan.realRayNumericalEvaluation 𝕜 complete regular
        (relation.numericalClass 𝕜 complete regular projective) = relation.realRayPairing := by
  classical
  apply (Pi.basisFun ℝ fan.Ray).ext
  intro ray
  rw [Pi.basisFun_apply]
  change (∑ selected : fan.Ray, (Pi.single ray (1 : ℝ) : fan.Ray → ℝ) selected *
    (relation.numericalClass 𝕜 complete regular projective).val
      (fan.numericalRayPicardClass 𝕜 complete regular selected)) = _
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  change (relation.numericalClass 𝕜 complete regular projective).val
    (fan.invariantDivisorPicardRealization 𝕜 complete regular
      (fan.invariantRayDivisorClass (Finsupp.single ray 1))) = _
  rw [relation.numericalClass_realization 𝕜, relation.classPairing_mk]
  have castSingle : (fun selected : fan.Ray =>
      ((Finsupp.single ray (1 : ℤ) : fan.InvariantRayDivisor) selected : ℝ)) =
      Pi.single ray 1 := by
    funext selected
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [← relation.realRayPairing_integral, castSingle]

theorem integralCurveNumericalClass_mem_primitiveNumericalCone
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    BondalThomsen.integralCurveNumericalClass curve ∈
      fan.primitiveNumericalCone 𝕜 complete regular projective := by
  apply (fan.primitiveNumericalCone_bipolar 𝕜 complete regular projective _).mpr
  intro values nonnegative
  apply fan.realRayCoefficients_nonnegative_on_integralCurve_of_primitivePairings 𝕜
    complete regular projective values _ curve
  intro left right relation
  have paired := nonnegative (relation.numericalClass 𝕜 complete regular projective)
    (relation.numericalClass_mem_primitiveNumericalCone 𝕜 complete regular projective)
  change 0 ≤ fan.realRayNumericalEvaluation 𝕜 complete regular
    (relation.numericalClass 𝕜 complete regular projective) values at paired
  rw [relation.realRayNumericalEvaluation_eq 𝕜 complete regular projective] at paired
  exact paired

theorem moriCone_le_primitiveNumericalCone
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) ≤
      fan.primitiveNumericalCone 𝕜 complete regular projective :=
  fan.moriCone_le_primitiveNumericalCone_of_integralCurves 𝕜 complete regular projective
    (fan.integralCurveNumericalClass_mem_primitiveNumericalCone 𝕜 complete regular projective)

end

end TauCeti.Toric.Fan
