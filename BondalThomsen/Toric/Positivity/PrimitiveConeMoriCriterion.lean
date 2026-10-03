module

public import BondalThomsen.Toric.Positivity.PrimitiveNumericalCone

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

variable {𝕜} in
local instance primitiveMoriBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

theorem moriCone_le_primitiveNumericalCone_of_integralCurves
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (curves : ∀ curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular),
      BondalThomsen.integralCurveNumericalClass curve ∈
        fan.primitiveNumericalCone 𝕜 complete regular projective) :
    BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) ≤
      fan.primitiveNumericalCone 𝕜 complete regular projective := by
  have hullIncluded : PointedCone.hull ℝ
      (Set.range (BondalThomsen.integralCurveNumericalClass
        (baseField := 𝕜) (scheme := fan.algebraicRealization 𝕜 regular))) ≤
      fan.primitiveNumericalCone 𝕜 complete regular projective := by
    apply Submodule.span_le.mpr
    rintro numericalClass ⟨curve, rfl⟩
    exact curves curve
  exact (fan.primitiveNumericalCone_isClosed 𝕜 complete regular projective).closure_subset_iff.mpr
    hullIncluded

theorem primitiveNumericalCone_le_moriCone_of_primitiveClasses
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (primitiveClasses : ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      relation.numericalClass 𝕜 complete regular projective ∈
        BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    fan.primitiveNumericalCone 𝕜 complete regular projective ≤
      BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) := by
  apply Submodule.span_le.mpr
  rintro numericalClass ⟨⟨left, right, relation⟩, rfl⟩
  exact primitiveClasses left right relation

theorem invariantClass_isNef_iff_extremalPrimitivePairings_of_moriCone_eq
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (generation : BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) =
      fan.primitiveNumericalCone 𝕜 complete regular projective)
    (divisorClass : fan.InvariantRayDivisorClass) :
    BondalThomsen.SchemeLineBundleClassIsNef (baseField := 𝕜)
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass)) ↔
      ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
        relation.IsMoriExtremal 𝕜 complete regular → 0 ≤ relation.classPairing divisorClass := by
  constructor
  · intro nef left right relation extremal
    exact relation.classPairing_nonnegative_of_isMoriExtremal 𝕜
      complete regular extremal divisorClass nef
  · intro pairings
    apply (BondalThomsen.schemeLineBundleClassIsNef_iff_moriCone_nonnegative _).mpr
    rw [generation]
    let evaluation := (LinearMap.proj
      (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass)).comp
        (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)).subtype
    change ∀ numericalClass ∈ fan.primitiveNumericalCone 𝕜 complete regular projective,
      0 ≤ evaluation numericalClass
    apply (BondalThomsen.FiniteConeExtremalGenerators.nonnegative_iff_on_extreme_generators
      (fan.primitiveNumericalGenerators_finite 𝕜 complete regular projective)
      (fan.primitiveNumericalCone_salient 𝕜 complete regular projective) evaluation).mpr
    rintro numericalClass ⟨⟨left, right, relation⟩, rfl⟩ nonzero face
    have actualExtremal : BondalThomsen.IsExtremalMoriClass
        (relation.numericalClass 𝕜 complete regular projective) := by
      refine ⟨nonzero, ?_⟩
      rw [generation]
      exact face
    have extremal := (relation.isMoriExtremal_iff_numericalClass 𝕜
      complete regular projective).mpr actualExtremal
    change 0 ≤ (relation.numericalClass 𝕜 complete regular projective).val
      (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass)
    rw [relation.numericalClass_realization 𝕜]
    exact_mod_cast pairings left right relation extremal

end

end TauCeti.Toric.Fan
