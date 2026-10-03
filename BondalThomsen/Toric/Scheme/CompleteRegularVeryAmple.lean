module

public import BondalThomsen.Toric.Scheme.CompleteRegularProperness
public import BondalThomsen.Toric.Positivity.VeryAmpleLineBundle
public import BondalThomsen.Toric.Projective.AllSectionPullbackSheafIso

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem allSectionProjectiveMonomialMap_isProper
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor) :
    IsProper (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support) := by
  let := fan.complete_regular_structureMap_isProper 𝕜 complete regular
  let := fan.allSectionProjectiveSpace_structureMap_isProper 𝕜 complete regular divisor
  have composite_proper : IsProper
      (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support ≫
        BondalThomsen.polynomialProjStructureMap 𝕜 (fan.globalDivisorSectionExponents divisor)) := by
    rw [fan.allSectionProjectiveMonomialMap_structureMap 𝕜 complete regular divisor support]
    infer_instance
  let := composite_proper
  exact IsProper.of_comp
    (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
    (BondalThomsen.polynomialProjStructureMap 𝕜 (fan.globalDivisorSectionExponents divisor))

theorem allSectionProjectiveMonomialMap_isClosedImmersion_of_isImmersion
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)
    (immersion : IsImmersion (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)) :
    IsClosedImmersion (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support) := by
  let := immersion
  let := fan.allSectionProjectiveMonomialMap_isProper 𝕜 complete regular divisor support
  exact IsClosedImmersion.of_isPreimmersion _ (Scheme.Hom.isClosedMap _).isClosed_range

theorem strictSupport_allSectionProjectiveMonomialMap_large_multiples_isClosedImmersion
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis), fan.BasisDivisorStrictSupport basis cone_basis divisor) :
    ∃ threshold : ℕ, 0 < threshold ∧ ∀ multiple : ℕ, threshold ≤ multiple →
      ∃ support : fan.HasRaySupportInequalities (multiple • divisor),
        IsClosedImmersion (fan.allSectionProjectiveMonomialMap 𝕜 complete regular
          (multiple • divisor) support) := by
  obtain ⟨threshold, positive, immersions⟩ :=
    fan.strictSupport_allSectionProjectiveMonomialMap_large_multiples_isImmersion 𝕜
      complete regular divisor strict_support
  refine ⟨threshold, positive, ?_⟩
  intro multiple large
  obtain ⟨support, immersion⟩ := immersions multiple large
  exact ⟨support, fan.allSectionProjectiveMonomialMap_isClosedImmersion_of_isImmersion 𝕜
    complete regular (multiple • divisor) support immersion⟩

theorem divisor_large_multiples_veryAmple_of_strictSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis), fan.BasisDivisorStrictSupport basis cone_basis divisor) :
    ∃ threshold : ℕ, 0 < threshold ∧ ∀ multiple : ℕ, threshold ≤ multiple →
      BondalThomsen.VeryAmpleOverField 𝕜 (fan.structureMap 𝕜 regular)
        (fan.invariantDivisorLineBundle 𝕜 complete regular (multiple • divisor)) := by
  obtain ⟨threshold, positive, embeddings⟩ :=
    fan.strictSupport_allSectionProjectiveMonomialMap_large_multiples_isClosedImmersion 𝕜
      complete regular divisor strict_support
  refine ⟨threshold, positive, ?_⟩
  intro multiple large
  obtain ⟨support, closed⟩ := embeddings multiple large
  let : Finite (fan.globalDivisorSectionExponents (multiple • divisor)) :=
    (fan.globalDivisorSectionExponents_finite complete regular (multiple • divisor)).to_subtype
  exact BondalThomsen.veryAmpleOverField_of_closedImmersion 𝕜 (fan.structureMap 𝕜 regular)
    (fan.invariantDivisorLineBundle 𝕜 complete regular (multiple • divisor))
    (fan.globalDivisorSectionExponents (multiple • divisor))
    (fan.allSectionProjectiveMonomialMap 𝕜 complete regular (multiple • divisor) support) closed
    (fan.allSectionProjectiveMonomialMap_structureMap 𝕜 complete regular (multiple • divisor) support)
    ⟨fan.allSectionProjectiveMonomialMap_pullback_degreeOneIso 𝕜
      complete regular (multiple • divisor) support⟩

theorem divisor_hasVeryAmplePower_of_strictSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis), fan.BasisDivisorStrictSupport basis cone_basis divisor) :
    BondalThomsen.HasVeryAmplePowerOverField 𝕜 (fan.structureMap 𝕜 regular)
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) := by
  obtain ⟨threshold, positive, multiples⟩ :=
    fan.divisor_large_multiples_veryAmple_of_strictSupport 𝕜 complete regular divisor strict_support
  exact ⟨threshold, positive, fan.invariantDivisorLineBundle 𝕜 complete regular (threshold • divisor),
    fan.invariantDivisorLineBundleClass_nsmul 𝕜 complete regular divisor threshold,
    multiples threshold le_rfl⟩

theorem raySum_hasVeryAmplePower_of_strictAnticanonicalSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (strict_support : fan.HasStrictAnticanonicalConeSupport) :
    BondalThomsen.HasVeryAmplePowerOverField 𝕜 (fan.structureMap 𝕜 regular)
      (fan.invariantDivisorLineBundle 𝕜 complete regular fan.anticanonicalRayDivisor) := by
  apply fan.divisor_hasVeryAmplePower_of_strictSupport 𝕜 complete regular fan.anticanonicalRayDivisor
  intro dimension basis cone_basis ray outside
  simpa only [fan.anticanonicalRayDivisor_apply, fan.coneDivisorCharacter_anticanonical] using
    strict_support dimension basis cone_basis ray outside

end TauCeti.Toric.Fan
