module

public import BondalThomsen.Toric.Scheme.CompleteRegularVeryAmple
public import BondalThomsen.ProjectiveBundle.Scheme
public import BondalThomsen.ProjectiveBundle.Support

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BondalThomsen.ProjectiveBundle

variable {rows baseDimension columns : ℕ}

theorem schemeStructureMap_isProper (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    IsProper (schemeStructureMap 𝕜 (baseDimension := baseDimension) matrix) :=
  (fan (baseDimension := baseDimension) matrix).complete_regular_structureMap_isProper 𝕜
    (fan_isComplete (baseDimension := baseDimension) matrix)
    (fan_isRegular (baseDimension := baseDimension) matrix)

theorem schemeRaySum_hasVeryAmplePower_of_strictAnticanonicalSupport
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (strict_support : (fan (baseDimension := baseDimension) matrix).HasStrictAnticanonicalConeSupport) :
    HasVeryAmplePowerOverField 𝕜 (schemeStructureMap 𝕜 (baseDimension := baseDimension) matrix)
      (schemeInvariantDivisorLineBundle 𝕜 (baseDimension := baseDimension) matrix
        (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor) :=
  (fan (baseDimension := baseDimension) matrix).raySum_hasVeryAmplePower_of_strictAnticanonicalSupport 𝕜
    (fan_isComplete (baseDimension := baseDimension) matrix)
    (fan_isRegular (baseDimension := baseDimension) matrix) strict_support

theorem schemeRaySum_large_multiples_projectiveClosedImmersion
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (strict_support : (fan (baseDimension := baseDimension) matrix).HasStrictAnticanonicalConeSupport) :
    ∃ threshold : ℕ, 0 < threshold ∧ ∀ multiple : ℕ, threshold ≤ multiple →
      ∃ support : (fan (baseDimension := baseDimension) matrix).HasRaySupportInequalities
          (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor),
        Finite ((fan (baseDimension := baseDimension) matrix).globalDivisorSectionExponents
          (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor)) ∧
        IsClosedImmersion ((fan (baseDimension := baseDimension) matrix).allSectionProjectiveMonomialMap 𝕜
          (fan_isComplete (baseDimension := baseDimension) matrix)
          (fan_isRegular (baseDimension := baseDimension) matrix)
          (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor) support) ∧
        (fan (baseDimension := baseDimension) matrix).allSectionProjectiveMonomialMap 𝕜
            (fan_isComplete (baseDimension := baseDimension) matrix)
            (fan_isRegular (baseDimension := baseDimension) matrix)
            (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor) support ≫
          polynomialProjStructureMap 𝕜 ((fan (baseDimension := baseDimension) matrix).globalDivisorSectionExponents
            (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor)) =
              schemeStructureMap 𝕜 (baseDimension := baseDimension) matrix ∧
        Nonempty ((Scheme.Modules.pullback
          ((fan (baseDimension := baseDimension) matrix).allSectionProjectiveMonomialMap 𝕜
            (fan_isComplete (baseDimension := baseDimension) matrix)
            (fan_isRegular (baseDimension := baseDimension) matrix)
            (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor)
            support)).obj (polynomialProjDegreeOneSheaf 𝕜
              ((fan (baseDimension := baseDimension) matrix).globalDivisorSectionExponents
                (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor))) ≅
          (schemeInvariantDivisorLineBundle 𝕜 (baseDimension := baseDimension) matrix
            (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor)).obj) := by
  have divisor_strict : ∀ dimension (basis : Basis (Fin dimension) ℤ
      (Lattice rows baseDimension columns))
      (cone_basis : (fan (baseDimension := baseDimension) matrix).IsConeBasis basis),
      (fan (baseDimension := baseDimension) matrix).BasisDivisorStrictSupport basis cone_basis
        (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor := by
    intro dimension basis cone_basis ray outside
    simpa only [(fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor_apply,
      (fan (baseDimension := baseDimension) matrix).coneDivisorCharacter_anticanonical] using
        strict_support dimension basis cone_basis ray outside
  obtain ⟨threshold, positive, embeddings⟩ :=
    (fan (baseDimension := baseDimension) matrix).strictSupport_allSectionProjectiveMonomialMap_large_multiples_isClosedImmersion 𝕜
      (fan_isComplete (baseDimension := baseDimension) matrix)
      (fan_isRegular (baseDimension := baseDimension) matrix)
      (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor divisor_strict
  refine ⟨threshold, positive, ?_⟩
  intro multiple large
  obtain ⟨support, closed⟩ := embeddings multiple large
  exact ⟨support, (fan (baseDimension := baseDimension) matrix).allDivisorMonomialCharacters_finite
    (fan_isComplete (baseDimension := baseDimension) matrix)
    (fan_isRegular (baseDimension := baseDimension) matrix)
    (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor),
    closed, (fan (baseDimension := baseDimension) matrix).allSectionProjectiveMonomialMap_structureMap 𝕜
      (fan_isComplete (baseDimension := baseDimension) matrix)
      (fan_isRegular (baseDimension := baseDimension) matrix)
      (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor) support,
    ⟨(fan (baseDimension := baseDimension) matrix).allSectionProjectiveMonomialMap_pullback_degreeOneIso 𝕜
      (fan_isComplete (baseDimension := baseDimension) matrix)
      (fan_isRegular (baseDimension := baseDimension) matrix)
      (multiple • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor) support⟩⟩

theorem scheme_projectiveClosedEmbedding_of_strictAnticanonicalSupport
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (strict_support : (fan (baseDimension := baseDimension) matrix).HasStrictAnticanonicalConeSupport) :
    ∃ Index : Type, Finite Index ∧
      ∃ closed_map : scheme 𝕜 (baseDimension := baseDimension) matrix ⟶
          Proj (MvPolynomial.homogeneousSubmodule Index 𝕜),
        IsClosedImmersion closed_map ∧
          closed_map ≫ polynomialProjStructureMap 𝕜 Index =
            schemeStructureMap 𝕜 (baseDimension := baseDimension) matrix := by
  obtain ⟨threshold, _, embeddings⟩ :=
    schemeRaySum_large_multiples_projectiveClosedImmersion 𝕜 (baseDimension := baseDimension) matrix strict_support
  obtain ⟨support, finite, closed, over_base, _⟩ := embeddings threshold le_rfl
  exact ⟨(fan (baseDimension := baseDimension) matrix).globalDivisorSectionExponents
    (threshold • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor),
    finite, (fan (baseDimension := baseDimension) matrix).allSectionProjectiveMonomialMap 𝕜
      (fan_isComplete (baseDimension := baseDimension) matrix)
      (fan_isRegular (baseDimension := baseDimension) matrix)
      (threshold • (fan (baseDimension := baseDimension) matrix).anticanonicalRayDivisor) support, closed, over_base⟩

theorem fixedWeight_schemeRaySum_hasVeryAmplePower {ones : ℕ}
    (matrix : FixedWeightMatrix rows columns ones)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns) (weight_bound : ones ≤ baseDimension) :
    HasVeryAmplePowerOverField 𝕜 (schemeStructureMap 𝕜 (baseDimension := baseDimension) (fixedWeightTwist matrix))
      (schemeInvariantDivisorLineBundle 𝕜 (baseDimension := baseDimension) (fixedWeightTwist matrix)
        (fan (baseDimension := baseDimension) (fixedWeightTwist matrix)).anticanonicalRayDivisor) :=
  schemeRaySum_hasVeryAmplePower_of_strictAnticanonicalSupport 𝕜 (baseDimension := baseDimension)
    (fixedWeightTwist matrix)
    (fixedWeight_hasStrictAnticanonicalConeSupport matrix base_positive fiber_positive weight_bound)

theorem paperFamily_projectiveClosedEmbedding
    (matrix : FixedWeightMatrix rows columns baseDimension)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns) :
    ∃ Index : Type, Finite Index ∧
      ∃ closed_map : scheme 𝕜 (baseDimension := baseDimension) (fixedWeightTwist matrix) ⟶
          Proj (MvPolynomial.homogeneousSubmodule Index 𝕜),
        IsClosedImmersion closed_map ∧ closed_map ≫ polynomialProjStructureMap 𝕜 Index =
          schemeStructureMap 𝕜 (baseDimension := baseDimension) (fixedWeightTwist matrix) :=
  scheme_projectiveClosedEmbedding_of_strictAnticanonicalSupport 𝕜 (baseDimension := baseDimension)
    (fixedWeightTwist matrix)
    (paperFamily_hasStrictAnticanonicalConeSupport matrix base_positive fiber_positive)

end BondalThomsen.ProjectiveBundle
