module

public import BondalThomsen.Toric.Canonical.RaySumConsequences
public import BondalThomsen.ProjectiveBundle.ParameterProjectivity
public import BondalThomsen.Toric.Divisor.PicardEquivalence
public import BondalThomsen.ProjectiveBundle.Scheme
public import BondalThomsen.ProjectiveBundle.NefSupport
public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Toric.Positivity.GlobalGenerationCriterion
public import BondalThomsen.ProjectiveBundle.ConeRigidity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Filter Real
open TauCeti.AlgebraicGeometry
open scoped Topology

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BondalThomsen.ProjectiveBundle

variable {rows columns ones : ℕ}

theorem paperFamily_inverseCanonicalClass_isAmple
    (matrix : FixedWeightMatrix rows columns ones)
    (basePositive : 0 < ones) (fiberPositive : 0 < columns) :
    let bundleFan := fan (baseDimension := ones) (fixedWeightTwist matrix)
    letI := bundleFan.algebraicRealization_isIntegral 𝕜 (fan_isRegular _)
      (bundleFan.completeFan_nonemptyCones (fan_isComplete _))
    SchemeLineBundleClassAmple ((bundleFan.toricCanonicalLineBundleClass 𝕜
      (fan_isComplete _) (fan_isRegular _))⁻¹) :=
  ((fan (baseDimension := ones) (fixedWeightTwist matrix)).toricCanonicalInverseClass_isAmple_iff_raySum 𝕜
    (fan_isComplete _) (fan_isRegular _)).mpr
      (paperFamily_schemeRaySum_isAmple 𝕜 matrix basePositive fiberPositive)

theorem parameterScheme_inverseCanonicalClass_isAmple (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension))
    (basePositive : 0 < familyWeight dimension) (fiberPositive : 0 < familyColumns dimension) :
    let bundleFan := fan (baseDimension := familyWeight dimension) (fixedWeightTwist matrix)
    letI := bundleFan.algebraicRealization_isIntegral 𝕜 (fan_isRegular _)
      (bundleFan.completeFan_nonemptyCones (fan_isComplete _))
    SchemeLineBundleClassAmple ((bundleFan.toricCanonicalLineBundleClass 𝕜
      (fan_isComplete _) (fan_isRegular _))⁻¹) :=
  paperFamily_inverseCanonicalClass_isAmple 𝕜 matrix basePositive fiberPositive

end BondalThomsen.ProjectiveBundle
