module

public import BondalThomsen.Toric.Positivity.VeryAmpleToAmple
public import BondalThomsen.Toric.Scheme.CompleteRegularVeryAmple
public import BondalThomsen.Toric.RankOne.NefCriterion
public import BondalThomsen.ProjectiveBundle.ParameterProjectivity

@[expose] public section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module
open Filter Real
open scoped Topology

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem divisorLineBundle_isAmple_of_strictSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (strictSupport : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (coneBasis : fan.IsConeBasis basis), fan.BasisDivisorStrictSupport basis coneBasis divisor) :
    IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj := by
  let := fan.complete_regular_structureMap_isProper 𝕜 complete regular
  exact (fan.divisor_hasVeryAmplePower_of_strictSupport 𝕜 complete regular divisor
    strictSupport).isAmple_of_isProper 𝕜

end TauCeti.Toric.Fan

namespace BondalThomsen.ProjectiveBundle

variable {rows columns baseDimension : ℕ}

theorem fixedWeight_schemeRaySum_isAmple
    {weight : ℕ} (matrix : FixedWeightMatrix rows columns weight)
    (basePositive : 0 < baseDimension) (fiberPositive : 0 < columns)
    (weightBound : weight ≤ baseDimension) :
    IsAmple (schemeInvariantDivisorLineBundle 𝕜 (baseDimension := baseDimension)
      (fixedWeightTwist matrix)
      (fan (baseDimension := baseDimension) (fixedWeightTwist matrix)).anticanonicalRayDivisor).obj := by
  let := schemeStructureMap_isProper 𝕜 (baseDimension := baseDimension) (fixedWeightTwist matrix)
  exact (fixedWeight_schemeRaySum_hasVeryAmplePower 𝕜 (baseDimension := baseDimension)
    matrix basePositive fiberPositive weightBound).isAmple_of_isProper 𝕜

theorem paperFamily_schemeRaySum_isAmple
    (matrix : FixedWeightMatrix rows columns baseDimension)
    (basePositive : 0 < baseDimension) (fiberPositive : 0 < columns) :
    IsAmple (schemeInvariantDivisorLineBundle 𝕜 (baseDimension := baseDimension)
      (fixedWeightTwist matrix)
      (fan (baseDimension := baseDimension) (fixedWeightTwist matrix)).anticanonicalRayDivisor).obj :=
  fixedWeight_schemeRaySum_isAmple 𝕜 matrix basePositive fiberPositive le_rfl

end BondalThomsen.ProjectiveBundle
