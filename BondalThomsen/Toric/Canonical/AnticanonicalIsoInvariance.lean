module

public import BondalThomsen.Toric.Canonical.BaseIso
public import BondalThomsen.Toric.Canonical.FanChartRestriction
public import BondalThomsen.Toric.Frobenius.MultiplicationFiniteLocallyFree
public import BondalThomsen.Toric.Scheme.Integral
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Adjunction.Limits
public import BondalThomsen.LineBundle.SchemePicardGlobalGeneration
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import BondalThomsen.ProjectiveBundle.SchemeAsymptoticLower

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {SourceLattice TargetLattice SourceAmbient TargetAmbient : Type}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    [FiniteDimensional ℝ SourceAmbient] [FiniteDimensional ℝ TargetAmbient]
    {sourceEmbedding : SourceLattice →+ SourceAmbient}
    {targetEmbedding : TargetLattice →+ TargetAmbient}

theorem invariantDivisorPicardClass_neg (fan : Fan sourceEmbedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    Additive.ofMul (TauCeti.AlgebraicGeometry.LineBundleClass.mk
      (fan.invariantDivisorLineBundle 𝕜 complete regular (-divisor))) =
        -Additive.ofMul (TauCeti.AlgebraicGeometry.LineBundleClass.mk
          (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  rw [← fan.invariantDivisorPicardRealization_apply 𝕜 complete regular (-divisor),
    ← fan.invariantDivisorPicardRealization_apply 𝕜 complete regular divisor,
    map_neg, map_neg]

end TauCeti.Toric.Fan

