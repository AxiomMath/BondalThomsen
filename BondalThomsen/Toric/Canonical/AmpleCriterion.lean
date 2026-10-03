module

public import BondalThomsen.LineBundle.AmpleLineBundleSchemeIso
public import BondalThomsen.Toric.Positivity.StrictSupportAmple
public import BondalThomsen.Toric.Canonical.AnticanonicalIsoInvariance

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {SourceLattice TargetLattice SourceAmbient TargetAmbient : Type}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    [FiniteDimensional ℝ SourceAmbient] [FiniteDimensional ℝ TargetAmbient]
    {sourceEmbedding : SourceLattice →+ SourceAmbient}
    {targetEmbedding : TargetLattice →+ TargetAmbient}

theorem toricCanonicalInverseClass_isAmple_iff_raySum_of_canonical_comparison
    (fan : Fan sourceEmbedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (canonicalComparison : fan.toricCanonicalLineBundleClass 𝕜 complete regular =
      LineBundleClass.mk (fan.invariantDivisorLineBundle 𝕜
        complete regular (-fan.anticanonicalRayDivisor))) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    BondalThomsen.SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹) ↔
      IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular fan.anticanonicalRayDivisor).obj := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  have negative := fan.invariantDivisorPicardClass_neg 𝕜 complete regular fan.anticanonicalRayDivisor
  have inverseClass : LineBundleClass.mk (fan.invariantDivisorLineBundle 𝕜
      complete regular (-fan.anticanonicalRayDivisor)) =
      (LineBundleClass.mk (fan.invariantDivisorLineBundle 𝕜
        complete regular fan.anticanonicalRayDivisor))⁻¹ :=
    congrArg Additive.toMul negative
  rw [canonicalComparison, inverseClass, inv_inv,
    BondalThomsen.schemeLineBundleClassAmple_mk_iff]

end TauCeti.Toric.Fan
