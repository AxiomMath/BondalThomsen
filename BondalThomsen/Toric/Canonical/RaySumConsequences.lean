module

public import BondalThomsen.Toric.Canonical.NegativeRaySumFinalDescent
public import BondalThomsen.Toric.Canonical.AmpleCriterion

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

theorem toricCanonicalLineBundleClass_eq_negativeRaySum
    (fan : Fan sourceEmbedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    fan.toricCanonicalLineBundleClass 𝕜 complete regular =
      LineBundleClass.mk (fan.invariantDivisorLineBundle 𝕜
        complete regular (-fan.anticanonicalRayDivisor)) :=
  LineBundleClass.mk_eq_mk_iff.mpr ⟨fan.toricCanonicalNegativeRaySumIso 𝕜 complete regular⟩

theorem toricCanonicalInverseClass_isAmple_iff_raySum
    (fan : Fan sourceEmbedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    BondalThomsen.SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹) ↔
      IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular fan.anticanonicalRayDivisor).obj :=
  fan.toricCanonicalInverseClass_isAmple_iff_raySum_of_canonical_comparison 𝕜 complete regular
    (fan.toricCanonicalLineBundleClass_eq_negativeRaySum 𝕜 complete regular)

end TauCeti.Toric.Fan
