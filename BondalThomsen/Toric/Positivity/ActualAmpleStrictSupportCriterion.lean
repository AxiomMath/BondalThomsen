module

public import BondalThomsen.Toric.Positivity.AmpleNegativeTwistEvaluationDescent
public import BondalThomsen.Toric.Positivity.StrictSupportAmple
public import BondalThomsen.Toric.Canonical.RaySumConsequences

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def HasStrictRaySupportInequalities (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) : Prop :=
  ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (ray : fan.Ray),
      ray.val ∉ Set.range basis →
        -divisor ray < fan.coneDivisorCharacter basis cone_basis divisor ray.val

omit [FiniteDimensional ℝ Ambient] in
theorem hasRaySupportInequalities_of_strict
    (fan : Fan embedding) (divisor : fan.InvariantRayDivisor)
    (strict : fan.HasStrictRaySupportInequalities divisor) :
    fan.HasRaySupportInequalities divisor := by
  intro dimension basis cone_basis
  exact fan.basisDivisor_admissible_of_strictSupport basis cone_basis divisor
    (strict dimension basis cone_basis)

theorem invariantDivisor_isAmple_iff_strictRaySupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) :
    IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ↔
      fan.HasStrictRaySupportInequalities divisor := by
  constructor
  · intro ample dimension basis cone_basis
    exact fan.invariantDivisor_basisStrictSupport_of_isAmple 𝕜
      complete regular divisor ample basis cone_basis
  · intro strict
    exact fan.divisorLineBundle_isAmple_of_strictSupport 𝕜 complete regular divisor strict

theorem invertibleSheaf_isAmple_iff_representative_strictSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular))
    (divisor : fan.InvariantRayDivisor)
    (comparison : bundle.obj ≅ (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) :
    IsAmple bundle.obj ↔ fan.HasStrictRaySupportInequalities divisor :=
  (AlgebraicGeometry.isAmple_iff_of_iso comparison).trans
    (fan.invariantDivisor_isAmple_iff_strictRaySupport 𝕜 complete regular divisor)

omit [FiniteDimensional ℝ Ambient] in
theorem strictRaySupport_anticanonical_iff
    (fan : Fan embedding) :
    fan.HasStrictRaySupportInequalities fan.anticanonicalRayDivisor ↔
      fan.HasStrictAnticanonicalConeSupport := by
  simp only [HasStrictRaySupportInequalities, HasStrictAnticanonicalConeSupport,
    fan.anticanonicalRayDivisor_apply, fan.coneDivisorCharacter_anticanonical]

theorem raySumLineBundle_isAmple_iff_strictAnticanonicalSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular fan.anticanonicalRayDivisor).obj ↔
      fan.HasStrictAnticanonicalConeSupport :=
  (fan.invariantDivisor_isAmple_iff_strictRaySupport 𝕜
    complete regular fan.anticanonicalRayDivisor).trans
    fan.strictRaySupport_anticanonical_iff

theorem toricCanonicalInverseClass_isAmple_iff_strictAnticanonicalSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    BondalThomsen.SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹) ↔
      fan.HasStrictAnticanonicalConeSupport := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (fan.toricCanonicalInverseClass_isAmple_iff_raySum 𝕜 complete regular).trans
    (fan.raySumLineBundle_isAmple_iff_strictAnticanonicalSupport 𝕜 complete regular)

theorem strictAnticanonicalSupport_of_actualCanonicalInverse_isAmple
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ample :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      BondalThomsen.SchemeLineBundleClassAmple
        ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹)) :
    fan.HasStrictAnticanonicalConeSupport :=
  (fan.toricCanonicalInverseClass_isAmple_iff_strictAnticanonicalSupport 𝕜
    complete regular).mp ample

end TauCeti.Toric.Fan
