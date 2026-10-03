module

public import BondalThomsen.Toric.RankOne.SemiampleBridge
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryDerivedCohomology
public import BondalThomsen.Toric.Divisor.DivisorExtCohomology
public import BondalThomsen.Toric.Positivity.AmpleGlobalGenerationCriterion

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Module TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def rankOneSchemePicardDegreeEquivInt
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular)) ≃+ ℤ :=
  (fan.invariantDivisorPicardEquiv 𝕜 complete regular).symm.trans
    (fan.rankOneInvariantDivisorClassEquivInt complete regular basis)

noncomputable def rankOneInvertibleSheafDegree
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) : ℤ :=
  fan.rankOneSchemePicardDegreeEquivInt 𝕜 complete regular basis
    (Additive.ofMul (LineBundleClass.mk bundle))

@[simp] theorem rankOneSchemePicardDegreeEquivInt_invariantClass
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) (divisorClass : fan.InvariantRayDivisorClass) :
    fan.rankOneSchemePicardDegreeEquivInt 𝕜 complete regular basis
      (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass) =
        fan.rankOneClassDegree complete regular basis divisorClass := by
  change fan.rankOneInvariantDivisorClassEquivInt complete regular basis
    ((fan.invariantDivisorPicardEquiv 𝕜 complete regular).symm
      ((fan.invariantDivisorPicardEquiv 𝕜 complete regular) divisorClass)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

@[simp] theorem rankOneInvertibleSheafDegree_invariantDivisor
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    fan.rankOneInvertibleSheafDegree 𝕜 complete regular basis
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) =
        fan.rankOneDivisorCoefficientDegree complete regular basis divisor := by
  unfold rankOneInvertibleSheafDegree
  rw [← fan.invariantDivisorPicardRealization_apply 𝕜,
    fan.rankOneSchemePicardDegreeEquivInt_invariantClass 𝕜,
    fan.rankOneClassDegree_apply]

theorem rankOneInvertibleSheafDegree_eq_of_iso
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    {first second : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)}
    (comparison : first.obj ≅ second.obj) :
    fan.rankOneInvertibleSheafDegree 𝕜 complete regular basis first =
      fan.rankOneInvertibleSheafDegree 𝕜 complete regular basis second := by
  unfold rankOneInvertibleSheafDegree
  rw [LineBundleClass.mk_eq_mk_iff.mpr ⟨comparison⟩]

theorem rankOneInvertibleSheafSemiample_iff_degree_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    BondalThomsen.InvertibleSheafSemiample bundle ↔
      0 ≤ fan.rankOneInvertibleSheafDegree 𝕜 complete regular basis bundle := by
  obtain ⟨divisor, ⟨comparison⟩⟩ :=
    fan.invertibleSheaf_exists_invariantDivisorRepresentative 𝕜 complete regular bundle
  rw [fan.rankOneInvertibleSheafDegree_eq_of_iso 𝕜 complete regular basis comparison,
    fan.rankOneInvertibleSheafDegree_invariantDivisor 𝕜]
  exact (BondalThomsen.invertibleSheafSemiample_iff_of_iso comparison).trans
    (fan.rankOne_invariantDivisorLineBundleSemiample_iff_coefficientDegree_nonnegative 𝕜
      complete regular basis divisor)

end TauCeti.Toric.Fan
