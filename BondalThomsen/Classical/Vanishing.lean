module

public import BondalThomsen.Classical.Demazure
public import BondalThomsen.Collection.SectionThree.ActualFanoSupport
public import BondalThomsen.LineBundle.PicardGeometricNef
public import BondalThomsen.Toric.Positivity.SemiampleClassCriterion
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Collection.SectionThree.Equivalences
public import BondalThomsen.Toric.Cohomology.PrimitivePairCohomology
public import BondalThomsen.Toric.Frobenius.FrobeniusRemainingSteps
public import BondalThomsen.Cohomology.FiniteAffineCoverQuasicoherentExtensions
public import BondalThomsen.Toric.Frobenius.MultiplicationGlobalResidueIso
public import BondalThomsen.DeepFan.PrimitiveCoefficientCriterion
public import BondalThomsen.Rarity.DeepFanUnconditionalCounting
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryDerivedCohomology
public import BondalThomsen.Toric.Cohomology.NefFirstCohomologyVanishing

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem inverseClass_positiveMultiples_isNef
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (divisorClass : fan.InvariantRayDivisorClass)
    (multiplication : ℕ) (positive : 0 < multiplication)
    (nef : letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
        ⟨fan.structureMap 𝕜 regular⟩
      SchemeLineBundleClassIsNef (baseField := 𝕜) (Additive.toMul
        (fan.invariantDivisorPicardRealization 𝕜 complete regular (-divisorClass)))) :
    letI : (fan.algebraicRealization 𝕜 regular).Over
        (Spec (CommRingCat.of 𝕜)) := ⟨fan.structureMap 𝕜 regular⟩
    AlgebraicGeometry.IsNef (baseField := 𝕜)
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular
        (-((multiplication : ℤ) • divisorClass))).obj := by
  let : (fan.algebraicRealization 𝕜 regular).Over
      (Spec (CommRingCat.of 𝕜)) := ⟨fan.structureMap 𝕜 regular⟩
  let := fan.algebraicRealization_isIntegral 𝕜 regular
    (fan.completeFan_nonemptyCones complete)
  have powerNef := (schemeLineBundleClassIsNef_pow_iff (baseField := 𝕜)
    (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular
      (-divisorClass))) positive).mpr nef
  have classEquality : Additive.toMul (fan.invariantDivisorPicardRealization 𝕜
      complete regular (-((multiplication : ℤ) • divisorClass))) =
      (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular
        (-divisorClass))) ^ multiplication := by
    rw [natCast_zsmul, ← neg_nsmul, map_nsmul, toMul_nsmul]
  apply (schemeLineBundleClassIsNef_mk_iff
    (fan.invariantClassInvertibleSheaf 𝕜 complete regular
      (-((multiplication : ℤ) • divisorClass)))).mp
  rw [fan.invariantClassInvertibleSheaf_class 𝕜, classEquality]
  exact powerNef

theorem nefPositiveVanishing_of_demazure
    (vanishing : DemazureVanishing 𝕜)
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) :
    letI : (fan.algebraicRealization 𝕜 regular).Over
        (Spec (CommRingCat.of 𝕜)) := ⟨fan.structureMap 𝕜 regular⟩
    ∀ multiplication : ℕ, 0 < multiplication →
      ∀ (source : fan.BondalThomsenClass) degree, 0 < degree →
        SchemeLineBundleClassIsNef (baseField := 𝕜) (Additive.toMul
          (fan.invariantDivisorPicardRealization 𝕜 complete regular (-source.val))) →
        Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular
            (-((multiplication : ℤ) • source.val))).obj degree) := by
  intro multiplication positive source degree degreePositive nef
  exact vanishing Lattice Ambient embedding fan complete regular
    (fan.invariantClassInvertibleSheaf 𝕜 complete regular
      (-((multiplication : ℤ) • source.val)))
    (inverseClass_positiveMultiples_isNef 𝕜 fan complete regular source.val
      multiplication positive nef) degree degreePositive

end BondalThomsen
