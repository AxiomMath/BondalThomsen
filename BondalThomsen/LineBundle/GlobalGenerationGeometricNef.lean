module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LineBundleDegreeIndependence
public import BondalThomsen.LineBundle.GloballyGeneratedPullback
public import BondalThomsen.Toric.Positivity.AmpleGlobalGenerationCriterion

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

universe schemeUniverse

theorem globallyGeneratedInvertibleSheaf_exists_nonzero_globalSection
    {scheme : Scheme.{schemeUniverse}} [IsIntegral scheme]
    (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    (generators : bundle.GeneratingSections) :
    ∃ sectionValue : Γ(bundle, ⊤), sectionValue ≠ 0 := by
  classical
  by_contra noSection
  have allZero : ∀ sectionValue : Γ(bundle, ⊤), sectionValue = 0 := by
    simpa only [not_exists, not_not] using noSection
  have sectionZero : ∀ index,
      generators.s index = bundle.unitHomEquiv (0 : SheafOfModules.unit _ ⟶ bundle) := by
    intro index
    apply PresheafOfModules.sections_ext
    intro openSet
    rw [← PresheafOfModules.sections_property _
      (homOfLE (show openSet.unop ≤ ⊤ from le_top)).op,
      allZero ((generators.s index).val (op ⊤))]
    simp only [SheafOfModules.unitHomEquiv_apply_coe]
    change bundle.res _ 0 = (0 : Γ(bundle, openSet.unop))
    exact map_zero _
  have evaluationZero : generators.π = 0 := by
    apply (SheafOfModules.freeHomEquiv _).injective
    funext index
    simp only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply,
      sectionZero]
    simp [SheafOfModules.freeHomEquiv]
  let : Epi generators.π := generators.epi
  have zeroBundle := IsZero.of_epi_eq_zero generators.π evaluationZero
  obtain ⟨region, contains, generator, frame⟩ := exists_frame bundle (genericPoint scheme)
  let : Nonempty region := ⟨⟨genericPoint scheme, contains⟩⟩
  have identityZero : (𝟙 bundle : bundle ⟶ bundle) = 0 := zeroBundle.eq_of_src _ _
  have generatorZero : generator = 0 := by
    have equality := congrArg (fun morphism : bundle ⟶ bundle => morphism.app region generator)
      identityZero
    simpa using equality
  apply frame.genericGenerator_ne_zero
  simp [IsFrame.genericGenerator, generatorZero]

theorem globallyGeneratedInvertibleSheaf_isNef
    {baseField : Type schemeUniverse} [Field baseField]
    {scheme : Scheme.{schemeUniverse}} [scheme.Over (Spec (CommRingCat.of baseField))]
    (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    (generated : Nonempty bundle.GeneratingSections) :
    AlgebraicGeometry.IsNef (baseField := baseField) bundle := by
  apply isNef_of_nonzero_globalSection_on_every_curve_pullback
  intro curve
  obtain ⟨generators⟩ := globallyGenerated_pullback curve.ι bundle generated
  exact globallyGeneratedInvertibleSheaf_exists_nonzero_globalSection _ generators

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem invariantDivisorSheaf_isNef_of_support
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor) :
    letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
      ⟨fan.structureMap 𝕜 regular⟩
    AlgebraicGeometry.IsNef (baseField := 𝕜)
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj := by
  let : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨fan.structureMap 𝕜 regular⟩
  exact BondalThomsen.globallyGeneratedInvertibleSheaf_isNef _
    ((fan.invariantDivisorGloballyGenerated_iff_support 𝕜 complete regular divisor).mpr support)

end TauCeti.Toric.Fan
