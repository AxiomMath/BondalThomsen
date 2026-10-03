module

public import BondalThomsen.LineBundle.AffineInvertibleSheafTrivial
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Restriction
public import BondalThomsen.Toric.Divisor.PicardSurjectivity
public import BondalThomsen.Toric.Divisor.PicardFaithfulness

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ToricPicardSurjective

universe u

theorem invertible_restrict {source target : Scheme.{u}}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf] :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible source (sheaf.restrict inclusion) := by
  let atlas := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible sheaf
  apply TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
  refine ⟨atlas.I, fun index => inclusion ⁻¹ᵁ atlas.X index, ?_, ?_⟩
  · apply IsOpenCover.mk
    apply top_unique
    intro point member
    have covered := (Opens.coversTop_iff target.carrier atlas.X).mp atlas.coversTop
    obtain ⟨index, contains⟩ := Opens.mem_iSup.mp
      (covered.symm ▸ (show inclusion point ∈ (⊤ : target.Opens) from trivial))
    exact Opens.mem_iSup.mpr ⟨index, contains⟩
  · intro index
    let localMap := inclusion.resLE (atlas.X index) (inclusion ⁻¹ᵁ atlas.X index) le_rfl
    have factorization : localMap ≫ Scheme.Opens.ι (atlas.X index) =
        Scheme.Opens.ι (inclusion ⁻¹ᵁ atlas.X index) ≫ inclusion :=
      inclusion.resLE_comp_ι le_rfl
    letI : IsOpenImmersion (localMap ≫ Scheme.Opens.ι (atlas.X index)) := by
      rw [factorization]
      infer_instance
    letI : IsOpenImmersion localMap := IsOpenImmersion.of_comp
      localMap (Scheme.Opens.ι (atlas.X index))
    let comparison := (Scheme.Modules.restrictFunctorComp
      (inclusion ⁻¹ᵁ atlas.X index).ι inclusion).symm.app sheaf ≪≫
      (Scheme.Modules.restrictFunctorCongr
        factorization.symm).app sheaf ≪≫
      (Scheme.Modules.restrictFunctorComp localMap (Scheme.Opens.ι (atlas.X index))).app sheaf
    exact ⟨(comparison ≪≫ (Scheme.Modules.restrictFunctor localMap).mapIso
      (TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict (atlas.iso index)).symm ≪≫
        Scheme.Modules.restrictUnitIso localMap).symm⟩

noncomputable def openImageTrivialization {source target : Scheme.{u}}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    (sheaf : target.Modules)
    (trivialization : sheaf.restrict inclusion ≅ SheafOfModules.unit source.ringCatSheaf) :
    SheafOfModules.free (R := target.ringCatSheaf.over inclusion.opensRange) PUnit ≅
      sheaf.over inclusion.opensRange := by
  let imageIso := inclusion.isoOpensRange
  let imageTrivialization :=
    (Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_inv_comp.symm).app sheaf ≪≫
      (Scheme.Modules.restrictFunctorComp imageIso.inv inclusion).app sheaf ≪≫
      (Scheme.Modules.restrictFunctor imageIso.inv).mapIso trivialization ≪≫
      Scheme.Modules.restrictUnitIso imageIso.inv
  exact (Scheme.Modules.overEquiv inclusion.opensRange).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overEquiv inclusion.opensRange).functor.mapIso
        (TauCeti.SheafOfModules.freePUnitIsoUnit _) ≪≫
      Opens.sheafOfModulesEquivOverUnit inclusion.opensRange target.ringCatSheaf ≪≫
      imageTrivialization.symm ≪≫
      ((Scheme.Modules.overFunctorEquiv inclusion.opensRange).app sheaf).symm)

end BondalThomsen.ToricPicardSurjective

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def denseTorus_invertibleSheafUnitIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.denseTorus 𝕜).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (fan.denseTorus 𝕜) sheaf] :
    sheaf ≅ SheafOfModules.unit (fan.denseTorus 𝕜).ringCatSheaf := by
  letI := fan.affineCoordinateRing_isDomain 𝕜 ⊥
  letI := fan.denseTorusCoordinateRing_uniqueFactorization 𝕜 complete regular
  exact BondalThomsen.AffineInvertibleSheafTrivial.invertibleSheafUnitIso
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice (⊥ : PointedCone ℝ Ambient))) sheaf

noncomputable def invertibleSheaf_denseTorusUnitIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    sheaf.restrict (fan.denseTorusι 𝕜 regular (fan.completeFan_nonemptyCones complete)) ≅
      SheafOfModules.unit (fan.denseTorus 𝕜).ringCatSheaf := by
  letI := BondalThomsen.ToricPicardSurjective.invertible_restrict
    (fan.denseTorusι 𝕜 regular (fan.completeFan_nonemptyCones complete)) sheaf
  exact fan.denseTorus_invertibleSheafUnitIso 𝕜 complete regular _

noncomputable def affineToricChart_invertibleSheafUnitIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones)
    (sheaf : (fan.affineToricChart 𝕜 cone).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (fan.affineToricChart 𝕜 cone) sheaf] :
    sheaf ≅ SheafOfModules.unit (fan.affineToricChart 𝕜 cone).ringCatSheaf := by
  letI := fan.affineCoordinateRing_isDomain 𝕜 cone.val
  letI := fan.affineCoordinateRing_uniqueFactorization 𝕜 complete regular cone
  exact BondalThomsen.AffineInvertibleSheafTrivial.invertibleSheafUnitIso
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val)) sheaf

noncomputable def invertibleSheaf_chartUnitIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    sheaf.restrict (fan.affineToricChartι 𝕜 regular cone) ≅
      SheafOfModules.unit (fan.affineToricChart 𝕜 cone).ringCatSheaf := by
  letI := BondalThomsen.ToricPicardSurjective.invertible_restrict
    (fan.affineToricChartι 𝕜 regular cone) sheaf
  exact fan.affineToricChart_invertibleSheafUnitIso 𝕜 complete regular cone _

noncomputable def invertibleSheaf_torusOpenTrivialization (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    SheafOfModules.free (R := (fan.algebraicRealization 𝕜 regular).ringCatSheaf.over
      (fan.denseTorusι 𝕜 regular (fan.completeFan_nonemptyCones complete)).opensRange) PUnit ≅
      sheaf.over (fan.denseTorusι 𝕜 regular (fan.completeFan_nonemptyCones complete)).opensRange :=
  BondalThomsen.ToricPicardSurjective.openImageTrivialization _ sheaf
    (fan.invertibleSheaf_denseTorusUnitIso 𝕜 complete regular sheaf)

noncomputable def invertibleSheaf_chartOpenTrivialization (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    SheafOfModules.free (R := (fan.algebraicRealization 𝕜 regular).ringCatSheaf.over
      (fan.affineToricChartι 𝕜 regular cone).opensRange) PUnit ≅
      sheaf.over (fan.affineToricChartι 𝕜 regular cone).opensRange :=
  BondalThomsen.ToricPicardSurjective.openImageTrivialization _ sheaf
    (fan.invertibleSheaf_chartUnitIso 𝕜 complete regular cone sheaf)

omit [FiniteDimensional ℝ Ambient] in

theorem torusOpen_dense (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) :
    Dense ((fan.denseTorusι 𝕜 regular nonempty).opensRange :
      Set (fan.algebraicRealization 𝕜 regular)) :=
  fan.denseTorusι_denseRange 𝕜 regular nonempty

theorem invertibleSheaf_chartRationalUnit_has_laurentUnit (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] (cone : fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    ∃ unit : (fan.LaurentCharacterAlgebra 𝕜)ˣ,
      Units.map (fan.laurentRationalMap 𝕜 regular
        (fan.completeFan_nonemptyCones complete)).toMonoidHom unit =
      Scheme.Modules.trivializationGeneratorRationalUnit sheaf
        (fan.invertibleSheaf_torusOpenTrivialization 𝕜 complete regular sheaf)
        (fan.torusOpen_dense 𝕜 regular (fan.completeFan_nonemptyCones complete))
        (fan.invertibleSheaf_chartOpenTrivialization 𝕜 complete regular cone sheaf) := by
  let nonempty := fan.completeFan_nonemptyCones complete
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let torus := fan.botCone nonempty
  let torusOpen := (fan.affineToricChartι 𝕜 regular torus).opensRange
  let chartOpen := (fan.affineToricChartι 𝕜 regular cone).opensRange
  letI := fan.chartOpen_nonempty 𝕜 regular torus
  letI := fan.chartOpen_nonempty 𝕜 regular cone
  let torusBasis : SheafOfModules.free
      (R := (fan.algebraicRealization 𝕜 regular).ringCatSheaf.over torusOpen) PUnit ≅
      sheaf.over torusOpen := fan.invertibleSheaf_torusOpenTrivialization 𝕜 complete regular sheaf
  have dense : Dense (torusOpen : Set (fan.algebraicRealization 𝕜 regular)) :=
    fan.torusOpen_dense 𝕜 regular nonempty
  let chartBasis := fan.invertibleSheaf_chartOpenTrivialization 𝕜 complete regular cone sheaf
  let included : torusOpen ⟶ chartOpen :=
    homOfLE (fan.torusChartOpen_le_chartOpen 𝕜 regular nonempty cone)
  obtain ⟨sectionUnit, transition, _⟩ :=
    Scheme.Modules.existsUnique_map_trivializationGenerator_eq_smul sheaf chartBasis torusBasis
      included (𝟙 torusOpen)
  let coordinateUnit := Units.map
    (fan.chartCoordinateSectionsEquiv 𝕜 regular torus).symm.toMonoidHom sectionUnit
  let unit := Units.map (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).toMonoidHom coordinateUnit
  refine ⟨unit, Units.ext ?_⟩
  change fan.chartCoordinateGerm 𝕜 regular nonempty torus
    ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm
      ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice) coordinateUnit.val)) = _
  erw [(denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm_apply_apply]
  rw [fan.chartCoordinateGerm_sections 𝕜 regular nonempty torus,
    show fan.chartCoordinateSectionsEquiv 𝕜 regular torus coordinateUnit.val = sectionUnit.val from
      (fan.chartCoordinateSectionsEquiv 𝕜 regular torus).apply_symm_apply _]
  rw [Scheme.Modules.coe_trivializationGeneratorRationalUnit,
    ← Scheme.Modules.rationalFunction_map sheaf torusBasis
      dense included, transition]
  simp only [op_id]
  rw [Scheme.Modules.rationalFunction_smul]
  simp only
  letI : Nonempty (torusOpen ⊓ torusOpen : (fan.algebraicRealization 𝕜 regular).Opens) := by
    simpa only [inf_idem] using (fan.chartOpen_nonempty 𝕜 regular torus)
  have basisValue : Scheme.Modules.rationalFunction sheaf torusBasis
      dense torusOpen
      (Scheme.Modules.trivializationGenerator sheaf torusBasis) = 1 := by
    rw [Scheme.Modules.rationalFunction_apply]
    rw [Scheme.Modules.trivializationCoordinate_map_trivializationGenerator]
    exact map_one _
  change (fan.algebraicRealization 𝕜 regular).germToFunctionField torusOpen sectionUnit.val =
    (fan.algebraicRealization 𝕜 regular).germToFunctionField torusOpen sectionUnit.val *
      Scheme.Modules.rationalFunction sheaf torusBasis dense torusOpen
        (sheaf.presheaf.map (𝟙 (op torusOpen))
          (Scheme.Modules.trivializationGenerator sheaf torusBasis))
  rw [sheaf.presheaf.map_id]
  change _ = _ * Scheme.Modules.rationalFunction sheaf torusBasis dense torusOpen
    (Scheme.Modules.trivializationGenerator sheaf torusBasis)
  rw [basisValue, mul_one]

theorem invertibleSheaf_chartRationalUnit_eq_scalar_character (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] (cone : fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    ∃ character : Lattice →+ ℤ, ∃ scalar : 𝕜ˣ,
      Scheme.Modules.trivializationGeneratorRationalUnit sheaf
        (fan.invertibleSheaf_torusOpenTrivialization 𝕜 complete regular sheaf)
        (fan.torusOpen_dense 𝕜 regular (fan.completeFan_nonemptyCones complete))
        (fan.invertibleSheaf_chartOpenTrivialization 𝕜 complete regular cone sheaf) =
      fan.rationalScalarUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) scalar *
        fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) character := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  letI := fan.chartOpen_nonempty 𝕜 regular cone
  obtain ⟨unit, same⟩ := fan.invertibleSheaf_chartRationalUnit_has_laurentUnit 𝕜
    complete regular sheaf cone
  obtain ⟨character, scalar, classified⟩ := fan.laurentRationalUnit_eq_scalar_character 𝕜
    regular (fan.completeFan_nonemptyCones complete) unit
  exact ⟨character, scalar, same.symm.trans classified⟩

end TauCeti.Toric.Fan
