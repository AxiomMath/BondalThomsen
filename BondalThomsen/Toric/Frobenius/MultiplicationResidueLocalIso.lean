module

public import BondalThomsen.Toric.Frobenius.MultiplicationResidueMapComparison

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

theorem schemeHom_comp_apply {SchemeModel : Scheme}
    {sourceSheaf middleSheaf targetSheaf : SchemeModel.Modules}
    (first : sourceSheaf ⟶ middleSheaf) (second : middleSheaf ⟶ targetSheaf)
    (domain : SchemeModel.Opens) (sectionValue : Γ(sourceSheaf, domain)) :
    Scheme.Modules.Hom.app (first ≫ second) domain sectionValue =
      Scheme.Modules.Hom.app second domain
        (Scheme.Modules.Hom.app first domain sectionValue) := by
  rfl

theorem openImmersion_appIso_top_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (coefficient : Γ(Source, ⊤)) :
    (inclusion.appIso ⊤).hom
      (Target.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op
        ((IsOpenImmersion.ΓIsoTop inclusion).hom coefficient)) = coefficient := by
  change (IsOpenImmersion.ΓIsoTop inclusion).inv
    ((IsOpenImmersion.ΓIsoTop inclusion).hom coefficient) = coefficient
  exact ConcreteCategory.congr_hom (IsOpenImmersion.ΓIsoTop inclusion).hom_inv_id coefficient

theorem scheme_appLE_restrict_sections {Source Target : Scheme}
    (morphism : Source ⟶ Target) {domain larger : Target.Opens}
    (contained : domain ≤ larger) (openSubset : Source.Opens)
    (preimage : openSubset ≤ morphism ⁻¹ᵁ domain)
    (sectionValue : Γ(Target, larger)) :
    morphism.appLE domain openSubset preimage
      (Target.presheaf.map (homOfLE contained).op sectionValue) =
    morphism.appLE larger openSubset
      (preimage.trans (Scheme.Hom.preimage_mono morphism contained)) sectionValue := by
  exact ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE morphism preimage (homOfLE contained).op) sectionValue

theorem openImmersion_appLE_top_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (preimage : ⊤ ≤ inclusion ⁻¹ᵁ inclusion.opensRange)
    (coefficient : Γ(Source, ⊤)) :
    inclusion.appLE inclusion.opensRange ⊤ preimage
      ((IsOpenImmersion.ΓIsoTop inclusion).hom coefficient) = coefficient := by
  rw [← openImmersion_sectionsIso_inv]
  exact ConcreteCategory.congr_hom (IsOpenImmersion.ΓIsoTop inclusion).hom_inv_id coefficient

theorem unitSheafHom_ext_top {SchemeModel : Scheme} {moduleSheaf : SchemeModel.Modules}
    {first second : SheafOfModules.unit SchemeModel.ringCatSheaf ⟶ moduleSheaf}
    (same : Scheme.Modules.Hom.app first ⊤ (1 : Γ(SchemeModel, ⊤)) =
      Scheme.Modules.Hom.app second ⊤ (1 : Γ(SchemeModel, ⊤))) : first = second := by
  apply moduleSheaf.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro domain
  have firstRestriction := (moduleSheaf.unitHomEquiv first).property
    (homOfLE (show domain.unop ≤ ⊤ from le_top)).op
  have secondRestriction := (moduleSheaf.unitHomEquiv second).property
    (homOfLE (show domain.unop ≤ ⊤ from le_top)).op
  rw [← firstRestriction, ← secondRestriction]
  exact congrArg (moduleSheaf.val.map
    (homOfLE (show domain.unop ≤ ⊤ from le_top)).op) same

theorem tildeUnit_toOpen_one (coordinateRing : CommRingCat) :
    tilde.toOpen (ModuleCat.of coordinateRing coordinateRing) ⊤ (1 : coordinateRing) =
      (1 : Γ(Spec coordinateRing, ⊤)) := by
  change StructureSheaf.toOpenₗ coordinateRing coordinateRing ⊤ 1 = 1
  exact StructureSheaf.const_one ⊤

theorem affineResidueSheaf_generator_one {Source Target : CommRingCat}
    (ringMap : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ringMap.hom;
      Module.Basis Index Target Source) (residue : Index) :
    letI := Module.compHom Source ringMap.hom
    affinePushforwardStructureSectionsEquiv ringMap
      (Scheme.Modules.Hom.app ((affineResidueSheafUnitIso ringMap basis residue).hom ≫
        affineResidueSheafInclusion ringMap basis residue) ⊤ (1 : Γ(Spec Target, ⊤))) =
      basisResidueInclusion basis residue 1 := by
  let := Module.compHom Source ringMap.hom
  have evaluation := affineResidueSheaf_generator_sections ringMap basis residue 1
  have oneSection := tildeUnit_toOpen_one Target
  rw [oneSection] at evaluation
  exact evaluation

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem residueFloorGlobalInclusion_affineFrame_top_sections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index)
    (coefficient : affineCoordinateRing 𝕜 fan.lattice
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index).val) :
    let cone := (fan.residueFloorAtlas 𝕜 complete regular degree character).cone index
    let inclusion := fan.affineToricChartι 𝕜 regular cone
    let floorSheaf := (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj
    Scheme.Modules.Hom.app
      ((BondalThomsen.residueOverToAffineFrame inclusion floorSheaf
          (fan.residueFloorFrame 𝕜 complete regular degree character index)).hom ≫
        (Scheme.Modules.restrictFunctor inclusion).map
          (fan.residueFloorGlobalInclusion 𝕜 complete regular positive character)) ⊤
      (BondalThomsen.affineGlobalSectionsEquiv
        (affineCoordinateRing 𝕜 fan.lattice cone.val) coefficient) =
    (fan.algebraicRealization 𝕜 regular).presheaf.map
      (homOfLE (by
        exact (Scheme.Hom.preimage_mono (fan.toricMultiplication 𝕜 regular degree)
          inclusion.image_top_eq_opensRange.le).trans
          (fan.toricMultiplication_preimage_chart_open 𝕜 regular positive cone).le)).op
      (fan.chartCoordinateSectionsEquiv 𝕜 regular cone
        (fan.toricMultiplicationRing 𝕜 degree _ coefficient *
          fan.residueFloorChartMonomial 𝕜 complete regular positive character index)) := by
  have evaluation := fan.residueFloorGlobalInclusion_transportedFrame_top_sections 𝕜
    complete regular positive character index coefficient
  dsimp only at evaluation ⊢
  have coordinate : fan.chartCoordinateSectionsEquiv 𝕜 regular
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index) coefficient =
      (IsOpenImmersion.ΓIsoTop (fan.affineToricChartι 𝕜 regular
        ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index))).hom
        (BondalThomsen.affineGlobalSectionsEquiv _ coefficient) := rfl
  rw [coordinate] at evaluation
  rw [BondalThomsen.openImmersion_appIso_top_sections] at evaluation
  exact evaluation

theorem residueFloorGlobalInclusion_canonicalChart_top_sections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index)
    (coefficient : affineCoordinateRing 𝕜 fan.lattice
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index).val) :
    let cone := (fan.residueFloorAtlas 𝕜 complete regular degree character).cone index
    let inclusion := fan.affineToricChartι 𝕜 regular cone
    let floorSheaf := (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj
    Scheme.Modules.Hom.app
      ((BondalThomsen.residueOverToAffineFrame inclusion floorSheaf
          (fan.residueFloorFrame 𝕜 complete regular degree character index)).hom ≫
        (Scheme.Modules.restrictFunctor inclusion).map
          (fan.residueFloorGlobalInclusion 𝕜 complete regular positive character) ≫
        (fan.toricMultiplicationPushforwardChartIso 𝕜 regular positive cone).hom) ⊤
      (BondalThomsen.affineGlobalSectionsEquiv
        (affineCoordinateRing 𝕜 fan.lattice cone.val) coefficient) =
    inclusion.appLE inclusion.opensRange
      (fan.toricMultiplicationChart 𝕜 degree cone ⁻¹ᵁ ⊤) (by
        rw [Opens.map_top]
        exact inclusion.preimage_image_eq ⊤ |>.ge.trans
          (Scheme.Hom.preimage_mono inclusion inclusion.image_top_eq_opensRange.le))
      (fan.chartCoordinateSectionsEquiv 𝕜 regular cone
        (fan.toricMultiplicationRing 𝕜 degree _ coefficient *
          fan.residueFloorChartMonomial 𝕜 complete regular positive character index)) := by
  dsimp only
  rw [← Category.assoc, BondalThomsen.schemeHom_comp_apply]
  rw [fan.residueFloorGlobalInclusion_affineFrame_top_sections 𝕜,
    fan.toricMultiplicationPushforwardChartIso_sections 𝕜]
  apply BondalThomsen.scheme_appLE_restrict_sections

theorem residueFloorGlobalInclusion_canonicalChart_coordinate (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index)
    (coefficient : affineCoordinateRing 𝕜 fan.lattice
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index).val) :
    let cone := (fan.residueFloorAtlas 𝕜 complete regular degree character).cone index
    let inclusion := fan.affineToricChartι 𝕜 regular cone
    let floorSheaf := (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj
    BondalThomsen.affinePushforwardStructureSectionsEquiv
      (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree cone.val).toRingHom)
      (Scheme.Modules.Hom.app
        ((BondalThomsen.residueOverToAffineFrame inclusion floorSheaf
            (fan.residueFloorFrame 𝕜 complete regular degree character index)).hom ≫
          (Scheme.Modules.restrictFunctor inclusion).map
            (fan.residueFloorGlobalInclusion 𝕜 complete regular positive character) ≫
          (fan.toricMultiplicationPushforwardChartIso 𝕜 regular positive cone).hom) ⊤
        (BondalThomsen.affineGlobalSectionsEquiv
          (affineCoordinateRing 𝕜 fan.lattice cone.val) coefficient)) =
    fan.toricMultiplicationRing 𝕜 degree cone.val coefficient *
      fan.residueFloorChartMonomial 𝕜 complete regular positive character index := by
  dsimp only
  rw [fan.residueFloorGlobalInclusion_canonicalChart_top_sections 𝕜]
  change (Scheme.ΓSpecIso (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
    ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index).val))).hom
    ((fan.affineToricChartι 𝕜 regular _).appLE _ ⊤ _
      ((IsOpenImmersion.ΓIsoTop (fan.affineToricChartι 𝕜 regular _)).hom
        (BondalThomsen.affineGlobalSectionsEquiv _ _))) = _
  rw [BondalThomsen.openImmersion_appLE_top_sections]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso _).inv_hom_id _

theorem residueFloorGlobalInclusion_canonicalChart_component (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index) :
    let cone := (fan.residueFloorAtlas 𝕜 complete regular degree character).cone index
    let inclusion := fan.affineToricChartι 𝕜 regular cone
    let floorSheaf := (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj
    (BondalThomsen.residueOverToAffineFrame inclusion floorSheaf
        (fan.residueFloorFrame 𝕜 complete regular degree character index)).hom ≫
      (Scheme.Modules.restrictFunctor inclusion).map
        (fan.residueFloorGlobalInclusion 𝕜 complete regular positive character) ≫
      (fan.toricMultiplicationPushforwardChartIso 𝕜 regular positive cone).hom =
    (fan.basisConeResidueSheafUnitIso 𝕜
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).property.1
        positive character).hom ≫
      fan.basisConeResidueSheafInclusion 𝕜
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).property.1
        positive character := by
  dsimp only
  apply BondalThomsen.unitSheafHom_ext_top
  apply (BondalThomsen.affinePushforwardStructureSectionsEquiv
    (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index).val).toRingHom)).injective
  have global := fan.residueFloorGlobalInclusion_canonicalChart_coordinate 𝕜
    complete regular positive character index 1
  have affine := BondalThomsen.affineResidueSheaf_generator_one
    (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index).val).toRingHom)
    (fan.basisConeMultiplicationBasis 𝕜 positive
      (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2)
    (normalizedResidue (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
      positive character)
  simp only [map_one, one_mul] at global affine
  have monomial := fan.basisConeResidueInclusion_apply 𝕜
    (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
    positive character 1
  simp only [map_one, one_mul] at monomial
  exact global.trans (monomial.symm.trans affine.symm)

end TauCeti.Toric.Fan
