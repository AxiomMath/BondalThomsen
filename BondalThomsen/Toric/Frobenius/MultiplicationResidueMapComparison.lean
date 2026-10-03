module

public import BondalThomsen.Toric.Frobenius.MultiplicationGlobalSplitting

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

theorem residueOverToAffine_image {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] (domain : Source.Opens) :
    inclusion ''ᵁ domain =
      inclusion.opensRange.ι ''ᵁ inclusion.isoOpensRange.hom ''ᵁ domain := by
  ext point
  change point ∈ Set.image inclusion (domain : Set Source) ↔
    point ∈ Set.image inclusion.opensRange.ι
      (Set.image inclusion.isoOpensRange.hom (domain : Set Source))
  have image := congrArg (fun morphism : Source ⟶ Target =>
    Set.image morphism (domain : Set Source)) inclusion.isoOpensRange_hom_ι
  simpa only [Set.image_image, Scheme.Hom.comp_apply] using
    Set.ext_iff.mp image.symm point

theorem residueOverToAffineRestrictionIso_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules) (domain : Source.Opens)
    (sectionValue : Γ((residueOverToAffine inclusion).obj
      (moduleSheaf.over inclusion.opensRange), domain)) :
    Scheme.Modules.Hom.app (residueOverToAffineRestrictionIso inclusion moduleSheaf).hom
      domain sectionValue =
    moduleSheaf.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain)).op
      sectionValue := by
  simp only [residueOverToAffineRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctor_map_app, Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

theorem residueOverToAffineRestrictionIso_inv_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules) (domain : Source.Opens)
    (sectionValue : Γ(moduleSheaf.restrict inclusion, domain)) :
    Scheme.Modules.Hom.app (residueOverToAffineRestrictionIso inclusion moduleSheaf).inv
      domain sectionValue =
    moduleSheaf.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain).symm).op
      sectionValue := by
  have cancellation := ConcreteCategory.congr_hom
    (congrArg (fun comparison => Scheme.Modules.Hom.app comparison domain)
      (residueOverToAffineRestrictionIso inclusion moduleSheaf).inv_hom_id) sectionValue
  change Scheme.Modules.Hom.app (residueOverToAffineRestrictionIso inclusion moduleSheaf).hom
    domain (Scheme.Modules.Hom.app (residueOverToAffineRestrictionIso inclusion moduleSheaf).inv
      domain sectionValue) = sectionValue at cancellation
  apply (ConcreteCategory.bijective_of_isIso
    (moduleSheaf.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain)).op)).injective
  calc
    _ = sectionValue :=
      (residueOverToAffineRestrictionIso_sections inclusion moduleSheaf domain _).symm.trans
        cancellation
    _ = _ := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      simp only [← op_comp, eqToHom_trans, eqToHom_refl, op_id]
      exact (ConcreteCategory.congr_hom (moduleSheaf.presheaf.map_id _) sectionValue).symm

theorem residueOverToAffine_map_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {sourceSheaf targetSheaf : SheafOfModules (Target.ringCatSheaf.over inclusion.opensRange)}
    (comparison : sourceSheaf ⟶ targetSheaf) (domain : Source.Opens)
    (sectionValue : Γ((residueOverToAffine inclusion).obj sourceSheaf, domain)) :
    Scheme.Modules.Hom.app ((residueOverToAffine inclusion).map comparison) domain
      sectionValue =
    comparison.val.app
      (op ((Opens.overEquivalence inclusion.opensRange).symm.functor.obj
        (inclusion.isoOpensRange.hom ''ᵁ domain))) sectionValue := by
  rfl

theorem restrictUnitIso_inv_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] (domain : Source.Opens)
    (sectionValue : Γ(Source, domain)) :
    Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso inclusion).inv domain sectionValue =
      (inclusion.appIso domain).inv sectionValue := by
  rfl

theorem residueOverToAffineFrame_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules)
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      moduleSheaf.over inclusion.opensRange)
    (domain : Source.Opens) (coefficient : Γ(Source, domain)) :
    Scheme.Modules.Hom.app (residueOverToAffineFrame inclusion moduleSheaf frame).hom domain
      coefficient =
    moduleSheaf.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain)).op
      (frame.hom.val.app
        (op ((Opens.overEquivalence inclusion.opensRange).symm.functor.obj
          (inclusion.isoOpensRange.hom ''ᵁ domain)))
        (Target.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain).symm).op
          ((inclusion.appIso domain).inv coefficient))) := by
  change Scheme.Modules.Hom.app
    (residueOverToAffineRestrictionIso inclusion moduleSheaf).hom domain
    (Scheme.Modules.Hom.app ((residueOverToAffine inclusion).map frame.hom) domain
      (Scheme.Modules.Hom.app
        (residueOverToAffineRestrictionIso inclusion (SheafOfModules.unit Target.ringCatSheaf)).inv
        domain (Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso inclusion).inv
          domain coefficient))) = _
  simp only [
    restrictUnitIso_inv_sections, residueOverToAffineRestrictionIso_inv_sections,
    residueOverToAffine_map_sections, residueOverToAffineRestrictionIso_sections]
  rfl

theorem residueOverToAffineFrame_image_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules)
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      moduleSheaf.over inclusion.opensRange)
    (domain : Source.Opens) (coefficient : Γ(Source, domain)) :
    Scheme.Modules.Hom.app (residueOverToAffineFrame inclusion moduleSheaf frame).hom domain
      coefficient =
    frame.hom.val.app (op (Over.mk (homOfLE (inclusion.image_le_opensRange domain))))
      ((inclusion.appIso domain).inv coefficient) := by
  rw [residueOverToAffineFrame_sections]
  let original : Over inclusion.opensRange :=
    Over.mk (homOfLE (inclusion.image_le_opensRange domain))
  let transported := (Opens.overEquivalence inclusion.opensRange).symm.functor.obj
    (inclusion.isoOpensRange.hom ''ᵁ domain)
  let reindex : original ⟶ transported :=
    Over.homMk (eqToHom (residueOverToAffine_image inclusion domain))
  have naturality := ConcreteCategory.congr_hom
    (frame.hom.val.naturality reindex.op)
    (Target.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain).symm).op
      ((inclusion.appIso domain).inv coefficient))
  change frame.hom.val.app (op original)
      (Target.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain)).op
        (Target.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain).symm).op
          ((inclusion.appIso domain).inv coefficient))) =
    moduleSheaf.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain)).op
      (frame.hom.val.app (op transported)
        (Target.presheaf.map (eqToHom (residueOverToAffine_image inclusion domain).symm).op
          ((inclusion.appIso domain).inv coefficient))) at naturality
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at naturality
  simp only [← op_comp, eqToHom_trans, eqToHom_refl, op_id] at naturality
  rw [Target.presheaf.map_id] at naturality
  simp only [ConcreteCategory.id_apply] at naturality
  exact naturality.symm

theorem residueOverToAffineFrame_top_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules)
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      moduleSheaf.over inclusion.opensRange)
    (coefficient : Γ(Target, inclusion.opensRange)) :
    Scheme.Modules.Hom.app (residueOverToAffineFrame inclusion moduleSheaf frame).hom ⊤
      ((inclusion.appIso ⊤).hom
        (Target.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op coefficient)) =
    moduleSheaf.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op
      (frame.hom.val.app (op (Over.mk (𝟙 inclusion.opensRange))) coefficient) := by
  rw [residueOverToAffineFrame_image_sections]
  have cancellation := ConcreteCategory.congr_hom (inclusion.appIso ⊤).hom_inv_id
    (Target.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op coefficient)
  change (inclusion.appIso ⊤).inv ((inclusion.appIso ⊤).hom _) = _ at cancellation
  rw [cancellation]
  let reindex : Over.mk (homOfLE (inclusion.image_le_opensRange ⊤)) ⟶
      Over.mk (𝟙 inclusion.opensRange) :=
    Over.homMk (eqToHom inclusion.image_top_eq_opensRange)
  exact ConcreteCategory.congr_hom (frame.hom.val.naturality reindex.op) coefficient

theorem residueOverToAffineFrame_comp_top_sections {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {sourceSheaf targetSheaf : Target.Modules}
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      sourceSheaf.over inclusion.opensRange)
    (comparison : sourceSheaf ⟶ targetSheaf)
    (coefficient : Γ(Target, inclusion.opensRange)) :
    Scheme.Modules.Hom.app
      ((residueOverToAffineFrame inclusion sourceSheaf frame).hom ≫
        (Scheme.Modules.restrictFunctor inclusion).map comparison) ⊤
      ((inclusion.appIso ⊤).hom
        (Target.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op coefficient)) =
    targetSheaf.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op
      (Scheme.Modules.Hom.app comparison inclusion.opensRange
        (frame.hom.val.app (op (Over.mk (𝟙 inclusion.opensRange))) coefficient)) := by
  change Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor inclusion).map comparison) ⊤
    (Scheme.Modules.Hom.app (residueOverToAffineFrame inclusion sourceSheaf frame).hom ⊤ _) = _
  rw [residueOverToAffineFrame_top_sections, restrictFunctor_map_app]
  exact ConcreteCategory.congr_hom
    (comparison.mapPresheaf.naturality (eqToHom inclusion.image_top_eq_opensRange).op)
    (frame.hom.val.app (op (Over.mk (𝟙 inclusion.opensRange))) coefficient)

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem residueFloorGlobalInclusion_transportedFrame_top_sections (fan : Fan embedding)
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
      ((inclusion.appIso ⊤).hom
        ((fan.algebraicRealization 𝕜 regular).presheaf.map
          (eqToHom inclusion.image_top_eq_opensRange).op
          (fan.chartCoordinateSectionsEquiv 𝕜 regular cone coefficient))) =
    (fan.algebraicRealization 𝕜 regular).presheaf.map
      (homOfLE (by
        exact (Scheme.Hom.preimage_mono (fan.toricMultiplication 𝕜 regular degree)
          inclusion.image_top_eq_opensRange.le).trans
          (fan.toricMultiplication_preimage_chart_open 𝕜 regular positive cone).le)).op
      (fan.chartCoordinateSectionsEquiv 𝕜 regular cone
        (fan.toricMultiplicationRing 𝕜 degree _ coefficient *
          fan.residueFloorChartMonomial 𝕜 complete regular positive character index)) := by
  dsimp only
  rw [BondalThomsen.residueOverToAffineFrame_comp_top_sections,
    fan.residueFloorGlobalInclusion_frame_sections 𝕜]
  change (fan.algebraicRealization 𝕜 regular).presheaf.map _
    ((fan.algebraicRealization 𝕜 regular).presheaf.map _ _) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

end TauCeti.Toric.Fan
