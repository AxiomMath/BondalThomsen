module

public import BondalThomsen.Toric.Frobenius.MultiplicationResidueSplitting

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

theorem restrictFunctor_map_app {Source Target : Scheme} (inclusion : Source ⟶ Target)
    [IsOpenImmersion inclusion] {sourceSheaf targetSheaf : Target.Modules}
    (comparison : sourceSheaf ⟶ targetSheaf) (domain : Source.Opens) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor inclusion).map comparison) domain =
      Scheme.Modules.Hom.app comparison (inclusion ''ᵁ domain) := by
  rfl

noncomputable def residueOverToAffine {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] :
    SheafOfModules (Target.ringCatSheaf.over inclusion.opensRange) ⥤ Source.Modules :=
  (Scheme.Modules.overEquiv inclusion.opensRange).functor ⋙
    Scheme.Modules.restrictFunctor inclusion.isoOpensRange.hom

noncomputable def residueOverToAffineRestrictionIso {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] (moduleSheaf : Target.Modules) :
    (residueOverToAffine inclusion).obj (moduleSheaf.over inclusion.opensRange) ≅
      moduleSheaf.restrict inclusion :=
  (Scheme.Modules.restrictFunctor inclusion.isoOpensRange.hom).mapIso
      ((Scheme.Modules.overFunctorEquiv inclusion.opensRange).app moduleSheaf) ≪≫
    ((Scheme.Modules.restrictFunctorComp inclusion.isoOpensRange.hom inclusion.opensRange.ι).symm.app
      moduleSheaf) ≪≫
    (Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_hom_ι).app moduleSheaf

noncomputable def residueOverToAffineFrame {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] (moduleSheaf : Target.Modules)
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      moduleSheaf.over inclusion.opensRange) :
    SheafOfModules.unit Source.ringCatSheaf ≅ moduleSheaf.restrict inclusion :=
  (Scheme.Modules.restrictUnitIso inclusion).symm ≪≫
    (residueOverToAffineRestrictionIso inclusion (SheafOfModules.unit Target.ringCatSheaf)).symm ≪≫
    (residueOverToAffine inclusion).mapIso frame ≪≫
    residueOverToAffineRestrictionIso inclusion moduleSheaf

theorem restrictUnitIso_app {Source Target : Scheme} (inclusion : Source ⟶ Target)
    [IsOpenImmersion inclusion] (domain : Source.Opens)
    (sectionValue : Γ(Target, inclusion ''ᵁ domain)) :
    Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso inclusion).hom domain sectionValue =
      (inclusion.appIso domain).hom sectionValue := by
  rfl

theorem restrictFunctorAdjCounitIso_app {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Source.Modules) (domain : Source.Opens)
    (sectionValue : Γ(moduleSheaf, inclusion ⁻¹ᵁ inclusion ''ᵁ domain)) :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorAdjCounitIso inclusion).app moduleSheaf).hom domain
        sectionValue =
      moduleSheaf.presheaf.map (eqToHom (inclusion.preimage_image_eq domain).symm).op
        sectionValue := by
  rfl

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in
theorem toricMultiplicationPushforwardChartIso_sections (fan : Fan embedding)
    (regular : fan.IsRegular) {degree : ℕ} (positive : 0 < degree) (cone : fan.cones)
    (domain : (fan.affineToricChart 𝕜 cone).Opens)
    (sectionValue : Γ(fan.algebraicRealization 𝕜 regular,
      fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ (fan.affineToricChartι 𝕜) regular cone ''ᵁ domain)) :
    Scheme.Modules.Hom.app
        (fan.toricMultiplicationPushforwardChartIso 𝕜 regular positive cone).hom domain sectionValue =
      (fan.affineToricChartι 𝕜 regular cone).appLE
        (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ (fan.affineToricChartι 𝕜) regular cone ''ᵁ domain)
        (fan.toricMultiplicationChart 𝕜 degree cone ⁻¹ᵁ domain) (by
          rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
            (fan.toricMultiplicationChart_isPullback 𝕜 regular positive cone) domain,
            (fan.affineToricChartι 𝕜 regular cone).preimage_image_eq]) sectionValue := by
  simp only [toricMultiplicationPushforwardChartIso, Iso.trans_hom,
    BondalThomsen.openPullbackPushforwardRestrictIso, Functor.mapIso_hom, asIso_hom]
  dsimp only [Iso.app_hom, Iso.app_inv, Iso.symm_hom]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    BondalThomsen.restrictFunctor_map_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  change (Scheme.Modules.restrictUnitIso (fan.affineToricChartι 𝕜 regular cone)).hom.app
    (fan.toricMultiplicationChart 𝕜 degree cone ⁻¹ᵁ domain) _ = _
  rw [BondalThomsen.restrictUnitIso_app]
  erw [← Iso.app_hom, BondalThomsen.restrictFunctorAdjCounitIso_app]
  change ((fan.affineToricChartι 𝕜 regular cone).appIso _).hom
    ((fan.algebraicRealization 𝕜 regular).presheaf.map _
      ((fan.algebraicRealization 𝕜 regular).presheaf.map _
        ((fan.algebraicRealization 𝕜 regular).presheaf.map _ sectionValue))) = _
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  apply (ConcreteCategory.congr_hom ?_ sectionValue)
  rw [← cancel_mono ((fan.affineToricChartι 𝕜 regular cone).appIso
    (fan.toricMultiplicationChart 𝕜 degree cone ⁻¹ᵁ domain)).inv,
    Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Scheme.Hom.appLE_appIso_inv]
  congr 1

end TauCeti.Toric.Fan
