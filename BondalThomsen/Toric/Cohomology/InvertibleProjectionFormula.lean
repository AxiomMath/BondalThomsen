module

public import BondalThomsen.Toric.Frobenius.MultiplicationProjectionFormula
public import BondalThomsen.Toric.Frobenius.FrobeniusCohomologyAssembly

@[expose] public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

universe u

noncomputable section

variable {Source Target : Scheme.{u}}

def projectionOpenModuleComparison (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (source_module : Source.Modules)
    (trivialization : source_module.restrict (morphism ⁻¹ᵁ open_set).ι ≅
      SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf) :
    (Scheme.Modules.pushforward morphism).obj source_module ⟶
      (Scheme.Modules.pushforward open_set.ι).obj
        ((Scheme.Modules.pushforward (morphism ∣_ open_set)).obj
          (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)) :=
  (Scheme.Modules.pushforward morphism).map
      ((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).unit.app source_module ≫
        (Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map trivialization.hom) ≫
    (projectionOpenPushforwardIso morphism open_set).hom.app _

def projectionOpenUnitComparison (morphism : Source ⟶ Target)
    (open_set : Target.Opens) :=
  projectionOpenModuleComparison morphism open_set
    (SheafOfModules.unit Source.ringCatSheaf)
    (Scheme.Modules.restrictUnitIso (morphism ⁻¹ᵁ open_set).ι)

lemma projectionOpenPreimage_eq (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_open : Target.Opens) :
    (morphism ⁻¹ᵁ open_set).ι ⁻¹ᵁ (morphism ⁻¹ᵁ target_open) =
      (morphism ∣_ open_set) ⁻¹ᵁ (open_set.ι ⁻¹ᵁ target_open) := by
  rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι,
    Scheme.Hom.comp_preimage]

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenPushforwardIso_app (morphism : Source ⟶ Target)
    (open_set : Target.Opens)
    (local_module : (morphism ⁻¹ᵁ open_set).toScheme.Modules)
    (target_open : Target.Opens) :
    ((projectionOpenPushforwardIso morphism open_set).hom.app local_module).app target_open =
      local_module.presheaf.map
        (eqToHom (projectionOpenPreimage_eq morphism open_set target_open).symm).op := by
  simp only [projectionOpenPushforwardIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenModuleComparison_smul (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (source_module : Source.Modules)
    (trivialization : source_module.restrict (morphism ⁻¹ᵁ open_set).ι ≅
      SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)
    (target_open : Target.Opens) (scalar : Γ(Source, morphism ⁻¹ᵁ target_open))
    (element : source_module.val.obj (op (morphism ⁻¹ᵁ target_open))) :
    (projectionOpenModuleComparison morphism open_set source_module trivialization).val.app
        (op target_open) (projectionSectionAction morphism source_module target_open scalar element) =
      (show Γ((morphism ⁻¹ᵁ open_set).toScheme,
          (morphism ∣_ open_set) ⁻¹ᵁ (open_set.ι ⁻¹ᵁ target_open)) from
        (projectionOpenUnitComparison morphism open_set).val.app (op target_open) scalar) *
      (show Γ((morphism ⁻¹ᵁ open_set).toScheme,
          (morphism ∣_ open_set) ⁻¹ᵁ (open_set.ι ⁻¹ᵁ target_open)) from
        (projectionOpenModuleComparison morphism open_set source_module trivialization).val.app
          (op target_open) element) := by
  let source_open := morphism ⁻¹ᵁ open_set
  let local_open := source_open.ι ⁻¹ᵁ (morphism ⁻¹ᵁ target_open)
  let unit_map := (Scheme.Modules.restrictAdjunction source_open.ι).unit.app source_module
  let : Module (Γ(source_open.toScheme, local_open))
      ((source_module.restrict source_open.ι).val.obj (op local_open)) :=
    ((source_module.restrict source_open.ι).val.obj (op local_open)).isModule
  let image : (source_module.restrict source_open.ι).val.obj (op local_open) :=
    unit_map.val.app (op (morphism ⁻¹ᵁ target_open)) element
  have scalar_action : unit_map.val.app (op (morphism ⁻¹ᵁ target_open))
      (projectionSectionAction morphism source_module target_open scalar element) =
      (source_open.ι.app (morphism ⁻¹ᵁ target_open)) scalar • image :=
    (unit_map.val.app _).hom.map_smul scalar element
  have local_action : trivialization.hom.val.app (op local_open)
      ((source_open.ι.app (morphism ⁻¹ᵁ target_open)) scalar • image) =
      (source_open.ι.app (morphism ⁻¹ᵁ target_open)) scalar *
        (show Γ(source_open.toScheme, local_open) from
          trivialization.hom.val.app (op local_open) image) :=
    (trivialization.hom.val.app _).hom.map_smul _ _
  have comparison_apply (argument : source_module.val.obj (op (morphism ⁻¹ᵁ target_open))) :
      (projectionOpenModuleComparison morphism open_set source_module trivialization).val.app
          (op target_open) argument =
        (source_open.toScheme.presheaf.map
          (eqToHom (projectionOpenPreimage_eq morphism open_set target_open).symm).op)
            (trivialization.hom.val.app (op local_open)
              (unit_map.val.app (op (morphism ⁻¹ᵁ target_open)) argument)) := by
    change ((projectionOpenPushforwardIso morphism open_set).hom.app
        (SheafOfModules.unit source_open.toScheme.ringCatSheaf)).app target_open
          (trivialization.hom.val.app (op local_open)
            (unit_map.val.app (op (morphism ⁻¹ᵁ target_open)) argument)) = _
    rw [projectionOpenPushforwardIso_app]
    rfl
  rw [comparison_apply, scalar_action, local_action, comparison_apply]
  change source_open.toScheme.presheaf.map _ (_ * _) =
    _ * source_open.toScheme.presheaf.map _ _
  rw [map_mul]
  congr 1
  change _ = ((projectionOpenPushforwardIso morphism open_set).hom.app
      (SheafOfModules.unit source_open.toScheme.ringCatSheaf)).app target_open
        ((Scheme.Modules.restrictUnitIso source_open.ι).hom.val.app (op local_open)
          (((Scheme.Modules.restrictAdjunction source_open.ι).unit.app
            (SheafOfModules.unit Source.ringCatSheaf)).val.app
              (op (morphism ⁻¹ᵁ target_open)) scalar))
  rw [projectionOpenPushforwardIso_app]
  change source_open.toScheme.presheaf.map _
      (source_open.ι.app (morphism ⁻¹ᵁ target_open) scalar) =
    source_open.toScheme.presheaf.map _
      ((source_open.ι.appIso local_open).hom
        (Source.presheaf.map
          (homOfLE (source_open.ι.image_preimage_le (morphism ⁻¹ᵁ target_open))).op scalar))
  congr 1
  have equality := source_open.ι.app_appIso_inv (morphism ⁻¹ᵁ target_open)
  have evaluated := congrArg (fun arrow => arrow scalar) equality
  have mapped := congrArg (fun value => (source_open.ι.appIso local_open).hom value) evaluated
  change (source_open.ι.appIso local_open).hom
      ((source_open.ι.appIso local_open).inv
        (source_open.ι.app (morphism ⁻¹ᵁ target_open) scalar)) = _ at mapped
  rw [Iso.inv_hom_id_apply] at mapped
  exact mapped

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenModuleComparison_app_isIso (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (source_module : Source.Modules)
    (trivialization : source_module.restrict (morphism ⁻¹ᵁ open_set).ι ≅
      SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)
    (subopen : open_set.toScheme.Opens) :
    IsIso ((projectionOpenModuleComparison morphism open_set source_module trivialization).val.app
      (op (open_set.ι ''ᵁ subopen))) := by
  have image_eq : (morphism ⁻¹ᵁ open_set).ι ''ᵁ
      ((morphism ⁻¹ᵁ open_set).ι ⁻¹ᵁ (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))) =
      morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen) := by
    rw [← image_morphismRestrict_preimage morphism open_set subopen,
      Scheme.Hom.preimage_image_eq]
  have inclusion_eq : homOfLE ((morphism ⁻¹ᵁ open_set).ι.image_preimage_le
      (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))) = eqToHom image_eq := Subsingleton.elim _ _
  let unit_iso : IsIso (((Scheme.Modules.restrictAdjunction
      (morphism ⁻¹ᵁ open_set).ι).unit.app source_module).app
        (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app, inclusion_eq]
    infer_instance
  let : IsIso (((Scheme.Modules.restrictAdjunction
      (morphism ⁻¹ᵁ open_set).ι).unit.app source_module).val.app
        (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen)))) := by
    let : IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
        (((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).unit.app
          source_module).val.app (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))))) := unit_iso
    exact isIso_of_reflects_iso _ (forget₂ (ModuleCat _) AddCommGrpCat)
  let : IsIso ((projectionOpenPushforwardIso morphism open_set).hom.app
      (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map
      ((projectionOpenPushforwardIso morphism open_set).hom.app _)))
  let : IsIso trivialization.hom.val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map trivialization.hom))
  let : IsIso ((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map
      trivialization.hom).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map
      ((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map trivialization.hom)))
  let : IsIso (((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map
      trivialization.hom).val.app (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen)))) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ _).map
      ((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map trivialization.hom).val))
  let : IsIso (((projectionOpenPushforwardIso morphism open_set).hom.app
      (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)).val.app
        (op (open_set.ι ''ᵁ subopen))) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ _).map
      ((projectionOpenPushforwardIso morphism open_set).hom.app _).val))
  change IsIso ((ModuleCat.restrictScalars (morphism.app
      (open_set.ι ''ᵁ subopen)).hom).map
        (((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).unit.app
          source_module).val.app (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))) ≫
          ((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map
            trivialization.hom).val.app (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen)))) ≫
      ((projectionOpenPushforwardIso morphism open_set).hom.app
        (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)).val.app
          (op (open_set.ι ''ᵁ subopen)))
  infer_instance

def projectionOpenTargetComparison (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    target_module ⟶ (Scheme.Modules.pushforward open_set.ι).obj
      (SheafOfModules.unit open_set.toScheme.ringCatSheaf) :=
  (Scheme.Modules.restrictAdjunction open_set.ι).unit.app target_module ≫
    (Scheme.Modules.pushforward open_set.ι).map trivialization.hom

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenTargetComparison_app_isIso (open_set : Target.Opens)
    (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf)
    (subopen : open_set.toScheme.Opens) :
    IsIso ((projectionOpenTargetComparison open_set target_module trivialization).val.app
      (op (open_set.ι ''ᵁ subopen))) := by
  have image_eq : open_set.ι ''ᵁ (open_set.ι ⁻¹ᵁ (open_set.ι ''ᵁ subopen)) =
      open_set.ι ''ᵁ subopen := by rw [Scheme.Hom.preimage_image_eq]
  have inclusion_eq : homOfLE (open_set.ι.image_preimage_le (open_set.ι ''ᵁ subopen)) =
      eqToHom image_eq := Subsingleton.elim _ _
  let unit_iso : IsIso (((Scheme.Modules.restrictAdjunction open_set.ι).unit.app
      target_module).app (open_set.ι ''ᵁ subopen)) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app, inclusion_eq]
    infer_instance
  let : IsIso (((Scheme.Modules.restrictAdjunction open_set.ι).unit.app
      target_module).val.app (op (open_set.ι ''ᵁ subopen))) := by
    let : IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
        (((Scheme.Modules.restrictAdjunction open_set.ι).unit.app target_module).val.app
          (op (open_set.ι ''ᵁ subopen)))) := unit_iso
    exact isIso_of_reflects_iso _ (forget₂ (ModuleCat _) AddCommGrpCat)
  let : IsIso ((Scheme.Modules.pushforward open_set.ι).map trivialization.hom).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map
      ((Scheme.Modules.pushforward open_set.ι).map trivialization.hom)))
  let : IsIso (((Scheme.Modules.pushforward open_set.ι).map trivialization.hom).val.app
      (op (open_set.ι ''ᵁ subopen))) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ _).map
      ((Scheme.Modules.pushforward open_set.ι).map trivialization.hom).val))
  change IsIso (_ ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenStructureComparison_app_isIso (open_set : Target.Opens)
    (subopen : open_set.toScheme.Opens) :
    IsIso ((SheafOfModules.unitToPushforwardObjUnit open_set.ι.toRingCatSheafHom).val.app
      (op (open_set.ι ''ᵁ subopen))) := by
  have equality := open_set.ι.appIso_hom subopen
  let : IsIso (open_set.toScheme.presheaf.map
      (eqToHom (open_set.ι.preimage_image_eq subopen).symm).op) := inferInstance
  let : IsIso (open_set.ι.app (open_set.ι ''ᵁ subopen) ≫
      open_set.toScheme.presheaf.map
        (eqToHom (open_set.ι.preimage_image_eq subopen).symm).op) := by
    rw [← equality]
    infer_instance
  let : IsIso (open_set.ι.app (open_set.ι ''ᵁ subopen)) :=
    IsIso.of_isIso_comp_right _ (open_set.toScheme.presheaf.map
      (eqToHom (open_set.ι.preimage_image_eq subopen).symm).op)
  let : IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
      ((SheafOfModules.unitToPushforwardObjUnit open_set.ι.toRingCatSheafHom).val.app
        (op (open_set.ι ''ᵁ subopen)))) :=
    inferInstanceAs (IsIso (((forget₂ CommRingCat RingCat) ⋙
      forget₂ RingCat AddCommGrpCat).map (open_set.ι.app (open_set.ι ''ᵁ subopen))))
  exact isIso_of_reflects_iso _ (forget₂ (ModuleCat _) AddCommGrpCat)

set_option backward.isDefEq.respectTransparency false in
lemma projectionActionPresheaf_app_isIso_on_trivializing_open
    (morphism : Source ⟶ Target) (open_set : Target.Opens)
    (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf)
    (subopen : open_set.toScheme.Opens) :
    IsIso ((projectionActionPresheaf morphism target_module
      ((Scheme.Modules.pullback morphism).obj target_module)
      ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)).app
        (op (open_set.ι ''ᵁ subopen))) := by
  let target_open := open_set.ι ''ᵁ subopen
  let : CommRing (Target.ringCatSheaf.obj.obj (op target_open)) :=
    inferInstanceAs (CommRing (Γ(Target, target_open)))
  let source_module := (Scheme.Modules.pullback morphism).obj target_module
  let source_trivialization :=
    projectionOpenSourceTrivialization morphism open_set target_module trivialization
  let target_comparison :=
    (projectionOpenTargetComparison open_set target_module trivialization).val.app (op target_open)
  let source_comparison := (projectionOpenModuleComparison morphism open_set source_module
    source_trivialization).val.app (op target_open)
  let unit_comparison := (projectionOpenUnitComparison morphism open_set).val.app (op target_open)
  let structure_comparison :=
    (SheafOfModules.unitToPushforwardObjUnit open_set.ι.toRingCatSheafHom).val.app (op target_open)
  let : IsIso target_comparison :=
    projectionOpenTargetComparison_app_isIso open_set target_module trivialization subopen
  let : IsIso source_comparison :=
    projectionOpenModuleComparison_app_isIso morphism open_set source_module
      source_trivialization subopen
  let : IsIso unit_comparison :=
    projectionOpenModuleComparison_app_isIso morphism open_set _ _ subopen
  let : IsIso structure_comparison :=
    projectionOpenStructureComparison_app_isIso open_set subopen
  let coordinate := target_comparison ≫ inv structure_comparison
  let canonical := (projectionActionPresheaf morphism target_module source_module
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)).app
      (op target_open)
  have equality : canonical ≫ source_comparison =
      (coordinate ⊗ₘ unit_comparison) ≫ (λ_ _).hom := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro element scalar
    change Γ(Source, morphism ⁻¹ᵁ target_open) at scalar
    change source_comparison
        (projectionSectionAction morphism source_module target_open scalar
          (((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app
            target_module).val.app (op target_open) element)) =
      (show Γ(Target, target_open) from coordinate element) • unit_comparison scalar
    rw [projectionOpenModuleComparison_smul]
    have comparison_unit := projectionOpenSourceTrivialization_unit morphism open_set
      target_module trivialization
    have evaluated := congrArg (fun arrow => arrow.val.app (op target_open) element) comparison_unit
    change source_comparison
      (((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module).val.app
        (op target_open) element) =
      (morphism ∣_ open_set).app (open_set.ι ⁻¹ᵁ target_open)
        (target_comparison element) at evaluated
    rw [evaluated]
    have coordinate_eq : structure_comparison (coordinate element) =
        target_comparison element := by
      change structure_comparison (inv structure_comparison (target_comparison element)) = _
      exact Iso.inv_hom_id_apply (asIso structure_comparison) _
    rw [← coordinate_eq]
    change _ * _ = (morphism ∣_ open_set).app (open_set.ι ⁻¹ᵁ target_open)
      (open_set.ι.app target_open (coordinate element)) * _
    exact mul_comm _ _
  let : IsIso coordinate := inferInstanceAs (IsIso (target_comparison ≫ inv structure_comparison))
  let : IsIso (canonical ≫ source_comparison) := by
    rw [equality]
    infer_instance
  exact IsIso.of_isIso_comp_right canonical source_comparison

set_option backward.isDefEq.respectTransparency false in
lemma projectionActionPresheaf_over_isIso (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    IsIso ((PresheafOfModules.pushforward (F := Over.forget open_set)
      (TauCeti.SheafOfModules.pushforwardRingIso
        (J := (Opens.grothendieckTopology Target).over open_set)
        (K := Opens.grothendieckTopology Target) (Over.forget open_set)
        Target.ringCatSheaf).inv).map
        (projectionActionPresheaf morphism target_module
          ((Scheme.Modules.pullback morphism).obj target_module)
          ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module))) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro local_open
  let ambient_open := local_open.unop.left
  let subopen := open_set.ι ⁻¹ᵁ ambient_open
  have image_eq : open_set.ι ''ᵁ subopen = ambient_open := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (leOfHom local_open.unop.hom)]
  have section_iso := projectionActionPresheaf_app_isIso_on_trivializing_open
    morphism open_set target_module trivialization subopen
  rw [image_eq] at section_iso
  let := section_iso
  exact inferInstanceAs (IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
    ((projectionActionPresheaf morphism target_module
      ((Scheme.Modules.pullback morphism).obj target_module)
      ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)).app
        (op ambient_open))))

set_option backward.isDefEq.respectTransparency false in
lemma schemeProjectionFormulaMap_over_isIso (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    IsIso ((SheafOfModules.overFunctor Target.ringCatSheaf open_set).map
      (schemeProjectionFormulaMap morphism target_module)) := by
  let section_action := projectionActionPresheaf morphism target_module
    ((Scheme.Modules.pullback morphism).obj target_module)
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)
  let sheafify := PresheafOfModules.sheafification (𝟙 Target.ringCatSheaf.obj)
  let restrict := SheafOfModules.overFunctor Target.ringCatSheaf open_set
  let : IsIso ((PresheafOfModules.pushforward (F := Over.forget open_set)
      (TauCeti.SheafOfModules.pushforwardRingIso
        (J := (Opens.grothendieckTopology Target).over open_set)
        (K := Opens.grothendieckTopology Target) (Over.forget open_set)
        Target.ringCatSheaf).inv).map section_action) :=
    projectionActionPresheaf_over_isIso morphism open_set target_module trivialization
  have naturality := TauCeti.SheafOfModules.overSheafificationIso_inv_naturality
    Target.ringCatSheaf section_action open_set
  let : IsIso (restrict.map (sheafify.map section_action)) := by
    have : IsIso ((TauCeti.SheafOfModules.overSheafificationIso Target.ringCatSheaf _
        open_set).inv ≫ restrict.map (sheafify.map section_action)) := by
      rw [← naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (TauCeti.SheafOfModules.overSheafificationIso Target.ringCatSheaf _ open_set).inv _
  change IsIso (restrict.map (projectionAction morphism target_module _ _))
  unfold projectionAction
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in

theorem schemeProjectionFormulaMap_isIso_of_isInvertible (morphism : Source ⟶ Target)
    (target_module : Target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Target target_module] :
    IsIso (schemeProjectionFormulaMap morphism target_module) := by
  let trivializations := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible target_module
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf Target.ringCatSheaf)]
  apply CategoryTheory.Sheaf.isIso_of_coversTop trivializations.coversTop
  intro index
  let local_iso := (TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict
    (trivializations.iso index)).symm
  let := schemeProjectionFormulaMap_over_isIso morphism (trivializations.X index)
    target_module local_iso
  exact inferInstanceAs (IsIso ((SheafOfModules.toSheaf _).map
    ((SheafOfModules.overFunctor Target.ringCatSheaf (trivializations.X index)).map
      (schemeProjectionFormulaMap morphism target_module))))

set_option backward.isDefEq.respectTransparency false in

def schemeInvertibleProjectionFormulaIso (morphism : Source ⟶ Target)
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf Target) :
    (Scheme.Modules.pushforward morphism).obj
        ((Scheme.Modules.pullback morphism).obj bundle.obj) ≅
      bundle.obj ⊗ (Scheme.Modules.pushforward morphism).obj
        (SheafOfModules.unit Source.ringCatSheaf) :=
  letI := schemeProjectionFormulaMap_isIso_of_isInvertible morphism bundle.obj
  (asIso (schemeProjectionFormulaMap morphism bundle.obj)).symm

@[simp]
lemma schemeInvertibleProjectionFormulaIso_inv (morphism : Source ⟶ Target)
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf Target) :
    (schemeInvertibleProjectionFormulaIso morphism bundle).inv =
      schemeProjectionFormulaMap morphism bundle.obj := rfl

end

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def toricMultiplicationInvertibleProjectionIso (fan : Fan embedding)
    (regular : fan.IsRegular) (degree : ℕ)
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    (Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).obj
        ((Scheme.Modules.pullback (fan.toricMultiplication 𝕜 regular degree)).obj bundle.obj) ≅
      bundle.obj ⊗ fan.toricMultiplicationPushforward 𝕜 regular degree :=
  BondalThomsen.schemeInvertibleProjectionFormulaIso (fan.toricMultiplication 𝕜 regular degree) bundle

theorem toricMultiplicationInvertibleProjectionFormula (fan : Fan embedding)
    (regular : fan.IsRegular) : fan.ToricMultiplicationInvertibleProjectionFormula 𝕜 regular := by
  intro degree _ bundle
  exact ⟨fan.toricMultiplicationInvertibleProjectionIso 𝕜 regular degree bundle⟩

end TauCeti.Toric.Fan
