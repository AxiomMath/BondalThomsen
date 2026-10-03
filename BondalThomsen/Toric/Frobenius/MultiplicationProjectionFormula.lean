module

public import BondalThomsen.Toric.Frobenius.MultiplicationFiniteLocallyFree
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.Pullback
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
public import Mathlib.CategoryTheory.Sites.LocalProperties

@[expose] public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite

namespace BondalThomsen

universe u

noncomputable section

variable {Source Target : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
def projectionSectionAction (morphism : Source ⟶ Target)
    (source_module : Source.Modules) (open_set : Target.Opens)
    (scalar : Γ(Source, morphism ⁻¹ᵁ open_set))
    (element : source_module.val.obj (op (morphism ⁻¹ᵁ open_set))) :
    source_module.val.obj (op (morphism ⁻¹ᵁ open_set)) :=
  letI : Module (Γ(Source, morphism ⁻¹ᵁ open_set))
      (source_module.val.obj (op (morphism ⁻¹ᵁ open_set))) :=
    (source_module.val.obj (op (morphism ⁻¹ᵁ open_set))).isModule
  scalar • element

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def projectionActionPresheaf (morphism : Source ⟶ Target)
    (target_module : Target.Modules) (source_module : Source.Modules)
    (comparison : target_module ⟶ (Scheme.Modules.pushforward morphism).obj source_module) :
    target_module.val ⊗
      ((Scheme.Modules.pushforward morphism).obj
        (SheafOfModules.unit Source.ringCatSheaf)).val ⟶
      ((Scheme.Modules.pushforward morphism).obj source_module).val where
  app open_set := by
    letI : Module (Γ(Source, morphism ⁻¹ᵁ open_set.unop))
        (source_module.val.obj (op (morphism ⁻¹ᵁ open_set.unop))) :=
      (source_module.val.obj (op (morphism ⁻¹ᵁ open_set.unop))).isModule
    exact ModuleCat.MonoidalCategory.tensorLift
      (fun element scalar => projectionSectionAction morphism source_module open_set.unop
        scalar (comparison.val.app open_set element))
      (by intros; simp [projectionSectionAction, smul_add])
      (by
        intro scalar element coefficient
        change Γ(Source, morphism ⁻¹ᵁ open_set.unop) at coefficient
        let image : source_module.val.obj (op (morphism ⁻¹ᵁ open_set.unop)) :=
          comparison.val.app open_set element
        dsimp [projectionSectionAction]
        rw [map_smul]
        change (coefficient : Γ(Source, morphism ⁻¹ᵁ open_set.unop)) •
            ((morphism.app open_set.unop) scalar • image) =
          (morphism.app open_set.unop) scalar •
            ((coefficient : Γ(Source, morphism ⁻¹ᵁ open_set.unop)) • image)
        exact smul_comm _ _ _)
      (by intros; simp [projectionSectionAction, add_smul])
      (by
        intro scalar element coefficient
        change Γ(Source, morphism ⁻¹ᵁ open_set.unop) at coefficient
        let image : source_module.val.obj (op (morphism ⁻¹ᵁ open_set.unop)) :=
          comparison.val.app open_set element
        dsimp [projectionSectionAction]
        change ((morphism.app open_set.unop) scalar *
            (coefficient : Source.ringCatSheaf.obj.obj
              (op (morphism ⁻¹ᵁ open_set.unop)))) • image =
          (morphism.app open_set.unop) scalar •
            ((coefficient : Γ(Source, morphism ⁻¹ᵁ open_set.unop)) • image)
        exact mul_smul _ _ _)
  naturality {first_open second_open} inclusion := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro element scalar
    change Γ(Source, morphism ⁻¹ᵁ first_open.unop) at scalar
    let : Module (Γ(Source, morphism ⁻¹ᵁ first_open.unop))
        (source_module.val.obj (op (morphism ⁻¹ᵁ first_open.unop))) :=
      (source_module.val.obj (op (morphism ⁻¹ᵁ first_open.unop))).isModule
    let : Module (Γ(Source, morphism ⁻¹ᵁ second_open.unop))
        (source_module.val.obj (op (morphism ⁻¹ᵁ second_open.unop))) :=
      (source_module.val.obj (op (morphism ⁻¹ᵁ second_open.unop))).isModule
    dsimp [PresheafOfModulesOfCommRing.Monoidal.tensorObj,
      PresheafOfModulesOfCommRing.Monoidal.tensorObjMap,
      ModuleCat.MonoidalCategory.tensorLift, ModuleCat.RestrictScalars.map']
    change projectionSectionAction morphism source_module second_open.unop
        ((Source.presheaf.map ((Opens.map morphism.base).map inclusion.unop).op) scalar)
        (comparison.val.app second_open (target_module.val.map inclusion element)) =
      source_module.val.map ((Opens.map morphism.base).map inclusion.unop).op
        (projectionSectionAction morphism source_module first_open.unop scalar
          (comparison.val.app first_open element))
    have naturality := PresheafOfModules.naturality_apply comparison.val inclusion element
    dsimp [ModuleCat.RestrictScalars.map'] at naturality
    rw [naturality]
    exact (source_module.val.map_smul _ scalar _).symm

set_option backward.isDefEq.respectTransparency false in
def projectionAction (morphism : Source ⟶ Target)
    (target_module : Target.Modules) (source_module : Source.Modules)
    (comparison : target_module ⟶ (Scheme.Modules.pushforward morphism).obj source_module) :
    target_module ⊗ (Scheme.Modules.pushforward morphism).obj
      (SheafOfModules.unit Source.ringCatSheaf) ⟶
        (Scheme.Modules.pushforward morphism).obj source_module :=
  (SheafOfModules.tensorUnderlyingIso (R := Target.sheaf) _ _).hom ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Target.ringCatSheaf.obj)).homEquiv
      _ _).symm (projectionActionPresheaf morphism target_module source_module comparison)

def schemeProjectionFormulaMap (morphism : Source ⟶ Target)
    (target_module : Target.Modules) :
    target_module ⊗ (Scheme.Modules.pushforward morphism).obj
      (SheafOfModules.unit Source.ringCatSheaf) ⟶
        (Scheme.Modules.pushforward morphism).obj
          ((Scheme.Modules.pullback morphism).obj target_module) :=
  projectionAction morphism target_module _
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)

def projectionOpenPushforwardIso (morphism : Source ⟶ Target) (open_set : Target.Opens) :
    Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι ⋙
        Scheme.Modules.pushforward morphism ≅
      Scheme.Modules.pushforward (morphism ∣_ open_set) ⋙
        Scheme.Modules.pushforward open_set.ι :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι morphism open_set).symm ≪≫
    (Scheme.Modules.pushforwardComp _ _).symm

set_option backward.isDefEq.respectTransparency false in
def projectionOpenPullbackIso (morphism : Source ⟶ Target) (open_set : Target.Opens) :
    Scheme.Modules.restrictFunctor open_set.ι ⋙
        Scheme.Modules.pullback (morphism ∣_ open_set) ≅
      Scheme.Modules.pullback morphism ⋙
        Scheme.Modules.restrictFunctor (morphism ⁻¹ᵁ open_set).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).comp
      (Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι))
    ((Scheme.Modules.restrictAdjunction open_set.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (morphism ∣_ open_set)))).symm
    (projectionOpenPushforwardIso morphism open_set)

set_option backward.isDefEq.respectTransparency false in
def projectionOpenSourceTrivialization (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    ((Scheme.Modules.pullback morphism).obj target_module).restrict
        (morphism ⁻¹ᵁ open_set).ι ≅
      SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf :=
  (projectionOpenPullbackIso morphism open_set).symm.app target_module ≪≫
    (Scheme.Modules.pullback (morphism ∣_ open_set)).mapIso trivialization ≪≫
    Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenSourceTrivialization_unit (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module ≫
        (Scheme.Modules.pushforward morphism).map
          ((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).unit.app _ ≫
            (Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map
              (projectionOpenSourceTrivialization morphism open_set target_module
                trivialization).hom) ≫
        (projectionOpenPushforwardIso morphism open_set).hom.app _ =
      (Scheme.Modules.restrictAdjunction open_set.ι).unit.app target_module ≫
        (Scheme.Modules.pushforward open_set.ι).map
          (trivialization.hom ≫
            SheafOfModules.unitToPushforwardObjUnit
              (morphism ∣_ open_set).toRingCatSheafHom) := by
  let global_adjunction := (Scheme.Modules.pullbackPushforwardAdjunction morphism).comp
    (Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι)
  let local_adjunction := (Scheme.Modules.restrictAdjunction open_set.ι).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (morphism ∣_ open_set))
  have conjugate : conjugateEquiv global_adjunction local_adjunction
      (projectionOpenPullbackIso morphism open_set).hom =
      (projectionOpenPushforwardIso morphism open_set).hom :=
    (conjugateEquiv global_adjunction local_adjunction).apply_symm_apply _
  have mapped := Adjunction.homEquiv_conjugateEquiv global_adjunction local_adjunction
    (projectionOpenPullbackIso morphism open_set).hom
    (projectionOpenSourceTrivialization morphism open_set target_module trivialization).hom
  rw [conjugate] at mapped
  have local_transpose : local_adjunction.homEquiv _ _
      ((projectionOpenPullbackIso morphism open_set).hom.app target_module ≫
        (projectionOpenSourceTrivialization morphism open_set target_module trivialization).hom) =
      (Scheme.Modules.restrictAdjunction open_set.ι).unit.app target_module ≫
        (Scheme.Modules.pushforward open_set.ι).map
          (trivialization.hom ≫ SheafOfModules.unitToPushforwardObjUnit
            (morphism ∣_ open_set).toRingCatSheafHom) := by
    have cancel : (projectionOpenPullbackIso morphism open_set).hom.app target_module ≫
        (projectionOpenSourceTrivialization morphism open_set target_module trivialization).hom =
      (Scheme.Modules.pullback (morphism ∣_ open_set)).map trivialization.hom ≫
        (Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)).hom := by
      change (projectionOpenPullbackIso morphism open_set).hom.app target_module ≫
          ((projectionOpenPullbackIso morphism open_set).inv.app target_module ≫
            (Scheme.Modules.pullback (morphism ∣_ open_set)).map trivialization.hom ≫
              (Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)).hom) = _
      simp
    rw [cancel]
    change (Scheme.Modules.restrictAdjunction open_set.ι).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction (morphism ∣_ open_set)).homEquiv _ _
        ((Scheme.Modules.pullback (morphism ∣_ open_set)).map trivialization.hom ≫
          (Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)).hom)) = _
    rw [Adjunction.homEquiv_naturality_left]
    have unit_transpose :=
      Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom
        (morphism ∣_ open_set)
    change (Scheme.Modules.pullbackPushforwardAdjunction (morphism ∣_ open_set)).homEquiv
      (SheafOfModules.unit open_set.toScheme.ringCatSheaf)
      (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)
      (Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)).hom = _ at unit_transpose
    trans (Scheme.Modules.restrictAdjunction open_set.ι).homEquiv _ _
      (trivialization.hom ≫ SheafOfModules.unitToPushforwardObjUnit
        (morphism ∣_ open_set).toRingCatSheafHom)
    · exact congrArg (fun transpose =>
        (Scheme.Modules.restrictAdjunction open_set.ι).homEquiv _ _
          (trivialization.hom ≫ transpose)) unit_transpose
    · rfl
  rw [local_transpose] at mapped
  change (Scheme.Modules.pullbackPushforwardAdjunction morphism).homEquiv _ _
      ((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).homEquiv _ _
        (projectionOpenSourceTrivialization morphism open_set target_module trivialization).hom) ≫
      (projectionOpenPushforwardIso morphism open_set).hom.app _ = _ at mapped
  simpa only [Adjunction.homEquiv_unit, Category.assoc] using mapped

end

end BondalThomsen
