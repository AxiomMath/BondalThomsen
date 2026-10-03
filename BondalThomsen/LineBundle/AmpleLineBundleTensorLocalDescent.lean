module

public import BondalThomsen.LineBundle.AmpleLineBundleGeneralAffinePullback
public import Mathlib.CategoryTheory.Sites.LocalProperties

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory

noncomputable section

namespace BondalThomsen

variable {source target : Scheme.{0}}

theorem ampleModuleHom_res {scheme : Scheme.{0}} {first second : scheme.Modules}
    (morphism : first ⟶ second) {smaller larger : scheme.Opens}
    (contained : smaller ≤ larger) (section_value : Γ(first, larger)) :
    second.res contained (Scheme.Modules.Hom.app morphism larger section_value) =
      Scheme.Modules.Hom.app morphism smaller (first.res contained section_value) := by
  simp only [ampleModuleApp_val]
  exact (PresheafOfModules.naturality_apply morphism.val (homOfLE contained).op section_value).symm

def amplePullbackLocalSection (map : source ⟶ target) (sheaf : target.Modules)
    (open_set : target.Opens) (section_value : Γ(sheaf, open_set)) :
    Γ((Scheme.Modules.pullback map).obj sheaf, map ⁻¹ᵁ open_set) :=
  Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
    open_set section_value

theorem amplePullbackLocalSection_res (map : source ⟶ target) (sheaf : target.Modules)
    {smaller larger : target.Opens} (contained : smaller ≤ larger)
    (section_value : Γ(sheaf, larger)) :
    ((Scheme.Modules.pullback map).obj sheaf).res (map.preimage_mono contained)
        (amplePullbackLocalSection map sheaf larger section_value) =
      amplePullbackLocalSection map sheaf smaller (sheaf.res contained section_value) := by
  exact (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf).val
      (homOfLE contained).op section_value).symm

theorem amplePullbackLocalSection_comp {middle : Scheme.{0}}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (sheaf : target.Modules) (open_set : target.Opens) (section_value : Γ(sheaf, open_set)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp first second).app sheaf).hom
        ((first ≫ second) ⁻¹ᵁ open_set)
        (amplePullbackLocalSection first ((Scheme.Modules.pullback second).obj sheaf)
          (second ⁻¹ᵁ open_set) (amplePullbackLocalSection second sheaf open_set section_value)) =
      amplePullbackLocalSection (first ≫ second) sheaf open_set section_value := by
  have compatibility := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction second).comp
      (Scheme.Modules.pullbackPushforwardAdjunction first))
    (Scheme.Modules.pullbackPushforwardAdjunction (first ≫ second))
    (Scheme.Modules.pullbackComp first second).inv sheaf
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at compatibility
  have inverse_formula := congrArg (fun morphism =>
    Scheme.Modules.Hom.app morphism open_set section_value) compatibility
  have inverse_value : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp first second).app sheaf).inv
      ((first ≫ second) ⁻¹ᵁ open_set)
      (amplePullbackLocalSection (first ≫ second) sheaf open_set section_value) =
      amplePullbackLocalSection first ((Scheme.Modules.pullback second).obj sheaf)
        (second ⁻¹ᵁ open_set) (amplePullbackLocalSection second sheaf open_set section_value) := by
    exact inverse_formula.symm
  rw [← inverse_value]
  change Scheme.Modules.Hom.app (((Scheme.Modules.pullbackComp first second).app sheaf).inv ≫
    ((Scheme.Modules.pullbackComp first second).app sheaf).hom) _ _ = _
  rw [Iso.inv_hom_id]
  rfl

theorem amplePullbackLocalSection_congr {first second : source ⟶ target}
    (equal : first = second) (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr equal).app sheaf).hom
        (first ⁻¹ᵁ open_set) (amplePullbackLocalSection first sheaf open_set section_value) =
      ((Scheme.Modules.pullback second).obj sheaf).res
        (show first ⁻¹ᵁ open_set ≤ second ⁻¹ᵁ open_set by rw [equal])
        (amplePullbackLocalSection second sheaf open_set section_value) := by
  subst second
  rw [Scheme.Modules.res_self]
  rfl

theorem amplePullbackLocalSection_restrict (inclusion : source ⟶ target)
    [IsOpenImmersion inclusion] (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback inclusion).app sheaf).hom
        (inclusion ⁻¹ᵁ open_set) (schemeRestrictedSection inclusion sheaf open_set section_value) =
      amplePullbackLocalSection inclusion sheaf open_set section_value := by
  exact congrArg (fun morphism => Scheme.Modules.Hom.app morphism open_set section_value)
    (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction inclusion)
      (Scheme.Modules.pullbackPushforwardAdjunction inclusion) sheaf)

def ampleSectionOnOpen (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set)) : Γ(sheaf.restrict open_set.ι, ⊤) :=
  (sheaf.restrict open_set.ι).res (by rw [Scheme.Opens.ι_preimage_self])
    (schemeRestrictedSection open_set.ι sheaf open_set section_value)

theorem ampleSectionOnOpen_isFrame (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set))
    (frame : Scheme.Modules.IsFrame sheaf open_set section_value) :
    Scheme.Modules.IsFrame (sheaf.restrict open_set.ι) ⊤
      (ampleSectionOnOpen sheaf open_set section_value) := by
  exact (schemeRestrictedSection_isFrame open_set.ι sheaf frame).restrict
    (by rw [Scheme.Opens.ι_preimage_self])

theorem ampleSectionOnOpen_pullbackUnit (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).hom ⊤
        (ampleSectionOnOpen sheaf open_set section_value) =
      ((Scheme.Modules.pullback open_set.ι).obj sheaf).res
        (by rw [Scheme.Opens.ι_preimage_self])
        (amplePullbackLocalSection open_set.ι sheaf open_set section_value) := by
  have local_identity := amplePullbackLocalSection_restrict open_set.ι sheaf open_set section_value
  have restricted_identity := congrArg (fun value =>
    ((Scheme.Modules.pullback open_set.ι).obj sheaf).res
      (show (⊤ : open_set.toScheme.Opens) ≤ open_set.ι ⁻¹ᵁ open_set by
        rw [Scheme.Opens.ι_preimage_self]) value) local_identity
  rw [ampleModuleHom_res] at restricted_identity
  exact restricted_identity

theorem amplePullbackLocalSection_restrictPullbackObjIso
    (map : source ⟶ target) (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set)) :
    Scheme.Modules.Hom.app (Scheme.Modules.restrictPullbackObjIso map open_set sheaf).hom ⊤
        (ampleSectionOnOpen ((Scheme.Modules.pullback map).obj sheaf) (map ⁻¹ᵁ open_set)
          (amplePullbackLocalSection map sheaf open_set section_value)) =
      amplePullbackGlobalSection (map ∣_ open_set) (sheaf.restrict open_set.ι)
        (ampleSectionOnOpen sheaf open_set section_value) := by
  unfold Scheme.Modules.restrictPullbackObjIso
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullback (map ∣_ open_set)).map
      ((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).inv) ⊤
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).inv ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr (morphismRestrict_ι map open_set).symm).app sheaf).hom ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp (map ⁻¹ᵁ open_set).ι map).app sheaf).hom ⊤
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.restrictFunctorIsoPullback (map ⁻¹ᵁ open_set).ι).app _).hom ⊤ _)))) = _
  rw [ampleSectionOnOpen_pullbackUnit]
  have top_identity : ((map ⁻¹ᵁ open_set).ι ≫ map) ⁻¹ᵁ open_set = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
  have composition := amplePullbackLocalSection_comp (map ⁻¹ᵁ open_set).ι map sheaf
    open_set section_value
  have first_formula : Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp (map ⁻¹ᵁ open_set).ι map).app sheaf).hom ⊤
      (((Scheme.Modules.pullback (map ⁻¹ᵁ open_set).ι).obj
        ((Scheme.Modules.pullback map).obj sheaf)).res
          (by rw [Scheme.Opens.ι_preimage_self])
          (amplePullbackLocalSection (map ⁻¹ᵁ open_set).ι
            ((Scheme.Modules.pullback map).obj sheaf) (map ⁻¹ᵁ open_set)
            (amplePullbackLocalSection map sheaf open_set section_value))) =
      ((Scheme.Modules.pullback ((map ⁻¹ᵁ open_set).ι ≫ map)).obj sheaf).res
        (by rw [top_identity])
        (amplePullbackLocalSection ((map ⁻¹ᵁ open_set).ι ≫ map) sheaf open_set section_value) := by
    have restricted_composition := congrArg (fun value =>
      ((Scheme.Modules.pullback ((map ⁻¹ᵁ open_set).ι ≫ map)).obj sheaf).res
        (show (⊤ : (map ⁻¹ᵁ open_set).toScheme.Opens) ≤
          ((map ⁻¹ᵁ open_set).ι ≫ map) ⁻¹ᵁ open_set by rw [top_identity]) value) composition
    rw [ampleModuleHom_res] at restricted_composition
    exact restricted_composition
  rw [first_formula]
  have congr_formula := amplePullbackLocalSection_congr
    (morphismRestrict_ι map open_set).symm sheaf open_set section_value
  have restricted_congr := congrArg (fun value =>
    ((Scheme.Modules.pullback ((map ∣_ open_set) ≫ open_set.ι)).obj sheaf).res
      (show (⊤ : (map ⁻¹ᵁ open_set).toScheme.Opens) ≤
        ((map ⁻¹ᵁ open_set).ι ≫ map) ⁻¹ᵁ open_set by rw [top_identity]) value) congr_formula
  rw [ampleModuleHom_res, Scheme.Modules.res_res] at restricted_congr
  have second_top : ((map ∣_ open_set) ≫ open_set.ι) ⁻¹ᵁ open_set = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  have second_composition := amplePullbackLocalSection_comp (map ∣_ open_set) open_set.ι
    sheaf open_set section_value
  have second_formula : Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).hom ⊤
      (amplePullbackGlobalSection (map ∣_ open_set) ((Scheme.Modules.pullback open_set.ι).obj sheaf)
        (((Scheme.Modules.pullback open_set.ι).obj sheaf).res
          (by rw [Scheme.Opens.ι_preimage_self])
          (amplePullbackLocalSection open_set.ι sheaf open_set section_value))) =
      ((Scheme.Modules.pullback ((map ∣_ open_set) ≫ open_set.ι)).obj sheaf).res
        (by rw [second_top])
        (amplePullbackLocalSection ((map ∣_ open_set) ≫ open_set.ι) sheaf open_set section_value) := by
    have restricted_composition := congrArg (fun value =>
      ((Scheme.Modules.pullback ((map ∣_ open_set) ≫ open_set.ι)).obj sheaf).res
        (show (⊤ : (map ⁻¹ᵁ open_set).toScheme.Opens) ≤
          ((map ∣_ open_set) ≫ open_set.ι) ⁻¹ᵁ open_set by rw [second_top]) value) second_composition
    rw [ampleModuleHom_res] at restricted_composition
    change Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).hom ⊤
      (((Scheme.Modules.pullback (map ∣_ open_set)).obj
        ((Scheme.Modules.pullback open_set.ι).obj sheaf)).res
          ((map ∣_ open_set).preimage_mono
            (show (⊤ : open_set.toScheme.Opens) ≤ open_set.ι ⁻¹ᵁ open_set by
              rw [Scheme.Opens.ι_preimage_self]))
          (amplePullbackLocalSection (map ∣_ open_set) ((Scheme.Modules.pullback open_set.ι).obj sheaf)
            (open_set.ι ⁻¹ᵁ open_set)
            (amplePullbackLocalSection open_set.ι sheaf open_set section_value))) = _ at restricted_composition
    have restriction_formula := amplePullbackLocalSection_res (map ∣_ open_set)
      ((Scheme.Modules.pullback open_set.ι).obj sheaf)
      (show (⊤ : open_set.toScheme.Opens) ≤ open_set.ι ⁻¹ᵁ open_set by
        rw [Scheme.Opens.ι_preimage_self])
      (amplePullbackLocalSection open_set.ι sheaf open_set section_value)
    exact (congrArg (fun value => Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).hom ⊤ value)
      restriction_formula).symm.trans restricted_composition
  rw [restricted_congr]
  rw [← second_formula]
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullback (map ∣_ open_set)).map
    ((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).inv) ⊤
    (Scheme.Modules.Hom.app (((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).hom ≫
      ((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).inv) ⊤ _) = _
  rw [Iso.hom_inv_id]
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullback (map ∣_ open_set)).map
    ((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).inv) ⊤
    (amplePullbackGlobalSection (map ∣_ open_set) ((Scheme.Modules.pullback open_set.ι).obj sheaf)
      (((Scheme.Modules.pullback open_set.ι).obj sheaf).res
        (by rw [Scheme.Opens.ι_preimage_self])
        (amplePullbackLocalSection open_set.ι sheaf open_set section_value))) = _
  rw [amplePullbackGlobalSection_naturality, ← ampleSectionOnOpen_pullbackUnit]
  change amplePullbackGlobalSection (map ∣_ open_set) (sheaf.restrict open_set.ι)
    (Scheme.Modules.Hom.app (((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).hom ≫
      ((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).inv) ⊤ _) = _
  rw [Iso.hom_inv_id]
  rfl

theorem ampleFrame_iso_hom {scheme : Scheme.{0}} {first second : scheme.Modules}
    (comparison : first ≅ second) (open_set : scheme.Opens) (section_value : Γ(first, open_set))
    (frame : Scheme.Modules.IsFrame first open_set section_value) :
    Scheme.Modules.IsFrame second open_set
      (Scheme.Modules.Hom.app comparison.hom open_set section_value) := by
  intro smaller contained
  rw [ampleModuleHom_res]
  have formula : (fun scalar : Γ(scheme, smaller) => scalar •
      Scheme.Modules.Hom.app comparison.hom smaller (first.res contained section_value)) =
      fun scalar => Scheme.Modules.Hom.app comparison.hom smaller
        (scalar • first.res contained section_value) := by
    funext scalar
    exact (Scheme.Modules.Hom.app_smul comparison.hom scalar _).symm
  rw [formula]
  exact (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app comparison.hom smaller)).comp (frame smaller contained)

theorem ampleFrameApp_transport {scheme : Scheme.{0}} (sheaf : scheme.Modules)
    {first second domain : scheme.Opens} (equal : first = second)
    (first_contained : first ≤ domain) (second_contained : second ≤ domain)
    (section_value : Γ(sheaf, domain))
    (bijective : Function.Bijective (fun scalar : Γ(scheme, first) =>
      scalar • sheaf.res first_contained section_value)) :
    Function.Bijective (fun scalar : Γ(scheme, second) =>
      scalar • sheaf.res second_contained section_value) := by
  subst second
  exact bijective

theorem ampleFrame_of_sectionOnOpen (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set))
    (frame : Scheme.Modules.IsFrame (sheaf.restrict open_set.ι) ⊤
      (ampleSectionOnOpen sheaf open_set section_value)) :
    Scheme.Modules.IsFrame sheaf open_set section_value := by
  intro smaller contained
  have image_equal : open_set.ι ''ᵁ (open_set.ι ⁻¹ᵁ smaller) = smaller := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr contained]
  have local_frame := frame (open_set.ι ⁻¹ᵁ smaller) le_top
  have original_frame : Function.Bijective (fun scalar : Γ(target,
      open_set.ι ''ᵁ (open_set.ι ⁻¹ᵁ smaller)) => scalar •
      sheaf.res (show open_set.ι ''ᵁ (open_set.ι ⁻¹ᵁ smaller) ≤ open_set from
        Scheme.Opens.ι_image_le _ _) section_value) := by
    have section_formula :
        (sheaf.restrictAppIso open_set.ι (open_set.ι ⁻¹ᵁ smaller)).hom
          ((sheaf.restrict open_set.ι).res le_top
            (ampleSectionOnOpen sheaf open_set section_value)) =
        sheaf.res (Scheme.Opens.ι_image_le _ _) section_value := by
      unfold ampleSectionOnOpen
      rw [Scheme.Modules.res_res]
      rw [schemeRestrictedSection_res]
      change sheaf.res _ section_value = _
      rfl
    have composite := (ConcreteCategory.bijective_of_isIso
      (sheaf.restrictAppIso open_set.ι (open_set.ι ⁻¹ᵁ smaller)).hom).comp
      (local_frame.comp (ConcreteCategory.bijective_of_isIso
        (open_set.ι.appIso (open_set.ι ⁻¹ᵁ smaller)).hom))
    have formula : (fun scalar : Γ(target, open_set.ι ''ᵁ (open_set.ι ⁻¹ᵁ smaller)) =>
        (sheaf.restrictAppIso open_set.ι (open_set.ι ⁻¹ᵁ smaller)).hom
          ((open_set.ι.appIso (open_set.ι ⁻¹ᵁ smaller)).hom scalar •
            (sheaf.restrict open_set.ι).res le_top
              (ampleSectionOnOpen sheaf open_set section_value))) =
        fun scalar => scalar • sheaf.res (Scheme.Opens.ι_image_le _ _) section_value := by
      funext scalar
      rw [Scheme.Modules.smul_restrictAppIso_hom_apply, section_formula]
      rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
      rfl
    change Function.Bijective (fun scalar : Γ(target, open_set.ι ''ᵁ (open_set.ι ⁻¹ᵁ smaller)) =>
      (sheaf.restrictAppIso open_set.ι (open_set.ι ⁻¹ᵁ smaller)).hom
        ((open_set.ι.appIso (open_set.ι ⁻¹ᵁ smaller)).hom scalar •
          (sheaf.restrict open_set.ι).res le_top
            (ampleSectionOnOpen sheaf open_set section_value))) at composite
    rw [formula] at composite
    exact composite
  exact ampleFrameApp_transport sheaf image_equal _ contained section_value original_frame

theorem amplePullbackLocalSection_isFrame (map : source ⟶ target) (sheaf : target.Modules)
    (open_set : target.Opens) (section_value : Γ(sheaf, open_set))
    (frame : Scheme.Modules.IsFrame sheaf open_set section_value) :
    Scheme.Modules.IsFrame ((Scheme.Modules.pullback map).obj sheaf) (map ⁻¹ᵁ open_set)
      (amplePullbackLocalSection map sheaf open_set section_value) := by
  apply ampleFrame_of_sectionOnOpen
  let comparison := Scheme.Modules.restrictPullbackObjIso map open_set sheaf
  have pulled_frame := amplePullbackGlobalSection_isFrame_of_globalFrame (map ∣_ open_set)
    (sheaf.restrict open_set.ι) (ampleSectionOnOpen sheaf open_set section_value)
    (ampleSectionOnOpen_isFrame sheaf open_set section_value frame)
  have inverse_frame := ampleFrame_iso_hom comparison.symm ⊤ _ pulled_frame
  rw [← amplePullbackLocalSection_restrictPullbackObjIso map sheaf open_set section_value] at inverse_frame
  change Scheme.Modules.IsFrame _ ⊤
    (Scheme.Modules.Hom.app (comparison.hom ≫ comparison.inv) ⊤ _) at inverse_frame
  rw [Iso.hom_inv_id] at inverse_frame
  exact inverse_frame

def ampleLocalFrameHom (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set)) :
    SheafOfModules.unit (TauCeti.SheafOfModules.ringCatSheaf (target.sheaf.over open_set)) ⟶ sheaf.over open_set :=
  (sheaf.over open_set).unitHomEquiv.symm <| (sheaf.over open_set).val.sectionsMk
    (fun subopen => sheaf.res subopen.unop.hom.le section_value)
    (by
      intro larger smaller inclusion
      change sheaf.res inclusion.unop.left.le (sheaf.res larger.unop.hom.le section_value) = _
      rw [Scheme.Modules.res_res]
      rfl)

theorem ampleLocalFrameHom_app (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set)) (subopen : Over open_set)
    (scalar : Γ(target, subopen.left)) :
    (ampleLocalFrameHom sheaf open_set section_value).val.app (op subopen) scalar =
      scalar • sheaf.res subopen.hom.le section_value := by
  rfl

theorem ampleLocalFrameHom_isIso (sheaf : target.Modules) (open_set : target.Opens)
    (section_value : Γ(sheaf, open_set))
    (frame : Scheme.Modules.IsFrame sheaf open_set section_value) :
    IsIso (ampleLocalFrameHom sheaf open_set section_value) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget _)).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro subopen
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact frame subopen.unop.left subopen.unop.hom.le

def ampleSliceTensorSection {scheme : Scheme.{0}} (open_set : scheme.Opens)
    (first second : SheafOfModules (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)))
    (subopen : Over open_set) (first_value : first.val.obj (op subopen))
    (second_value : second.val.obj (op subopen)) :
    (TauCeti.SheafOfModules.tensorProduct (scheme.sheaf.over open_set)
      first second).val.obj (op subopen) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)).obj)).unit.app
      (first.val ⊗ second.val)).app (op subopen) (first_value ⊗ₜ second_value)

theorem ampleSliceTensorUnitLeft_section {scheme : Scheme.{0}} (open_set : scheme.Opens)
    (sheaf : SheafOfModules (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)))
    (subopen : Over open_set)
    (scalar : scheme.sheaf.obj.obj (op subopen.left)) (value : sheaf.val.obj (op subopen)) :
    (TauCeti.SheafOfModules.tensorProductUnitIsoLeft (scheme.sheaf.over open_set) sheaf).hom.val.app
        (op subopen) (ampleSliceTensorSection open_set
          (SheafOfModules.unit (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)))
          sheaf subopen scalar value) =
      scalar • value := by
  change (TauCeti.SheafOfModules.sheafificationIso
    (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)) sheaf).hom.val.app
    (op subopen) (((PresheafOfModules.sheafification
      (𝟙 (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)).obj)).map
      (λ_ sheaf.val).hom).val.app (op subopen)
        (ampleSliceTensorSection open_set (SheafOfModules.unit
          (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)))
          sheaf subopen scalar value)) = _
  have naturality := congrArg (fun morphism => morphism.app (op subopen) (scalar ⊗ₜ value))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)).obj)).unit.naturality
      (λ_ sheaf.val).hom)
  have rewritten := congrArg (fun tensor_value =>
    (TauCeti.SheafOfModules.sheafificationIso
      (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)) sheaf).hom.val.app
      (op subopen) tensor_value) naturality.symm
  have triangle := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)).obj)).right_triangle_components sheaf
  exact rewritten.trans (congrArg (fun morphism => morphism.app (op subopen)
    ((λ_ sheaf.val).hom.app (op subopen) (scalar ⊗ₜ value))) triangle)

theorem ampleSliceHom_app_isIso {scheme : Scheme.{0}} (open_set : scheme.Opens)
    {first second : SheafOfModules (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set))}
    (morphism : first ⟶ second) [IsIso morphism] (subopen : Over open_set) :
    IsIso (morphism.val.app (op subopen)) := by
  let component := ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map morphism).app
    (op subopen)
  let : IsIso component := inferInstance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso component

theorem ampleTensorSection_isFrame_of_localFrames {scheme : Scheme.{0}}
    (first second : scheme.Modules) (open_set : scheme.Opens)
    (first_value : Γ(first, open_set)) (second_value : Γ(second, open_set))
    (first_frame : Scheme.Modules.IsFrame first open_set first_value)
    (second_frame : Scheme.Modules.IsFrame second open_set second_value) :
    Scheme.Modules.IsFrame (Scheme.Modules.tensor first second) open_set
      (ampleTensorSection first second open_set first_value second_value) := by
  let first_map := ampleLocalFrameHom first open_set first_value
  let second_map := ampleLocalFrameHom second open_set second_value
  let : IsIso first_map := ampleLocalFrameHom_isIso first open_set first_value first_frame
  let : IsIso second_map := ampleLocalFrameHom_isIso second open_set second_value second_frame
  let unit_sheaf := SheafOfModules.unit
    (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set))
  let tensor_comparison := (PresheafOfModules.sheafification
    (𝟙 (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)).obj)).mapIso
      ((SheafOfModules.forget _).mapIso (asIso first_map) ⊗ᵢ
        (SheafOfModules.forget _).mapIso (asIso second_map))
  let unit_comparison := TauCeti.SheafOfModules.tensorProductUnitIsoLeft
    (scheme.sheaf.over open_set) unit_sheaf
  let comparison := unit_comparison.inv ≫ tensor_comparison.hom ≫
    (TauCeti.SheafOfModules.overTensorProductIso scheme.sheaf first second open_set).inv
  let : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map unit_comparison.hom) :=
    inferInstance
  let : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map comparison) :=
    inferInstance
  intro smaller contained
  let subopen := Over.mk (homOfLE contained)
  let : IsIso (unit_comparison.hom.val.app (op subopen)) :=
    ampleSliceHom_app_isIso open_set unit_comparison.hom subopen
  let : IsIso (comparison.val.app (op subopen)) :=
    ampleSliceHom_app_isIso open_set comparison subopen
  have unit_formula : unit_comparison.inv.val.app (op subopen)
      (1 : scheme.sheaf.obj.obj (op smaller)) =
      ampleSliceTensorSection open_set unit_sheaf unit_sheaf subopen
        (1 : scheme.sheaf.obj.obj (op smaller)) (1 : scheme.sheaf.obj.obj (op smaller)) := by
    apply (ConcreteCategory.bijective_of_isIso (unit_comparison.hom.val.app (op subopen))).injective
    change (unit_comparison.inv ≫ unit_comparison.hom).val.app (op subopen)
      (1 : scheme.sheaf.obj.obj (op smaller)) = _
    rw [Iso.inv_hom_id]
    change (1 : scheme.sheaf.obj.obj (op smaller)) = _
    have unit_result := ampleSliceTensorUnitLeft_section open_set unit_sheaf subopen
      (1 : scheme.sheaf.obj.obj (op smaller)) (1 : scheme.sheaf.obj.obj (op smaller))
    rw [one_smul] at unit_result
    exact unit_result.symm
  have tensor_formula : tensor_comparison.hom.val.app (op subopen)
      (ampleSliceTensorSection open_set unit_sheaf unit_sheaf subopen
        (1 : scheme.sheaf.obj.obj (op smaller)) (1 : scheme.sheaf.obj.obj (op smaller))) =
      ampleOverTensorSection first second open_set subopen
        (first.res contained first_value) (second.res contained second_value) := by
    have naturality := congrArg (fun morphism => morphism.app (op subopen)
      ((1 : scheme.sheaf.obj.obj (op smaller)) ⊗ₜ (1 : scheme.sheaf.obj.obj (op smaller))))
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)).obj)).unit.naturality
          (first_map.val ⊗ₘ second_map.val))
    have identity := naturality.symm
    change tensor_comparison.hom.val.app (op subopen)
      (ampleSliceTensorSection open_set unit_sheaf unit_sheaf subopen
        (1 : scheme.sheaf.obj.obj (op smaller)) (1 : scheme.sheaf.obj.obj (op smaller))) =
      ampleOverTensorSection first second open_set subopen
        (first_map.val.app (op subopen) (1 : scheme.sheaf.obj.obj (op smaller)))
        (second_map.val.app (op subopen) (1 : scheme.sheaf.obj.obj (op smaller))) at identity
    simpa only [first_map, second_map, ampleLocalFrameHom_app, one_smul] using identity
  have comparison_one : comparison.val.app (op subopen) (1 : scheme.sheaf.obj.obj (op smaller)) =
      (Scheme.Modules.tensor first second).res contained
        (ampleTensorSection first second open_set first_value second_value) := by
    change (TauCeti.SheafOfModules.overTensorProductIso scheme.sheaf first second open_set).inv.val.app
      (op subopen) (tensor_comparison.hom.val.app (op subopen)
        (unit_comparison.inv.val.app (op subopen) (1 : scheme.sheaf.obj.obj (op smaller)))) = _
    rw [unit_formula, tensor_formula, ampleOverTensorProductIso_inv_section, ampleTensorSection_res]
    rfl
  have formula : (fun scalar : Γ(scheme, smaller) => scalar •
      (Scheme.Modules.tensor first second).res contained
        (ampleTensorSection first second open_set first_value second_value)) =
      fun scalar => comparison.val.app (op subopen) scalar := by
    funext scalar
    rw [← comparison_one]
    have linearity := (comparison.val.app (op subopen)).hom.map_smul scalar
      (1 : scheme.sheaf.obj.obj (op smaller))
    simpa only [smul_eq_mul, mul_one] using linearity.symm
  rw [formula]
  exact ConcreteCategory.bijective_of_isIso _

theorem ampleModuleHom_over_isIso_of_localFrames {scheme : Scheme.{0}}
    {first second : scheme.Modules} (morphism : first ⟶ second) (open_set : scheme.Opens)
    (first_value : Γ(first, open_set)) (second_value : Γ(second, open_set))
    (first_frame : Scheme.Modules.IsFrame first open_set first_value)
    (second_frame : Scheme.Modules.IsFrame second open_set second_value)
    (maps_frame : Scheme.Modules.Hom.app morphism open_set first_value = second_value) :
    IsIso (morphism.over open_set) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget _)).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro subopen
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have naturality : Scheme.Modules.Hom.app morphism subopen.unop.left
      (first.res subopen.unop.hom.le first_value) = second.res subopen.unop.hom.le second_value := by
    rw [← ampleModuleHom_res, maps_frame]
  have formula : (fun scalar : Γ(scheme, subopen.unop.left) =>
      Scheme.Modules.Hom.app morphism subopen.unop.left
        (scalar • first.res subopen.unop.hom.le first_value)) =
      fun scalar => scalar • second.res subopen.unop.hom.le second_value := by
    funext scalar
    rw [Scheme.Modules.Hom.app_smul, naturality]
  have composite := second_frame subopen.unop.left subopen.unop.hom.le
  rw [← formula] at composite
  exact (Function.Bijective.of_comp_iff _
    (first_frame subopen.unop.left subopen.unop.hom.le)).mp composite

theorem ampleTensorPullbackHom_over_isIso_of_localFrames (map : source ⟶ target)
    (first second : target.Modules) (open_set : target.Opens)
    (first_value : Γ(first, open_set)) (second_value : Γ(second, open_set))
    (first_frame : Scheme.Modules.IsFrame first open_set first_value)
    (second_frame : Scheme.Modules.IsFrame second open_set second_value) :
    IsIso ((ampleTensorPullbackHom map first second).over (map ⁻¹ᵁ open_set)) := by
  apply ampleModuleHom_over_isIso_of_localFrames (ampleTensorPullbackHom map first second)
    (map ⁻¹ᵁ open_set)
    (amplePullbackLocalSection map (Scheme.Modules.tensor first second) open_set
      (ampleTensorSection first second open_set first_value second_value))
    (ampleTensorSection ((Scheme.Modules.pullback map).obj first)
      ((Scheme.Modules.pullback map).obj second) (map ⁻¹ᵁ open_set)
      (amplePullbackLocalSection map first open_set first_value)
      (amplePullbackLocalSection map second open_set second_value))
  · exact amplePullbackLocalSection_isFrame map _ _ _
      (ampleTensorSection_isFrame_of_localFrames first second open_set first_value second_value
        first_frame second_frame)
  · exact ampleTensorSection_isFrame_of_localFrames _ _ _ _ _
      (amplePullbackLocalSection_isFrame map first open_set first_value first_frame)
      (amplePullbackLocalSection_isFrame map second open_set second_value second_frame)
  · exact ampleTensorPullbackHom_section map first second open_set first_value second_value

theorem ampleModuleHom_isIso_of_cover {scheme : Scheme.{0}} {first second : scheme.Modules}
    (morphism : first ⟶ second) {Index : Type} (charts : Index → scheme.Opens)
    (covers : IsOpenCover charts) (local_iso : ∀ index, IsIso (morphism.over (charts index))) :
    IsIso morphism := by
  let underlying := (SheafOfModules.toSheaf scheme.ringCatSheaf).map morphism
  have underlying_iso : IsIso underlying := by
    apply CategoryTheory.Sheaf.isIso_of_coversTop
      ((Opens.coversTop_iff scheme charts).mpr covers)
    intro index
    let : IsIso (morphism.over (charts index)) := local_iso index
    exact inferInstanceAs
      (IsIso ((SheafOfModules.toSheaf (scheme.ringCatSheaf.over (charts index))).map
        (morphism.over (charts index))))
  let := underlying_iso
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro open_set
  exact inferInstanceAs (IsIso (underlying.hom.app (op open_set)))

theorem ampleTensorPullbackHom_isIso_of_isInvertible (map : source ⟶ target)
    (first second : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target first]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target second] :
    IsIso (ampleTensorPullbackHom map first second) := by
  let Index := {open_set : target.Opens //
    (∃ first_value : Γ(first, open_set), Scheme.Modules.IsFrame first open_set first_value) ∧
      (∃ second_value : Γ(second, open_set), Scheme.Modules.IsFrame second open_set second_value)}
  let charts : Index → source.Opens := fun index => map ⁻¹ᵁ index.val
  have covers : IsOpenCover charts := by
    apply IsOpenCover.mk
    apply top_unique
    intro point _
    obtain ⟨first_open, first_contains, first_value, first_frame⟩ := Scheme.Modules.exists_frame first (map point)
    obtain ⟨second_open, second_contains, second_value, second_frame⟩ := Scheme.Modules.exists_frame second (map point)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨⟨first_open ⊓ second_open,
      ⟨⟨first.res inf_le_left first_value, first_frame.restrict inf_le_left⟩,
        ⟨second.res inf_le_right second_value, second_frame.restrict inf_le_right⟩⟩⟩,
      first_contains, second_contains⟩
  apply ampleModuleHom_isIso_of_cover (ampleTensorPullbackHom map first second) charts covers
  intro index
  obtain ⟨first_value, first_frame⟩ := index.property.1
  obtain ⟨second_value, second_frame⟩ := index.property.2
  exact ampleTensorPullbackHom_over_isIso_of_localFrames map first second index.val
    first_value second_value first_frame second_frame

def ampleInvertibleTensorPullbackIso (map : source ⟶ target)
    (first second : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target first]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target second] :
    (Scheme.Modules.pullback map).obj (Scheme.Modules.tensor first second) ≅
      Scheme.Modules.tensor ((Scheme.Modules.pullback map).obj first)
        ((Scheme.Modules.pullback map).obj second) := by
  letI := ampleTensorPullbackHom_isIso_of_isInvertible map first second
  exact asIso (ampleTensorPullbackHom map first second)

def ampleInvertibleTensorPowerPullbackIso (map : source ⟶ target)
    (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf] :
    (exponent : ℕ) → (Scheme.Modules.pullback map).obj (Scheme.Modules.tensorPow sheaf exponent) ≅
      Scheme.Modules.tensorPow ((Scheme.Modules.pullback map).obj sheaf) exponent
  | 0 => Scheme.Modules.pullbackObjUnitIso map
  | exponent + 1 =>
      ampleInvertibleTensorPullbackIso map (Scheme.Modules.tensorPow sheaf exponent) sheaf ≪≫
        ampleTensorSheafIso (ampleInvertibleTensorPowerPullbackIso map sheaf exponent) (Iso.refl _)

end BondalThomsen
