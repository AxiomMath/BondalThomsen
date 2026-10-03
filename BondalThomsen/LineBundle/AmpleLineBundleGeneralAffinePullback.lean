module

public import BondalThomsen.LineBundle.AmpleLineBundleAffinePullback

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory

noncomputable section

namespace BondalThomsen

variable {scheme : Scheme.{0}}

theorem ampleModuleApp_val {first second : scheme.Modules} (morphism : first ⟶ second)
    (open_set : scheme.Opens) (value : Γ(first, open_set)) :
    Scheme.Modules.Hom.app morphism open_set value =
      morphism.val.app (op open_set) value := by
  rfl

def ampleTensorSection (first second : scheme.Modules) (open_set : scheme.Opens)
    (first_value : first.val.obj (op open_set)) (second_value : second.val.obj (op open_set)) :
    (Scheme.Modules.tensor first second).val.obj (op open_set) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).unit.app
    (first.val ⊗ second.val)).app (op open_set) (first_value ⊗ₜ second_value)

theorem ampleTensorSection_res (first second : scheme.Modules)
    {smaller larger : scheme.Opens} (contained : smaller ≤ larger)
    (first_value : Γ(first, larger)) (second_value : Γ(second, larger)) :
    (Scheme.Modules.tensor first second).res contained
        (ampleTensorSection first second larger first_value second_value) =
      ampleTensorSection first second smaller (first.res contained first_value)
        (second.res contained second_value) := by
  have naturality := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).unit.app
      (first.val ⊗ second.val)) (homOfLE contained).op (first_value ⊗ₜ second_value)
  exact naturality.symm

def ampleTensorSheafIso {first second third fourth : scheme.Modules}
    (first_iso : first ≅ third) (second_iso : second ≅ fourth) :
    Scheme.Modules.tensor first second ≅ Scheme.Modules.tensor third fourth :=
  Scheme.Modules.isoOfSheafIso scheme
    ((PresheafOfModules.sheafification (𝟙 scheme.ringCatSheaf.obj)).mapIso
      ((SheafOfModules.forget _).mapIso
        (Scheme.Modules.tensorPowerUnderlyingSheafIso first_iso) ⊗ᵢ
      (SheafOfModules.forget _).mapIso
        (Scheme.Modules.tensorPowerUnderlyingSheafIso second_iso)))

theorem ampleTensorSection_add_left (first second : scheme.Modules) (open_set : scheme.Opens)
    (first_value other_value : Γ(first, open_set)) (second_value : Γ(second, open_set)) :
    ampleTensorSection first second open_set (first_value + other_value) second_value =
      ampleTensorSection first second open_set first_value second_value +
        ampleTensorSection first second open_set other_value second_value := by
  unfold ampleTensorSection
  rw [TensorProduct.add_tmul, map_add]

theorem ampleTensorSection_add_right (first second : scheme.Modules) (open_set : scheme.Opens)
    (first_value : Γ(first, open_set)) (second_value other_value : Γ(second, open_set)) :
    ampleTensorSection first second open_set first_value (second_value + other_value) =
      ampleTensorSection first second open_set first_value second_value +
        ampleTensorSection first second open_set first_value other_value := by
  unfold ampleTensorSection
  rw [TensorProduct.tmul_add, map_add]

theorem ampleTensorSection_smul_left (first second : scheme.Modules) (open_set : scheme.Opens)
    (scalar : scheme.sheaf.obj.obj (op open_set))
    (first_value : first.val.obj (op open_set))
    (second_value : second.val.obj (op open_set)) :
    ampleTensorSection first second open_set (scalar • first_value) second_value =
      scalar • ampleTensorSection first second open_set first_value second_value := by
  unfold ampleTensorSection
  rw [← TensorProduct.smul_tmul' (R := scheme.sheaf.obj.obj (op open_set))
    (R' := scheme.sheaf.obj.obj (op open_set)) scalar first_value second_value]
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).unit.app
    (first.val ⊗ second.val)).app (op open_set) |>.hom.map_smul scalar _

theorem ampleTensorSection_smul_right (first second : scheme.Modules) (open_set : scheme.Opens)
    (scalar : scheme.sheaf.obj.obj (op open_set))
    (first_value : first.val.obj (op open_set))
    (second_value : second.val.obj (op open_set)) :
    ampleTensorSection first second open_set first_value (scalar • second_value) =
      scalar • ampleTensorSection first second open_set first_value second_value := by
  unfold ampleTensorSection
  rw [TensorProduct.tmul_smul (R := scheme.sheaf.obj.obj (op open_set))
    (R' := scheme.sheaf.obj.obj (op open_set)) scalar first_value second_value]
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).unit.app
    (first.val ⊗ second.val)).app (op open_set) |>.hom.map_smul scalar _

variable {source target : Scheme.{0}}

def ampleTensorPullbackPresheafHom (map : source ⟶ target) (first second : target.Modules) :
    first.val ⊗ second.val ⟶
      ((Scheme.Modules.pushforward map).obj (Scheme.Modules.tensor
        ((Scheme.Modules.pullback map).obj first) ((Scheme.Modules.pullback map).obj second))).val where
  app open_set := ModuleCat.MonoidalCategory.tensorLift
    (fun first_value second_value => ampleTensorSection
      ((Scheme.Modules.pullback map).obj first) ((Scheme.Modules.pullback map).obj second)
      (map ⁻¹ᵁ open_set.unop)
      (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app first).val.app open_set first_value)
      (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app second).val.app open_set second_value))
    (by
      intro first_value other_value second_value
      rw [map_add, ampleTensorSection_add_left])
    (by
      intro scalar first_value second_value
      rw [map_smul]
      exact ampleTensorSection_smul_left _ _ _ _ _ _)
    (by
      intro first_value second_value other_value
      rw [map_add, ampleTensorSection_add_right])
    (by
      intro scalar first_value second_value
      rw [map_smul]
      exact ampleTensorSection_smul_right _ _ _ _ _ _)
  naturality {larger smaller} inclusion := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro first_value second_value
    change ampleTensorSection ((Scheme.Modules.pullback map).obj first)
      ((Scheme.Modules.pullback map).obj second) (map ⁻¹ᵁ smaller.unop)
      (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app first).val.app smaller
        (first.val.map inclusion first_value))
      (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app second).val.app smaller
        (second.val.map inclusion second_value)) =
      (Scheme.Modules.tensor ((Scheme.Modules.pullback map).obj first)
        ((Scheme.Modules.pullback map).obj second)).res
        (show map ⁻¹ᵁ smaller.unop ≤ map ⁻¹ᵁ larger.unop from
          fun point member => inclusion.unop.le member)
        (ampleTensorSection ((Scheme.Modules.pullback map).obj first)
          ((Scheme.Modules.pullback map).obj second) (map ⁻¹ᵁ larger.unop)
          (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app first).val.app larger first_value)
          (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app second).val.app larger second_value))
    rw [ampleTensorSection_res]
    congr 1
    · exact PresheafOfModules.naturality_apply _ inclusion first_value
    · exact PresheafOfModules.naturality_apply _ inclusion second_value

def ampleTensorPullbackTranspose (map : source ⟶ target) (first second : target.Modules) :
    Scheme.Modules.tensor first second ⟶
      (Scheme.Modules.pushforward map).obj (Scheme.Modules.tensor
        ((Scheme.Modules.pullback map).obj first) ((Scheme.Modules.pullback map).obj second)) :=
  ⟨((PresheafOfModules.sheafificationHomEquiv (𝟙 target.ringCatSheaf.obj)).symm
    (ampleTensorPullbackPresheafHom map first second)).val⟩

def ampleTensorPullbackHom (map : source ⟶ target) (first second : target.Modules) :
    (Scheme.Modules.pullback map).obj (Scheme.Modules.tensor first second) ⟶
      Scheme.Modules.tensor ((Scheme.Modules.pullback map).obj first)
        ((Scheme.Modules.pullback map).obj second) :=
  (Scheme.Modules.pullbackPushforwardAdjunction map).homEquiv _ _ |>.symm
    (ampleTensorPullbackTranspose map first second)

theorem ampleSheafificationHom_section {presheaf : PresheafOfModules scheme.ringCatSheaf.obj}
    {sheaf : scheme.Modules} (morphism : presheaf ⟶ sheaf.val)
    (open_set : scheme.Opens) (value : presheaf.obj (op open_set)) :
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 scheme.ringCatSheaf.obj)).symm
      morphism).val.app (op open_set)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).unit.app
          presheaf).app (op open_set) value) = morphism.app (op open_set) value := by
  have identity := (PresheafOfModules.sheafificationHomEquiv (𝟙 scheme.ringCatSheaf.obj)).apply_symm_apply
    morphism
  exact congrArg (fun section_map => section_map.app (op open_set) value) identity

theorem ampleTensorPullbackTranspose_section (map : source ⟶ target)
    (first second : target.Modules) (open_set : target.Opens)
    (first_value : Γ(first, open_set)) (second_value : Γ(second, open_set)) :
    Scheme.Modules.Hom.app (ampleTensorPullbackTranspose map first second) open_set
        (ampleTensorSection first second open_set first_value second_value) =
      ampleTensorSection ((Scheme.Modules.pullback map).obj first)
        ((Scheme.Modules.pullback map).obj second) (map ⁻¹ᵁ open_set)
        (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app first).val.app
          (op open_set) first_value)
        (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app second).val.app
          (op open_set) second_value) := by
  rw [show Scheme.Modules.Hom.app (ampleTensorPullbackTranspose map first second) open_set
      (ampleTensorSection first second open_set first_value second_value) =
      (ampleTensorPullbackPresheafHom map first second).app (op open_set)
        (first_value ⊗ₜ second_value) from
    ampleSheafificationHom_section (ampleTensorPullbackPresheafHom map first second)
      open_set (first_value ⊗ₜ second_value)]
  rfl

theorem ampleTensorPullbackHom_section (map : source ⟶ target)
    (first second : target.Modules) (open_set : target.Opens)
    (first_value : Γ(first, open_set)) (second_value : Γ(second, open_set)) :
    Scheme.Modules.Hom.app (ampleTensorPullbackHom map first second) (map ⁻¹ᵁ open_set)
      (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app
        (Scheme.Modules.tensor first second)).val.app (op open_set)
        (ampleTensorSection first second open_set first_value second_value)) =
      ampleTensorSection ((Scheme.Modules.pullback map).obj first)
        ((Scheme.Modules.pullback map).obj second) (map ⁻¹ᵁ open_set)
        (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app first).val.app
          (op open_set) first_value)
        (((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app second).val.app
          (op open_set) second_value) := by
  have transpose := ((Scheme.Modules.pullbackPushforwardAdjunction map).homEquiv _ _).apply_symm_apply
    (ampleTensorPullbackTranspose map first second)
  have identity := congrArg (fun morphism : Scheme.Modules.tensor first second ⟶
      (Scheme.Modules.pushforward map).obj (Scheme.Modules.tensor
        ((Scheme.Modules.pullback map).obj first) ((Scheme.Modules.pullback map).obj second)) =>
      morphism.val.app (op open_set)
        (ampleTensorSection first second open_set first_value second_value)) transpose
  exact identity.trans (ampleTensorPullbackTranspose_section map first second
    open_set first_value second_value)

theorem amplePullbackGlobalSection_isFrame_of_globalFrame
    (map : source ⟶ target) (sheaf : target.Modules) (section_value : Γ(sheaf, ⊤))
    (frame : Scheme.Modules.IsFrame sheaf ⊤ section_value) :
    Scheme.Modules.IsFrame ((Scheme.Modules.pullback map).obj sheaf) ⊤
      (amplePullbackGlobalSection map sheaf section_value) := by
  have section_iso : IsIso (moduleGlobalSectionHom sheaf section_value) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro open_set
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact frame open_set le_top
  let := section_iso
  have pulled_iso : IsIso (modulePullbackSectionHom map
      (moduleGlobalSectionHom sheaf section_value)) := by
    unfold modulePullbackSectionHom
    infer_instance
  have local_iso : IsIso ((modulePullbackSectionHom map
      (moduleGlobalSectionHom sheaf section_value)).over ⊤) := by
    let := pulled_iso
    infer_instance
  have result := amplePulledSection_isFrame_of_localIso map sheaf section_value ⊤ local_iso
  rwa [Scheme.Modules.res_self] at result

def ampleOverTensorSection (first second : scheme.Modules) (open_set : scheme.Opens)
    (subopen : Over open_set) (first_value : Γ(first, subopen.left))
    (second_value : Γ(second, subopen.left)) :
    (TauCeti.SheafOfModules.tensorProduct (scheme.sheaf.over open_set)
      (first.over open_set) (second.over open_set)).val.obj (op subopen) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over open_set)).obj)).unit.app
      ((first.over open_set).val ⊗ (second.over open_set).val)).app (op subopen)
        (first_value ⊗ₜ second_value)

theorem ampleOverTensorProductIso_inv_section (first second : scheme.Modules)
    (open_set : scheme.Opens) (subopen : Over open_set)
    (first_value : Γ(first, subopen.left)) (second_value : Γ(second, subopen.left)) :
    (TauCeti.SheafOfModules.overTensorProductIso scheme.sheaf first second open_set).inv.val.app
      (op subopen) (ampleOverTensorSection first second open_set subopen first_value second_value) =
      ampleTensorSection first second subopen.left first_value second_value := by
  let tensor_presheaf := first.val ⊗ second.val
  let pushed_presheaf := (PresheafOfModules.pushforward₀OfCommRingCat
    (Over.forget open_set) scheme.sheaf.obj).obj tensor_presheaf
  let tensor_comparison := Functor.Monoidal.μIso
    (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget open_set) scheme.sheaf.obj)
      first.val second.val
  let push_unit := TauCeti.SheafOfModules.pushforwardToSheafify
    (J := (Opens.grothendieckTopology scheme).over open_set)
    (K := Opens.grothendieckTopology scheme)
    (Over.forget open_set) scheme.ringCatSheaf tensor_presheaf
  let sheafification := PresheafOfModules.sheafification
    (𝟙 (scheme.ringCatSheaf.over open_set).obj)
  let pushed_tensor := (Scheme.Modules.tensor first second).over open_set
  have first_naturality := congrArg (fun morphism => morphism.app (op subopen)
    (first_value ⊗ₜ second_value))
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (scheme.ringCatSheaf.over open_set).obj)).unit.naturality tensor_comparison.hom)
  have second_naturality := congrArg (fun morphism => morphism.app (op subopen)
    (tensor_comparison.hom.app (op subopen) (first_value ⊗ₜ second_value)))
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (scheme.ringCatSheaf.over open_set).obj)).unit.naturality push_unit)
  have triangle := congrArg (fun morphism => morphism.app (op subopen)
    (push_unit.app (op subopen)
      (tensor_comparison.hom.app (op subopen) (first_value ⊗ₜ second_value))))
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (scheme.ringCatSheaf.over open_set).obj)).right_triangle_components pushed_tensor)
  change (TauCeti.SheafOfModules.sheafificationIso
      (scheme.ringCatSheaf.over open_set) pushed_tensor).hom.val.app (op subopen)
    ((sheafification.map push_unit).val.app (op subopen)
      ((sheafification.map tensor_comparison.hom).val.app (op subopen)
        (ampleOverTensorSection first second open_set subopen first_value second_value))) = _
  have first_step := congrArg (fun value =>
    (TauCeti.SheafOfModules.sheafificationIso
      (scheme.ringCatSheaf.over open_set) pushed_tensor).hom.val.app (op subopen)
        ((sheafification.map push_unit).val.app (op subopen) value)) first_naturality.symm
  have second_step := congrArg (fun value =>
    (TauCeti.SheafOfModules.sheafificationIso
      (scheme.ringCatSheaf.over open_set) pushed_tensor).hom.val.app (op subopen) value)
        second_naturality.symm
  exact first_step.trans (second_step.trans triangle)

end BondalThomsen
