module

public import BondalThomsen.LineBundle.AmpleLineBundleGlobalGeneration
public import BondalThomsen.LineBundle.AmpleLineBundleSchemeIso
public import BondalThomsen.Toric.Projective.GlobalSheafIso

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace BondalThomsen

variable {source target : Scheme.{0}}

def amplePullbackGlobalSection (map : source ⟶ target) (sheaf : target.Modules)
    (section_value : Γ(sheaf, ⊤)) : Γ((Scheme.Modules.pullback map).obj sheaf, ⊤) :=
  Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
    ⊤ section_value

theorem amplePullbackGlobalSection_sectionHom (map : source ⟶ target) (sheaf : target.Modules)
    (section_value : Γ(sheaf, ⊤)) :
    amplePullbackGlobalSection map sheaf section_value =
      Scheme.Modules.Hom.app
        (modulePullbackSectionHom map (moduleGlobalSectionHom sheaf section_value)) ⊤
          (1 : Γ(source, ⊤)) := by
  have value := modulePullbackSectionHom_appLE_one map
    (moduleGlobalSectionHom sheaf section_value) ⊤ ⊤ le_top
  rw [moduleGlobalSectionHom_app, one_smul] at value
  have identity : homOfLE (show (⊤ : target.Opens) ≤ ⊤ from le_top) = 𝟙 ⊤ := rfl
  rw [identity, op_id, sheaf.presheaf.map_id] at value
  change _ = ((Scheme.Modules.pullback map).obj sheaf).res le_top
    (amplePullbackGlobalSection map sheaf section_value) at value
  rw [Scheme.Modules.res_self] at value
  exact value.symm

theorem amplePulledSection_isFrame_of_localIso (map : source ⟶ target) (sheaf : target.Modules)
    (section_value : Γ(sheaf, ⊤)) (open_set : source.Opens)
    (local_iso : IsIso ((modulePullbackSectionHom map
      (moduleGlobalSectionHom sheaf section_value)).over open_set)) :
    Scheme.Modules.IsFrame ((Scheme.Modules.pullback map).obj sheaf) open_set
      (((Scheme.Modules.pullback map).obj sheaf).res le_top
        (amplePullbackGlobalSection map sheaf section_value)) := by
  let := local_iso
  intro smaller inclusion
  let section_map := modulePullbackSectionHom map (moduleGlobalSectionHom sheaf section_value)
  let : IsIso (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (section_map.over open_set)).app (op (Over.mk (homOfLE inclusion)))) := inferInstance
  have value := modulePullbackSectionHom_appLE_one map
    (moduleGlobalSectionHom sheaf section_value) ⊤ smaller le_top
  rw [moduleGlobalSectionHom_app, one_smul] at value
  have identity : homOfLE (show (⊤ : target.Opens) ≤ ⊤ from le_top) = 𝟙 ⊤ := rfl
  rw [identity, op_id, sheaf.presheaf.map_id] at value
  change Scheme.Modules.Hom.app section_map smaller (1 : Γ(source, smaller)) =
    ((Scheme.Modules.pullback map).obj sheaf).res le_top
      (amplePullbackGlobalSection map sheaf section_value) at value
  rw [Scheme.Modules.res_res]
  have formula : (fun scalar : Γ(source, smaller) =>
      scalar • ((Scheme.Modules.pullback map).obj sheaf).res le_top
        (amplePullbackGlobalSection map sheaf section_value)) =
      fun scalar => Scheme.Modules.Hom.app (modulePullbackSectionHom map
        (moduleGlobalSectionHom sheaf section_value)) smaller scalar := by
    funext scalar
    rw [← value]
    rw [← Scheme.Modules.Hom.app_smul]
    simp only [smul_eq_mul, mul_one]
    rfl
  rw [formula]
  exact ConcreteCategory.bijective_of_isIso (((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).map (section_map.over open_set)).app
      (op (Over.mk (homOfLE inclusion))))

theorem amplePullbackGlobalSection_naturality (map : source ⟶ target)
    {first second : target.Modules} (morphism : first ⟶ second)
    (section_value : Γ(first, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback map).map morphism) ⊤
        (amplePullbackGlobalSection map first section_value) =
      amplePullbackGlobalSection map second (Scheme.Modules.Hom.app morphism ⊤ section_value) := by
  exact (congrArg (fun comparison => Scheme.Modules.Hom.app comparison ⊤ section_value)
    ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.naturality morphism)).symm

theorem amplePullbackGlobalSection_comp {middle : Scheme.{0}}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (sheaf : target.Modules) (section_value : Γ(sheaf, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp first second).app sheaf).hom ⊤
        (amplePullbackGlobalSection first ((Scheme.Modules.pullback second).obj sheaf)
          (amplePullbackGlobalSection second sheaf section_value)) =
      amplePullbackGlobalSection (first ≫ second) sheaf section_value := by
  have compatibility := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction second).comp
      (Scheme.Modules.pullbackPushforwardAdjunction first))
    (Scheme.Modules.pullbackPushforwardAdjunction (first ≫ second))
    (Scheme.Modules.pullbackComp first second).inv sheaf
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at compatibility
  have inverse_formula := congrArg (fun morphism =>
    Scheme.Modules.Hom.app morphism ⊤ section_value) compatibility
  have inverse_value : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp first second).app sheaf).inv ⊤
      (amplePullbackGlobalSection (first ≫ second) sheaf section_value) =
      amplePullbackGlobalSection first ((Scheme.Modules.pullback second).obj sheaf)
        (amplePullbackGlobalSection second sheaf section_value) := by
    exact inverse_formula.symm
  rw [← inverse_value]
  change Scheme.Modules.Hom.app (((Scheme.Modules.pullbackComp first second).app sheaf).inv ≫
    ((Scheme.Modules.pullbackComp first second).app sheaf).hom) ⊤ _ = _
  rw [Iso.inv_hom_id]
  rfl

theorem amplePullbackGlobalSection_restrict (inclusion : source ⟶ target)
    [IsOpenImmersion inclusion] (sheaf : target.Modules) (section_value : Γ(sheaf, ⊤)) :
    ((Scheme.Modules.restrictFunctorIsoPullback inclusion).app sheaf).hom.app ⊤
        (schemeRestrictedGlobalSection inclusion sheaf section_value) =
      amplePullbackGlobalSection inclusion sheaf section_value := by
  rw [amplePullbackGlobalSection_sectionHom, modulePullbackSectionHom_restrict]
  change Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback inclusion).app sheaf).hom ⊤
    ((sheaf.restrictAppIso inclusion ⊤).inv
      (sheaf.res (inclusion.image_preimage_le ⊤) section_value)) =
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback inclusion).app sheaf).hom ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor inclusion).map
        (moduleGlobalSectionHom sheaf section_value)) ⊤
          (Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso inclusion).inv ⊤
            (1 : Γ(source, ⊤))))
  congr 1
  change sheaf.presheaf.map (homOfLE _).op section_value =
    (inclusion.appIso ⊤).inv (1 : Γ(source, ⊤)) •
      sheaf.presheaf.map (homOfLE (show inclusion ''ᵁ (⊤ : source.Opens) ≤ ⊤ from le_top)).op section_value
  rw [map_one, one_smul]

theorem amplePullbackGlobalSection_nonvanishingLocus_of_globalFrame
    (map : source ⟶ target) (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (frame_value : Γ(sheaf, ⊤)) (frame : Scheme.Modules.IsFrame sheaf ⊤ frame_value)
    (section_value : Γ(sheaf, ⊤)) :
    ((Scheme.Modules.pullback map).obj sheaf).nonvanishingLocus
        (amplePullbackGlobalSection map sheaf section_value) =
      map ⁻¹ᵁ sheaf.nonvanishingLocus section_value := by
  have frame_iso : IsIso (moduleGlobalSectionHom sheaf frame_value) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro open_set
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun scalar : Γ(target, open_set) =>
      scalar • sheaf.res (show open_set ≤ ⊤ from le_top) frame_value)
    exact frame open_set le_top
  let := frame_iso
  have pulled_iso : IsIso (modulePullbackSectionHom map (moduleGlobalSectionHom sheaf frame_value)) := by
    unfold modulePullbackSectionHom
    infer_instance
  let := pulled_iso
  have local_iso : IsIso ((modulePullbackSectionHom map
      (moduleGlobalSectionHom sheaf frame_value)).over ⊤) := inferInstance
  have pulled_frame := amplePulledSection_isFrame_of_localIso map sheaf frame_value ⊤ local_iso
  rw [Scheme.Modules.res_self] at pulled_frame
  let coefficient := frame.coord le_rfl section_value
  let pulled_coefficient_value : Γ(source, ⊤) :=
    map.appLE ⊤ ⊤ le_top coefficient
  have coefficient_relation : amplePullbackGlobalSection map sheaf section_value =
      pulled_coefficient_value • amplePullbackGlobalSection map sheaf frame_value := by
    have relation := modulePullbackSectionHom_coefficient map
      (moduleGlobalSectionHom sheaf frame_value) (moduleGlobalSectionHom sheaf section_value)
      ⊤ ⊤ le_top coefficient (by
        rw [moduleGlobalSectionHom_app, moduleGlobalSectionHom_app, one_smul, one_smul]
        change sheaf.res le_top section_value = coefficient • sheaf.res le_top frame_value
        rw [Scheme.Modules.res_self, Scheme.Modules.res_self]
        simpa only [Scheme.Modules.res_self] using
          (frame.coord_smul_frame le_rfl section_value).symm)
    rw [← amplePullbackGlobalSection_sectionHom, ← amplePullbackGlobalSection_sectionHom] at relation
    exact relation
  have pulled_coefficient : pulled_frame.coord le_rfl
      (((Scheme.Modules.pullback map).obj sheaf).res le_top
        (amplePullbackGlobalSection map sheaf section_value)) = pulled_coefficient_value := by
    apply (pulled_frame _ le_rfl).injective
    dsimp only
    rw [pulled_frame.coord_smul_frame, Scheme.Modules.res_self, Scheme.Modules.res_self]
    exact coefficient_relation
  have pulled_locus := pulled_frame.inf_nonvanishingLocus_eq_basicOpen _
    (amplePullbackGlobalSection map sheaf section_value)
  have original_locus := frame.inf_nonvanishingLocus_eq_basicOpen _ section_value
  rw [top_inf_eq, pulled_coefficient] at pulled_locus
  rw [top_inf_eq, Scheme.Modules.res_self] at original_locus
  have basic_equal : source.basicOpen pulled_coefficient_value = map ⁻¹ᵁ target.basicOpen coefficient := by
    change source.basicOpen (source.presheaf.map (homOfLE le_top).op (map.app ⊤ coefficient)) = _
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    simp only [top_inf_eq]
  exact pulled_locus.trans (basic_equal.trans
    (congrArg (fun open_set => map ⁻¹ᵁ open_set) original_locus.symm))

theorem amplePullbackGlobalSection_congr {first second : source ⟶ target}
    (equal : first = second) (sheaf : target.Modules) (section_value : Γ(sheaf, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr equal).app sheaf).hom ⊤
        (amplePullbackGlobalSection first sheaf section_value) =
      amplePullbackGlobalSection second sheaf section_value := by
  subst second
  rfl

theorem amplePullbackGlobalSection_restrictPullbackObjIso
    (map : source ⟶ target) (sheaf : target.Modules) (section_value : Γ(sheaf, ⊤))
    (open_set : target.Opens) :
    Scheme.Modules.Hom.app (Scheme.Modules.restrictPullbackObjIso map open_set sheaf).hom ⊤
        (schemeRestrictedGlobalSection (map ⁻¹ᵁ open_set).ι
          ((Scheme.Modules.pullback map).obj sheaf) (amplePullbackGlobalSection map sheaf section_value)) =
      amplePullbackGlobalSection (map ∣_ open_set) (sheaf.restrict open_set.ι)
        (schemeRestrictedGlobalSection open_set.ι sheaf section_value) := by
  unfold Scheme.Modules.restrictPullbackObjIso
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullback (map ∣_ open_set)).map
      ((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).inv) ⊤
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).inv ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr (morphismRestrict_ι map open_set).symm).app sheaf).hom ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp (map ⁻¹ᵁ open_set).ι map).app sheaf).hom ⊤
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.restrictFunctorIsoPullback (map ⁻¹ᵁ open_set).ι).app _).hom ⊤ _)))) = _
  rw [amplePullbackGlobalSection_restrict, amplePullbackGlobalSection_comp,
    amplePullbackGlobalSection_congr]
  have inverse_comp : Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).inv ⊤
        (amplePullbackGlobalSection ((map ∣_ open_set) ≫ open_set.ι) sheaf section_value) =
      amplePullbackGlobalSection (map ∣_ open_set) ((Scheme.Modules.pullback open_set.ι).obj sheaf)
        (amplePullbackGlobalSection open_set.ι sheaf section_value) := by
    rw [← amplePullbackGlobalSection_comp (map ∣_ open_set) open_set.ι sheaf section_value]
    change Scheme.Modules.Hom.app (((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).hom ≫
      ((Scheme.Modules.pullbackComp (map ∣_ open_set) open_set.ι).app sheaf).inv) ⊤ _ = _
    rw [Iso.hom_inv_id]
    rfl
  rw [inverse_comp, amplePullbackGlobalSection_naturality]
  congr 1
  rw [← amplePullbackGlobalSection_restrict open_set.ι sheaf section_value]
  change Scheme.Modules.Hom.app (((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).hom ≫
    ((Scheme.Modules.restrictFunctorIsoPullback open_set.ι).app sheaf).inv) ⊤ _ = _
  rw [Iso.hom_inv_id]
  rfl

theorem amplePullbackGlobalSection_nonvanishingLocus
    (map : source ⟶ target) (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (section_value : Γ(sheaf, ⊤)) :
    ((Scheme.Modules.pullback map).obj sheaf).nonvanishingLocus
        (amplePullbackGlobalSection map sheaf section_value) =
      map ⁻¹ᵁ sheaf.nonvanishingLocus section_value := by
  apply Opens.ext
  ext point
  obtain ⟨open_set, contains, frame_value, frame⟩ := Scheme.Modules.exists_frame sheaf (map point)
  have restricted_frame := schemeRestrictedSection_isFrame open_set.ι sheaf frame
  have top_equal : open_set.ι ⁻¹ᵁ open_set = ⊤ := by
    ext local_point
    exact iff_true_intro local_point.property
  obtain ⟨restricted_value, local_frame⟩ : ∃ restricted_value : Γ(sheaf.restrict open_set.ι, ⊤),
      Scheme.Modules.IsFrame (sheaf.restrict open_set.ι) ⊤ restricted_value := by
    have existence : ∃ restricted_value : Γ(sheaf.restrict open_set.ι, open_set.ι ⁻¹ᵁ open_set),
        Scheme.Modules.IsFrame (sheaf.restrict open_set.ι) (open_set.ι ⁻¹ᵁ open_set) restricted_value :=
      ⟨_, restricted_frame⟩
    rwa [top_equal] at existence
  let comparison := Scheme.Modules.restrictPullbackObjIso map open_set sheaf
  have local_locus := amplePullbackGlobalSection_nonvanishingLocus_of_globalFrame
    (map ∣_ open_set) (sheaf.restrict open_set.ι) restricted_value local_frame
      (schemeRestrictedGlobalSection open_set.ι sheaf section_value)
  have comparison_locus := Scheme.Modules.nonvanishingLocus_iso comparison
    (schemeRestrictedGlobalSection (map ⁻¹ᵁ open_set).ι
      ((Scheme.Modules.pullback map).obj sheaf) (amplePullbackGlobalSection map sheaf section_value))
  rw [amplePullbackGlobalSection_restrictPullbackObjIso, local_locus,
    schemeRestrictedGlobalSection_nonvanishingLocus, schemeRestrictedGlobalSection_nonvanishingLocus]
    at comparison_locus
  have local_point : point ∈ map ⁻¹ᵁ open_set := contains
  have point_equivalence := congrArg
    (fun locus => (⟨point, local_point⟩ : map ⁻¹ᵁ open_set) ∈ locus) comparison_locus
  have mapped_point : open_set.ι ((map ∣_ open_set) (⟨point, local_point⟩ : map ⁻¹ᵁ open_set)) = map point := by
    have compatibility := congrArg (fun morphism => morphism
      (⟨point, local_point⟩ : map ⁻¹ᵁ open_set)) (morphismRestrict_ι map open_set)
    simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using compatibility
  have equivalence := (eq_iff_iff.mp point_equivalence).symm
  change point ∈ ((Scheme.Modules.pullback map).obj sheaf).nonvanishingLocus
    (amplePullbackGlobalSection map sheaf section_value) ↔
      open_set.ι ((map ∣_ open_set) (⟨point, local_point⟩ : map ⁻¹ᵁ open_set)) ∈
        sheaf.nonvanishingLocus section_value at equivalence
  rwa [mapped_point] at equivalence

end BondalThomsen

