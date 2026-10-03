module

public import BondalThomsen.Toric.Positivity.VeryAmpleToAmple
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped CategoryTheory.MonoidalCategory

universe schemeUniverse

noncomputable section

namespace BondalThomsen

variable {scheme : Scheme.{schemeUniverse}}

def ampleGlobalSectionHom (sheaf : scheme.Modules) (section_value : Γ(sheaf, ⊤)) :
    SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf :=
  sheaf.unitHomEquiv.symm <| sheaf.val.sectionsMk
    (fun open_set => sheaf.presheaf.map (homOfLE le_top).op section_value)
    (by
      intro larger smaller inclusion
      change sheaf.presheaf.map inclusion
        (sheaf.presheaf.map (homOfLE le_top).op section_value) = _
      rw [← ConcreteCategory.comp_apply, ← sheaf.presheaf.map_comp]
      rfl)

theorem moduleFrame_of_isUnit_coordinate {sheaf : scheme.Modules} {open_set : scheme.Opens}
    {frame_section : Γ(sheaf, open_set)}
    (frame : Scheme.Modules.IsFrame sheaf open_set frame_section)
    {section_value : Γ(sheaf, open_set)}
    (unit : IsUnit (frame.coord le_rfl section_value)) :
    Scheme.Modules.IsFrame sheaf open_set section_value := by
  intro smaller inclusion
  have relation : sheaf.res inclusion section_value =
      scheme.presheaf.map (homOfLE inclusion).op (frame.coord le_rfl section_value) •
        sheaf.res inclusion frame_section := by
    have equal := congrArg (sheaf.res inclusion) (frame.coord_smul_frame le_rfl section_value)
    rw [Scheme.Modules.res_self] at equal
    change sheaf.presheaf.map (homOfLE inclusion).op
      (frame.coord le_rfl section_value • frame_section) = _ at equal
    rw [Scheme.Modules.map_smul] at equal
    exact equal.symm
  obtain ⟨local_unit, unit_equal⟩ := unit.map
    (scheme.presheaf.map (homOfLE inclusion).op).hom
  have formula : (fun scalar : Γ(scheme, smaller) => scalar • sheaf.res inclusion section_value) =
      (fun scalar : Γ(scheme, smaller) => scalar • sheaf.res inclusion frame_section) ∘
        (fun scalar => scalar * (local_unit : Γ(scheme, smaller))) := by
    funext scalar
    dsimp only [Function.comp_apply]
    rw [relation, ← unit_equal, mul_smul]
  rw [formula]
  exact (frame smaller inclusion).comp (Units.mulRight_bijective local_unit)

theorem exists_frame_neighborhood_of_nonvanishing (sheaf : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme sheaf]
    (section_value : Γ(sheaf, ⊤)) (point : scheme)
    (nonvanishing : point ∈ sheaf.nonvanishingLocus section_value) :
    ∃ open_set : scheme.Opens, point ∈ open_set ∧
      Scheme.Modules.IsFrame sheaf open_set (sheaf.res le_top section_value) := by
  obtain ⟨open_set, contains, frame_section, frame⟩ := Scheme.Modules.exists_frame sheaf point
  let coefficient := frame.coord le_rfl (sheaf.res le_top section_value)
  have locus := frame.inf_nonvanishingLocus_eq_basicOpen sheaf section_value
  have basic_member : point ∈ scheme.basicOpen coefficient := locus ▸ ⟨contains, nonvanishing⟩
  have germ_unit := (scheme.mem_basicOpen coefficient point contains).mp basic_member
  obtain ⟨smaller, inclusion, smaller_contains, unit⟩ :=
    scheme.toRingedSpace.isUnit_res_of_isUnit_germ open_set coefficient point contains germ_unit
  let smaller_frame := frame.restrict inclusion.le
  have coord_equal : smaller_frame.coord le_rfl (sheaf.res le_top section_value) =
      scheme.presheaf.map inclusion.op coefficient := by
    apply (smaller_frame _ le_rfl).injective
    dsimp only
    rw [smaller_frame.coord_smul_frame, Scheme.Modules.res_self]
    have equal := congrArg (sheaf.res inclusion.le)
      (frame.coord_smul_frame le_rfl (sheaf.res le_top section_value))
    rw [Scheme.Modules.res_self] at equal
    change sheaf.presheaf.map inclusion.op
      (frame.coord le_rfl (sheaf.res le_top section_value) • frame_section) = _ at equal
    rw [Scheme.Modules.map_smul] at equal
    change _ = sheaf.res inclusion.le (sheaf.res le_top section_value) at equal
    rw [Scheme.Modules.res_res] at equal
    exact equal.symm
  refine ⟨smaller, smaller_contains, moduleFrame_of_isUnit_coordinate smaller_frame ?_⟩
  rw [coord_equal]
  exact unit

theorem moduleGlobalSectionHom_over_isIso_of_frame (sheaf : scheme.Modules)
    (section_value : Γ(sheaf, ⊤)) (open_set : scheme.Opens)
    (frame : Scheme.Modules.IsFrame sheaf open_set (sheaf.res le_top section_value)) :
    IsIso ((ampleGlobalSectionHom sheaf section_value).over open_set) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget _)).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro local_open
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun scalar : Γ(scheme, local_open.unop.left) =>
    scalar • sheaf.res (show local_open.unop.left ≤ ⊤ from le_top) section_value)
  have bijective := frame local_open.unop.left local_open.unop.hom.le
  rw [Scheme.Modules.res_res] at bijective
  exact bijective

def monoidalSheafPower (sheaf : scheme.Modules) : ℕ → scheme.Modules
  | 0 => SheafOfModules.unit scheme.ringCatSheaf
  | exponent + 1 => monoidalSheafPower sheaf exponent ⊗ sheaf

def monoidalSheafPowerSectionHom (sheaf : scheme.Modules)
    (section_map : SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf) :
    (exponent : ℕ) → SheafOfModules.unit scheme.ringCatSheaf ⟶ monoidalSheafPower sheaf exponent
  | 0 => 𝟙 _
  | exponent + 1 => (λ_ (SheafOfModules.unit scheme.ringCatSheaf)).inv ≫
      (monoidalSheafPowerSectionHom sheaf section_map exponent ⊗ₘ section_map)

def monoidalSheafPowerTensorPowIso (sheaf : scheme.Modules) : (exponent : ℕ) →
    monoidalSheafPower sheaf exponent ≅ Scheme.Modules.tensorPow sheaf exponent
  | 0 => Iso.refl _
  | exponent + 1 => Scheme.Modules.isoOfSheafIso scheme
      (SheafOfModules.tensorUnderlyingIso (R := scheme.sheaf) _ _ ≪≫
        (TauCeti.SheafOfModules.tensorProductIso scheme.sheaf _ _).symm ≪≫
          TauCeti.SheafOfModules.tensorProductCongrLeft scheme.sheaf
            (Scheme.Modules.tensorPowerUnderlyingSheafIso
              (monoidalSheafPowerTensorPowIso sheaf exponent)))

theorem monoidalSheafPowerSectionHom_over_isIso (sheaf : scheme.Modules)
    (section_map : SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf)
    (open_set : scheme.Opens) (local_iso : IsIso (section_map.over open_set)) (exponent : ℕ) :
    IsIso ((monoidalSheafPowerSectionHom sheaf section_map exponent).over open_set) := by
  let := TauCeti.SheafOfModules.monoidalCategory (scheme.sheaf.over open_set)
  let := SheafOfModules.overFunctorMonoidal scheme.sheaf open_set
  induction exponent with
  | zero =>
      change IsIso ((SheafOfModules.overFunctor
        (TauCeti.SheafOfModules.ringCatSheaf scheme.sheaf) open_set).map (𝟙 _))
      infer_instance
  | succ exponent induction_hypothesis =>
      let := local_iso
      let := induction_hypothesis
      change IsIso ((SheafOfModules.overFunctor
        (TauCeti.SheafOfModules.ringCatSheaf scheme.sheaf) open_set).map
        ((λ_ (SheafOfModules.unit scheme.ringCatSheaf)).inv ≫
          (monoidalSheafPowerSectionHom sheaf section_map exponent ⊗ₘ section_map)))
      rw [Functor.map_comp]
      have tensor_iso : IsIso ((SheafOfModules.overFunctor
          (TauCeti.SheafOfModules.ringCatSheaf scheme.sheaf) open_set).map
          (monoidalSheafPowerSectionHom sheaf section_map exponent ⊗ₘ section_map)) := by
        have formula := @Functor.Monoidal.map_tensor
          (SheafOfModules.{schemeUniverse} (TauCeti.SheafOfModules.ringCatSheaf scheme.sheaf)) _
          (TauCeti.SheafOfModules.monoidalCategory scheme.sheaf)
          (SheafOfModules.{schemeUniverse} ((TauCeti.SheafOfModules.ringCatSheaf scheme.sheaf).over open_set)) _
          (TauCeti.SheafOfModules.monoidalCategory (scheme.sheaf.over open_set))
          (SheafOfModules.overFunctor (TauCeti.SheafOfModules.ringCatSheaf scheme.sheaf) open_set)
          (SheafOfModules.overFunctorMonoidal scheme.sheaf open_set)
          _ _ _ _ (monoidalSheafPowerSectionHom sheaf section_map exponent) section_map
        rw [formula]
        infer_instance
      let := tensor_iso
      infer_instance

def actualTensorPowIterateIso (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (first second : ℕ) :
    Scheme.Modules.tensorPow (Scheme.Modules.tensorPow bundle.obj first) second ≅
      Scheme.Modules.tensorPow bundle.obj (first * second) :=
  Scheme.Modules.tensorPowMapIso
    (MiyaokaMori.invertibleSheafTensorPowerIso bundle first).symm second ≪≫
      invertibleSheafTensorPowerIterateIso bundle first second

theorem exists_finite_positivePower_frameCover_of_isAmple
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (ample : AlgebraicGeometry.IsAmple bundle.obj) :
    ∃ (exponent : ℕ) (_ : 0 < exponent) (Index : Type schemeUniverse) (_ : Fintype Index)
      (charts : Index → scheme.Opens)
      (section_maps : Index → (SheafOfModules.unit scheme.ringCatSheaf ⟶
        Scheme.Modules.tensorPow bundle.obj exponent)),
      IsOpenCover charts ∧ ∀ index, IsIso ((section_maps index).over (charts index)) := by
  let : CompactSpace scheme := ample.1
  choose degree positive section_value contains affine using ample.2
  have frames : ∀ point : scheme, ∃ chart : scheme.Opens, point ∈ chart ∧
      Scheme.Modules.IsFrame (Scheme.Modules.tensorPow bundle.obj (degree point)) chart
        ((Scheme.Modules.tensorPow bundle.obj (degree point)).res le_top (section_value point)) :=
    fun point => exists_frame_neighborhood_of_nonvanishing _ _ point (contains point)
  choose charts chart_contains chart_frame using frames
  obtain ⟨selected, covers⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
    (fun point : scheme => (charts point : Set scheme))
    (fun point => (charts point).isOpen)
    (fun point _ => Set.mem_iUnion.mpr ⟨point, chart_contains point⟩)
  classical
  let exponent := ∏ point ∈ selected, degree point
  have exponent_positive : 0 < exponent := Finset.prod_pos fun point _ => positive point
  have divides : ∀ point ∈ selected, degree point ∣ exponent :=
    fun point member => Finset.dvd_prod_of_mem degree member
  let repeats : scheme → ℕ := fun point => exponent / degree point
  have common_degree : ∀ point ∈ selected, degree point * repeats point = exponent :=
    fun point member => Nat.mul_div_cancel' (divides point member)
  let comparison : ∀ point ∈ selected,
      monoidalSheafPower (Scheme.Modules.tensorPow bundle.obj (degree point)) (repeats point) ≅
        Scheme.Modules.tensorPow bundle.obj exponent := fun point member =>
    monoidalSheafPowerTensorPowIso _ _ ≪≫ actualTensorPowIterateIso bundle _ _ ≪≫
      eqToIso (by rw [common_degree point member])
  let section_maps : ∀ point ∈ selected,
      SheafOfModules.unit scheme.ringCatSheaf ⟶ Scheme.Modules.tensorPow bundle.obj exponent :=
    fun point member => monoidalSheafPowerSectionHom _
      (ampleGlobalSectionHom _ (section_value point)) (repeats point) ≫
        (comparison point member).hom
  refine ⟨exponent, exponent_positive, {point // point ∈ selected}, inferInstance,
    fun point => charts point.val, fun point => section_maps point.val point.property, ?_, ?_⟩
  · apply IsOpenCover.mk
    apply top_unique
    intro point _
    obtain ⟨chosen, member, contains⟩ := Set.mem_iUnion₂.mp (covers (Set.mem_univ point))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨chosen, member⟩, contains⟩
  · intro point
    have original_iso := moduleGlobalSectionHom_over_isIso_of_frame _ _ _ (chart_frame point.val)
    have powered_iso := monoidalSheafPowerSectionHom_over_isIso _ _ _ original_iso (repeats point.val)
    let := powered_iso
    change IsIso (((SheafOfModules.overFunctor scheme.ringCatSheaf (charts point.val)).map
      (monoidalSheafPowerSectionHom _ (ampleGlobalSectionHom _ (section_value point.val))
        (repeats point.val) ≫ (comparison point.val point.property).hom)))
    rw [Functor.map_comp]
    infer_instance

def finiteFrameCoverSectionFamily {sheaf : scheme.Modules} {Index : Type schemeUniverse}
    (section_maps : Index → (SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf)) :
    Index → sheaf.sections := fun index => sheaf.unitHomEquiv (section_maps index)

def finiteFrameCoverEvaluation {sheaf : scheme.Modules} {Index : Type schemeUniverse}
    (section_maps : Index → (SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf)) :
    SheafOfModules.free (R := scheme.ringCatSheaf) Index ⟶ sheaf :=
  sheaf.freeHomEquiv.symm (finiteFrameCoverSectionFamily section_maps)

theorem finiteFrameCoverEvaluation_coordinate {sheaf : scheme.Modules} {Index : Type schemeUniverse}
    (section_maps : Index → (SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf)) (index : Index) :
    SheafOfModules.ιFree index ≫ finiteFrameCoverEvaluation section_maps = section_maps index := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [finiteFrameCoverEvaluation, Equiv.apply_symm_apply, finiteFrameCoverSectionFamily,
    Equiv.symm_apply_apply]

theorem ampleModuleHom_ext_of_cover {source target : scheme.Modules}
    {Index : Type schemeUniverse} (charts : Index → scheme.Opens) (covers : IsOpenCover charts)
    (first second : source ⟶ target)
    (local_equal : ∀ index, first.over (charts index) = second.over (charts index)) :
    first = second := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext domain
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro section_value
  have intersection_cover : domain.unop ≤ ⨆ index, domain.unop ⊓ charts index := by
    rw [← inf_iSup_eq, covers.iSup_eq_top, inf_top_eq]
  apply (show TopCat.Sheaf AddCommGrpCat.{schemeUniverse} scheme from
    (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => domain.unop ⊓ charts index) domain.unop (fun index => homOfLE inf_le_left)
    intersection_cover
  intro index
  have local_value := congrArg (fun morphism => morphism.val.app
      (op (Over.mk (homOfLE (inf_le_right : domain.unop ⊓ charts index ≤ charts index))))
      (source.presheaf.map (homOfLE (inf_le_left : domain.unop ⊓ charts index ≤ domain.unop)).op
        section_value)) (local_equal index)
  have first_natural := ConcreteCategory.congr_hom
    (first.val.naturality
      (homOfLE (inf_le_left : domain.unop ⊓ charts index ≤ domain.unop)).op) section_value
  have second_natural := ConcreteCategory.congr_hom
    (second.val.naturality
      (homOfLE (inf_le_left : domain.unop ⊓ charts index ≤ domain.unop)).op) section_value
  simp only [ConcreteCategory.comp_apply] at first_natural second_natural
  exact first_natural.symm.trans (local_value.trans second_natural)

theorem ampleModuleEpi_of_cover {source target : scheme.Modules}
    {Index : Type schemeUniverse} (charts : Index → scheme.Opens) (covers : IsOpenCover charts)
    (morphism : source ⟶ target)
    (local_epi : ∀ index, Epi (morphism.over (charts index))) : Epi morphism where
  left_cancellation := by
    intro destination first second equal
    apply ampleModuleHom_ext_of_cover charts covers
    intro index
    let := local_epi index
    apply (cancel_epi (morphism.over (charts index))).mp
    exact congrArg (fun local_morphism => local_morphism.over (charts index)) equal

theorem finiteFrameCoverEvaluation_epi {sheaf : scheme.Modules} {Index : Type schemeUniverse}
    (charts : Index → scheme.Opens) (covers : IsOpenCover charts)
    (section_maps : Index → (SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf))
    (local_iso : ∀ index, IsIso ((section_maps index).over (charts index))) :
    Epi (finiteFrameCoverEvaluation section_maps) := by
  apply ampleModuleEpi_of_cover charts covers
  intro index
  let := local_iso index
  have factorization := congrArg
    (fun morphism => morphism.over (charts index))
    (finiteFrameCoverEvaluation_coordinate section_maps index)
  change (SheafOfModules.ιFree index).over (charts index) ≫
    (finiteFrameCoverEvaluation section_maps).over (charts index) =
      (section_maps index).over (charts index) at factorization
  exact epi_of_epi_fac factorization

def finiteFrameCoverGeneratingSections {sheaf : scheme.Modules} {Index : Type schemeUniverse}
    (charts : Index → scheme.Opens) (covers : IsOpenCover charts)
    (section_maps : Index → (SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf))
    (local_iso : ∀ index, IsIso ((section_maps index).over (charts index))) :
    sheaf.GeneratingSections where
  I := Index
  s := finiteFrameCoverSectionFamily section_maps
  epi := finiteFrameCoverEvaluation_epi charts covers section_maps local_iso

instance finiteFrameCoverGeneratingSections_isFiniteType {sheaf : scheme.Modules}
    {Index : Type schemeUniverse} [Finite Index]
    (charts : Index → scheme.Opens) (covers : IsOpenCover charts)
    (section_maps : Index → (SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf))
    (local_iso : ∀ index, IsIso ((section_maps index).over (charts index))) :
    (finiteFrameCoverGeneratingSections charts covers section_maps local_iso).IsFiniteType where
  finite := by
    change Finite Index
    infer_instance

theorem exists_finite_generatingSections_positivePower_of_isAmple
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (ample : AlgebraicGeometry.IsAmple bundle.obj) :
    ∃ (exponent : ℕ) (_ : 0 < exponent)
      (generators : (Scheme.Modules.tensorPow bundle.obj exponent).GeneratingSections),
      generators.IsFiniteType := by
  obtain ⟨exponent, positive, Index, fintype, charts, section_maps, covers, local_iso⟩ :=
    exists_finite_positivePower_frameCover_of_isAmple bundle ample
  let := fintype
  exact ⟨exponent, positive, finiteFrameCoverGeneratingSections charts covers section_maps local_iso,
    inferInstance⟩

theorem invertibleSheafSemiample_of_isAmple
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (ample : AlgebraicGeometry.IsAmple bundle.obj) : InvertibleSheafSemiample bundle := by
  obtain ⟨exponent, positive, generators, finite⟩ :=
    exists_finite_generatingSections_positivePower_of_isAmple bundle ample
  let comparison := MiyaokaMori.invertibleSheafTensorPowerIso bundle exponent
  exact ⟨exponent, positive, ⟨generators.ofEpi comparison.inv⟩⟩

end BondalThomsen
