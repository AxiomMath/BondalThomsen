module

public import BondalThomsen.Toric.Canonical.Exterior
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.RingTheory.Kaehler.TensorProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace BondalThomsen.CanonicalChart

universe schemeUniverse

noncomputable def differentialAlgebraCoordinates {Base Source Target : CommRingCat.{schemeUniverse}}
    (source : Base ⟶ Source) (target : Base ⟶ Target) (coordinates : Source ≅ Target)
    (compatible : source ≫ coordinates.hom = target) :
    letI := source.hom.toAlgebra
    letI := target.hom.toAlgebra
    Source ≃ₐ[Base] Target := by
  letI := source.hom.toAlgebra
  letI := target.hom.toAlgebra
  exact
    { coordinates.commRingCatIsoToRingEquiv with
      commutes' := fun scalar => ConcreteCategory.congr_hom compatible scalar }

noncomputable def differentialCoefficientIso {Base Source Target : CommRingCat.{schemeUniverse}}
    (source : Base ⟶ Source) (target : Base ⟶ Target) (coordinates : Source ≅ Target)
    (compatible : source ≫ coordinates.hom = target) :
    CommRingCat.KaehlerDifferential source ≅
      (ModuleCat.restrictScalars coordinates.hom.hom).obj
        (CommRingCat.KaehlerDifferential target) := by
  letI := source.hom.toAlgebra
  letI := target.hom.toAlgebra
  let algebraCoordinates := differentialAlgebraCoordinates source target coordinates compatible
  letI := RingHomInvPair.of_ringEquiv algebraCoordinates.toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm algebraCoordinates.toRingEquiv
  let transport := DifferentialCoordinates.equiv algebraCoordinates
  let linear : KaehlerDifferential Base Source ≃ₗ[Source]
      (ModuleCat.restrictScalars coordinates.hom.hom).obj
        (CommRingCat.KaehlerDifferential target) :=
    { transport.toAddEquiv with
      map_smul' := fun scalar vector => transport.map_smulₛₗ scalar vector }
  exact linear.toModuleIso

theorem differentialCoefficientIso_d {Base Source Target : CommRingCat.{schemeUniverse}}
    (source : Base ⟶ Source) (target : Base ⟶ Target) (coordinates : Source ≅ Target)
    (compatible : source ≫ coordinates.hom = target) (regularFunction : Source) :
    (differentialCoefficientIso source target coordinates compatible).hom
        (CommRingCat.KaehlerDifferential.d regularFunction) =
      CommRingCat.KaehlerDifferential.d (coordinates.hom regularFunction) := by
  let := source.hom.toAlgebra
  let := target.hom.toAlgebra
  let algebraCoordinates := differentialAlgebraCoordinates source target coordinates compatible
  change DifferentialCoordinates.map algebraCoordinates.toAlgHom
      (KaehlerDifferential.D Base Source regularFunction) =
    KaehlerDifferential.D Base Target (coordinates.hom regularFunction)
  exact DifferentialCoordinates.map_D algebraCoordinates.toAlgHom regularFunction

variable {Chart SchemeModel : Scheme.{schemeUniverse}}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]

noncomputable def restrictionCoefficientMap :
    Chart.presheaf ⟶ inclusion.opensFunctor.op ⋙ SchemeModel.presheaf where
  app domain := (inclusion.appIso domain.unop).inv
  naturality := fun _ _ restriction => inclusion.appIso_inv_naturality restriction

noncomputable def presheafRestriction :
    SchemeModel.PresheafOfModules ⥤ Chart.PresheafOfModules :=
  PresheafOfModules.pushforward
    (Functor.whiskerRight (restrictionCoefficientMap inclusion) (forget₂ CommRingCat RingCat))

noncomputable def restrictionSheafificationComparison
    (presheaf : SchemeModel.PresheafOfModules) :
    (PresheafOfModules.sheafification (𝟙 Chart.ringCatSheaf.obj)).obj
        ((presheafRestriction inclusion).obj presheaf) ⟶
      (Scheme.Modules.restrictFunctor inclusion).obj
        ((PresheafOfModules.sheafification (𝟙 SchemeModel.ringCatSheaf.obj)).obj presheaf) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 Chart.ringCatSheaf.obj)).symm
    ((presheafRestriction inclusion).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app presheaf))

theorem restrictionSheafificationComparison_toSheaf
    (presheaf : SchemeModel.PresheafOfModules) :
    (SheafOfModules.toSheaf Chart.ringCatSheaf).map
        (restrictionSheafificationComparison inclusion presheaf) =
      ((inclusion.opensFunctor.pushforwardContinuousSheafificationCompatibility AddCommGrpCat
        (Opens.grothendieckTopology Chart) (Opens.grothendieckTopology SchemeModel)).app
          presheaf.presheaf).hom := by
  rw [restrictionSheafificationComparison,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  change ((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Chart)
      AddCommGrpCat).homEquiv (inclusion.opensFunctor.op ⋙ presheaf.presheaf)
        ((inclusion.opensFunctor.sheafPushforwardContinuous AddCommGrpCat
          (Opens.grothendieckTopology Chart) (Opens.grothendieckTopology SchemeModel)).obj
            ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology SchemeModel)
              AddCommGrpCat).obj presheaf.presheaf))).symm
        (Functor.whiskerLeft inclusion.opensFunctor.op
          (CategoryTheory.toSheafify (Opens.grothendieckTopology SchemeModel) presheaf.presheaf)) = _
  apply ((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Chart)
    AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (Functor.toSheafify_pullbackSheafificationCompatibility inclusion.opensFunctor
    AddCommGrpCat (Opens.grothendieckTopology Chart) (Opens.grothendieckTopology SchemeModel)
      presheaf.presheaf).symm

instance restrictionSheafificationComparison_isIso
    (presheaf : SchemeModel.PresheafOfModules) :
    IsIso (restrictionSheafificationComparison inclusion presheaf) := by
  have : IsIso ((SheafOfModules.toSheaf Chart.ringCatSheaf).map
      (restrictionSheafificationComparison inclusion presheaf)) := by
    rw [restrictionSheafificationComparison_toSheaf]
    infer_instance
  exact isIso_of_reflects_iso (restrictionSheafificationComparison inclusion presheaf)
    (SheafOfModules.toSheaf Chart.ringCatSheaf)

noncomputable def restrictionSheafificationIso
    (presheaf : SchemeModel.PresheafOfModules) :
    (Scheme.Modules.restrictFunctor inclusion).obj
        ((PresheafOfModules.sheafification (𝟙 SchemeModel.ringCatSheaf.obj)).obj presheaf) ≅
      (PresheafOfModules.sheafification (𝟙 Chart.ringCatSheaf.obj)).obj
        ((presheafRestriction inclusion).obj presheaf) :=
  (asIso (restrictionSheafificationComparison inclusion presheaf)).symm

theorem cotangentCoefficientMap_chart {Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) (domain : Chart.Opens) :
    (cotangentCoefficientMap structureMap).app (op (inclusion.opensFunctor.obj domain)) ≫
        (inclusion.appIso domain).hom =
      (cotangentCoefficientMap (inclusion ≫ structureMap)).app (op domain) := by
  change structureMap.appLE ⊤ (inclusion.opensFunctor.obj domain) (by simp) ≫
    (inclusion.appIso domain).hom = (inclusion ≫ structureMap).appLE ⊤ domain (by simp)
  rw [inclusion.appIso_hom', Scheme.Hom.appLE_comp_appLE]

noncomputable def cotangentChartSectionIso {Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) (domain : Chart.Opensᵒᵖ) :
    (cotangentPresheaf (inclusion ≫ structureMap)).obj domain ≅
      ((presheafRestriction inclusion).obj (cotangentPresheaf structureMap)).obj domain :=
  differentialCoefficientIso
    ((cotangentCoefficientMap (inclusion ≫ structureMap)).app domain)
    ((cotangentCoefficientMap structureMap).app (inclusion.opensFunctor.op.obj domain))
    (inclusion.appIso domain.unop).symm (by
      rw [← cotangentCoefficientMap_chart inclusion structureMap domain.unop]
      simp)

theorem cotangentChartSectionIso_d {Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) (domain : Chart.Opensᵒᵖ)
    (regularFunction : Chart.presheaf.obj domain) :
    (cotangentChartSectionIso inclusion structureMap domain).hom
        (CommRingCat.KaehlerDifferential.d regularFunction) =
      CommRingCat.KaehlerDifferential.d ((inclusion.appIso domain.unop).inv regularFunction) :=
  differentialCoefficientIso_d _ _ _ _ regularFunction

noncomputable def cotangentPresheafRestrictionIso {Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) :
    cotangentPresheaf (inclusion ≫ structureMap) ≅
      (presheafRestriction inclusion).obj (cotangentPresheaf structureMap) := by
  refine PresheafOfModules.isoMk (cotangentChartSectionIso inclusion structureMap) ?_
  intro domain smaller restriction
  apply CommRingCat.KaehlerDifferential.ext
  intro regularFunction
  change (cotangentChartSectionIso inclusion structureMap smaller).hom
      ((cotangentPresheaf (inclusion ≫ structureMap)).map restriction
        (CommRingCat.KaehlerDifferential.d regularFunction)) =
    (cotangentPresheaf structureMap).map (inclusion.opensFunctor.op.map restriction)
      ((cotangentChartSectionIso inclusion structureMap domain).hom
        (CommRingCat.KaehlerDifferential.d regularFunction))
  have local_d :=
    PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
      (cotangentCoefficientMap (inclusion ≫ structureMap)) restriction regularFunction
  have ambient_d :=
    PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
      (cotangentCoefficientMap structureMap) (inclusion.opensFunctor.op.map restriction)
        ((inclusion.appIso domain.unop).inv regularFunction)
  calc
    _ = (cotangentChartSectionIso inclusion structureMap smaller).hom
        (CommRingCat.KaehlerDifferential.d (Chart.presheaf.map restriction regularFunction)) :=
      congrArg (fun differential =>
        (cotangentChartSectionIso inclusion structureMap smaller).hom differential) local_d
    _ = CommRingCat.KaehlerDifferential.d
        ((inclusion.appIso smaller.unop).inv (Chart.presheaf.map restriction regularFunction)) :=
      cotangentChartSectionIso_d inclusion structureMap smaller _
    _ = CommRingCat.KaehlerDifferential.d
        (SchemeModel.presheaf.map (inclusion.opensFunctor.op.map restriction)
          ((inclusion.appIso domain.unop).inv regularFunction)) :=
      congrArg CommRingCat.KaehlerDifferential.d
        (ConcreteCategory.congr_hom (inclusion.appIso_inv_naturality restriction) regularFunction)
    _ = (cotangentPresheaf structureMap).map (inclusion.opensFunctor.op.map restriction)
        (CommRingCat.KaehlerDifferential.d ((inclusion.appIso domain.unop).inv regularFunction)) :=
      ambient_d.symm
    _ = _ := congrArg (fun differential => (cotangentPresheaf structureMap).map
      (inclusion.opensFunctor.op.map restriction) differential)
        (cotangentChartSectionIso_d inclusion structureMap domain regularFunction).symm

noncomputable def cotangentSheafRestrictionIso {Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) :
    (cotangentSheaf structureMap).restrict inclusion ≅
      cotangentSheaf (inclusion ≫ structureMap) :=
  restrictionSheafificationIso inclusion (cotangentPresheaf structureMap) ≪≫
    (PresheafOfModules.sheafification (𝟙 Chart.ringCatSheaf.obj)).mapIso
      (cotangentPresheafRestrictionIso inclusion structureMap).symm

end BondalThomsen.CanonicalChart

namespace BondalThomsen.CanonicalChart

universe coefficientUniverse moduleUniverse

noncomputable def exteriorModuleCoefficientIso {Source Target : CommRingCat.{coefficientUniverse}}
    (coordinates : Source ≅ Target) (modules : ModuleCat.{moduleUniverse} Target) (degree : ℕ) :
    ModuleCat.of Source
        (⋀[Source]^degree ((ModuleCat.restrictScalars coordinates.hom.hom).obj modules)) ≅
      (ModuleCat.restrictScalars coordinates.hom.hom).obj
        (ModuleCat.of Target (⋀[Target]^degree modules)) := by
  let forwardModule : (ModuleCat.restrictScalars coordinates.hom.hom).obj modules
      →ₛₗ[coordinates.hom.hom] modules :=
    { toFun := fun vector => vector
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let backwardModule : modules →ₛₗ[coordinates.inv.hom]
      (ModuleCat.restrictScalars coordinates.hom.hom).obj modules :=
    { toFun := fun vector => vector
      map_add' := fun _ _ => rfl
      map_smul' := fun scalar vector => by
        change scalar • vector = coordinates.hom (coordinates.inv scalar) • vector
        rw [Iso.inv_hom_id_apply] }
  let forward := SemilinearExterior.map degree coordinates.hom.hom forwardModule
  let backward := SemilinearExterior.map degree coordinates.inv.hom backwardModule
  refine
    { hom := ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars coordinates.hom.hom).obj
          (ModuleCat.of Target (⋀[Target]^degree modules)))
        { toFun := forward
          map_add' := forward.map_add
          map_smul' := fun scalar vector => forward.map_smulₛₗ scalar vector }
      inv := ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars coordinates.hom.hom).obj
          (ModuleCat.of Target (⋀[Target]^degree modules)))
        (Y := ModuleCat.of Source
          (⋀[Source]^degree ((ModuleCat.restrictScalars coordinates.hom.hom).obj modules)))
        { toFun := backward
          map_add' := backward.map_add
          map_smul' := fun scalar vector => by
            change backward (coordinates.hom scalar • vector) = scalar • backward vector
            rw [backward.map_smulₛₗ]
            congr 1
            exact Iso.hom_inv_id_apply coordinates scalar }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply ModuleCat.hom_ext
    apply exteriorLinear_ext
    intro vectors
    change backward (forward (exteriorPower.ιMulti Source degree vectors)) = _
    rw [SemilinearExterior.map_wedge, SemilinearExterior.map_wedge]
    rfl
  · apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro vector
    change forward (backward vector) = vector
    have membership : vector ∈ Submodule.span Target
        (Set.range (exteriorPower.ιMulti Target degree)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction membership using Submodule.span_induction with
    | mem vector membership =>
        obtain ⟨vectors, rfl⟩ := membership
        rw [SemilinearExterior.map_wedge, SemilinearExterior.map_wedge]
        rfl
    | zero => simp only [map_zero]
    | add first second first_mem second_mem first_eq second_eq =>
        simp only [map_add, first_eq, second_eq]
    | smul scalar vector vector_mem vector_eq =>
        simp only [map_smulₛₗ, vector_eq]
        rw [Iso.inv_hom_id_apply]

theorem exteriorModuleCoefficientIso_wedge {Source Target : CommRingCat.{coefficientUniverse}}
    (coordinates : Source ≅ Target) (modules : ModuleCat.{moduleUniverse} Target) (degree : ℕ)
    (vectors : Fin degree → (ModuleCat.restrictScalars coordinates.hom.hom).obj modules) :
    (exteriorModuleCoefficientIso coordinates modules degree).hom
        (exteriorPower.ιMulti Source degree vectors) =
      exteriorPower.ιMulti (M := modules) Target degree (fun index => (vectors index : modules)) := by
  change SemilinearExterior.map degree coordinates.hom.hom _
    (exteriorPower.ιMulti Source degree vectors) = _
  exact SemilinearExterior.map_wedge _ _ _ _

end BondalThomsen.CanonicalChart
