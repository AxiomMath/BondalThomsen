module

public import BondalThomsen.Toric.Canonical.RaySumGluing
public import BondalThomsen.Toric.Canonical.Invertible
public import BondalThomsen.Toric.Canonical.BaseIso
public import BondalThomsen.Toric.Canonical.FanChartRestriction
public import BondalThomsen.Toric.Frobenius.MultiplicationFiniteLocallyFree
public import BondalThomsen.Toric.Scheme.Integral
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CanonicalRaySumSheaf

noncomputable def cotangentUnit {SchemeModel Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) :
    cotangentPresheaf structureMap ⟶ (cotangentSheaf structureMap).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app (cotangentPresheaf structureMap)

noncomputable def exteriorUnit {SchemeModel : Scheme}
    (modules : SchemeModel.Modules) (degree : ℕ) :
    exteriorPresheaf modules.val degree ⟶ (exteriorSheaf modules degree).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app (exteriorPresheaf modules.val degree)

noncomputable def differentialSection {SchemeModel Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) (domain : SchemeModel.Opens)
    (regularFunction : Γ(SchemeModel, domain)) :
    (cotangentSheaf structureMap).val.obj (op domain) :=
  (cotangentUnit structureMap).app (op domain)
    (CommRingCat.KaehlerDifferential.d regularFunction)

theorem differentialSection_restriction {SchemeModel Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) {domain smaller : SchemeModel.Opens}
    (restriction : smaller ⟶ domain) (regularFunction : Γ(SchemeModel, domain)) :
    (cotangentSheaf structureMap).val.map restriction.op
        (differentialSection structureMap domain regularFunction) =
      differentialSection structureMap smaller
        (SchemeModel.presheaf.map restriction.op regularFunction) := by
  unfold differentialSection
  rw [← PresheafOfModules.naturality_apply, cotangentPresheaf_map_d]

noncomputable def differentialTopSection {SchemeModel Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ) (domain : SchemeModel.Opens)
    (coordinates : Fin degree → Γ(SchemeModel, domain)) :
    (canonicalExteriorSheaf structureMap degree).val.obj (op domain) :=
  (exteriorUnit (cotangentSheaf structureMap) degree).app (op domain)
    (exteriorPower.ιMulti Γ(SchemeModel, domain) degree
      (fun index => differentialSection structureMap domain (coordinates index)))

theorem differentialTopSection_restriction {SchemeModel Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ)
    {domain smaller : SchemeModel.Opens} (restriction : smaller ⟶ domain)
    (coordinates : Fin degree → Γ(SchemeModel, domain)) :
    (canonicalExteriorSheaf structureMap degree).val.map restriction.op
        (differentialTopSection structureMap degree domain coordinates) =
      differentialTopSection structureMap degree smaller
        (fun index => SchemeModel.presheaf.map restriction.op (coordinates index)) := by
  unfold differentialTopSection
  change (exteriorSheaf (cotangentSheaf structureMap) degree).val.map restriction.op
      ((exteriorUnit (cotangentSheaf structureMap) degree).app (op domain)
        (exteriorPower.ιMulti Γ(SchemeModel, domain) degree
          (fun index => differentialSection structureMap domain (coordinates index)))) = _
  have naturality := PresheafOfModules.naturality_apply
    (exteriorUnit (cotangentSheaf structureMap) degree) restriction.op
    (exteriorPower.ιMulti Γ(SchemeModel, domain) degree
      (fun index => differentialSection structureMap domain (coordinates index)))
  refine naturality.symm.trans ?_
  apply congrArg ((exteriorUnit (cotangentSheaf structureMap) degree).app (op smaller))
  exact (exteriorPresheaf_map_wedge
    (Coefficients := SchemeModel.presheaf) (cotangentSheaf structureMap).val degree restriction.op
    (fun index => differentialSection structureMap domain (coordinates index))).trans
      (congrArg (exteriorPower.ιMulti Γ(SchemeModel, smaller) degree)
        (funext (fun index => differentialSection_restriction structureMap restriction
          (coordinates index))))

theorem exteriorSheafIso_unit_wedge {SchemeModel : Scheme}
    {source target : SchemeModel.Modules} (comparison : source ≅ target)
    (degree : ℕ) (domain : SchemeModel.Opens)
    (vectors : Fin degree → source.val.obj (op domain)) :
    (CanonicalTopExterior.exteriorSheafIso comparison degree).hom.val.app (op domain)
        ((exteriorUnit source degree).app (op domain)
          (exteriorPower.ιMulti Γ(SchemeModel, domain) degree vectors)) =
      (exteriorUnit target degree).app (op domain)
        (exteriorPower.ιMulti Γ(SchemeModel, domain) degree
          (fun index => comparison.hom.val.app (op domain) (vectors index))) := by
  have naturality :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 SchemeModel.ringCatSheaf.obj)).unit.naturality
        (CanonicalTopExterior.exteriorPresheafHom comparison.hom.val degree)
  change CanonicalTopExterior.exteriorPresheafHom comparison.hom.val degree ≫
      exteriorUnit target degree = exteriorUnit source degree ≫
        (CanonicalTopExterior.exteriorSheafIso comparison degree).hom.val at naturality
  have value := congrArg (fun morphism => morphism.app (op domain)
    (exteriorPower.ιMulti Γ(SchemeModel, domain) degree vectors)) naturality
  have exteriorMap :
      (CanonicalTopExterior.exteriorPresheafHom comparison.hom.val degree).app (op domain)
          (exteriorPower.ιMulti Γ(SchemeModel, domain) degree vectors) =
        exteriorPower.ιMulti Γ(SchemeModel, domain) degree
          (fun index => comparison.hom.val.app (op domain) (vectors index)) := by
    exact exteriorPower.map_apply_ιMulti
      (R := SchemeModel.presheaf.obj (op domain))
      (comparison.hom.val.app (op domain)).hom vectors
  exact value.symm.trans (congrArg ((exteriorUnit target degree).app (op domain)) exteriorMap)

theorem sheafificationMap_unit_app {SchemeModel : Scheme}
    {source target : SchemeModel.PresheafOfModules} (morphism : source ⟶ target)
    (domain : SchemeModel.Opens) (vector : source.obj (op domain)) :
    ((PresheafOfModules.sheafification (𝟙 SchemeModel.ringCatSheaf.obj)).map morphism).val.app
        (op domain)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app
          source).app (op domain) vector) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app
        target).app (op domain) (morphism.app (op domain) vector) := by
  have naturality := (PresheafOfModules.sheafificationAdjunction
    (𝟙 SchemeModel.ringCatSheaf.obj)).unit.naturality morphism
  change morphism ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app target =
    (PresheafOfModules.sheafificationAdjunction (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app source ≫
      ((PresheafOfModules.sheafification (𝟙 SchemeModel.ringCatSheaf.obj)).map morphism).val
    at naturality
  exact (congrArg (fun comparison => comparison.app (op domain) vector) naturality).symm

theorem restrictionSheafificationComparison_unit {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (presheaf : SchemeModel.PresheafOfModules) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 Chart.ringCatSheaf.obj)).unit.app
        ((CanonicalChart.presheafRestriction inclusion).obj presheaf) ≫
        (CanonicalChart.restrictionSheafificationComparison inclusion presheaf).val =
      (CanonicalChart.presheafRestriction inclusion).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app presheaf) := by
  apply (PresheafOfModules.toPresheaf Chart.ringCatSheaf.obj).map_injective
  change CategoryTheory.toSheafify (Opens.grothendieckTopology Chart)
      (((CanonicalChart.presheafRestriction inclusion).obj presheaf).presheaf) ≫
      (PresheafOfModules.toPresheaf Chart.ringCatSheaf.obj).map
        (CanonicalChart.restrictionSheafificationComparison inclusion presheaf).val = _
  rw [← PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  let restricted := (CanonicalChart.presheafRestriction inclusion).obj presheaf
  let sheaf := (Scheme.Modules.restrictFunctor inclusion).obj
    ((PresheafOfModules.sheafification (𝟙 SchemeModel.ringCatSheaf.obj)).obj presheaf)
  let restrictedUnit : restricted ⟶ sheaf.val :=
    (CanonicalChart.presheafRestriction inclusion).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app presheaf)
  exact congrArg ((PresheafOfModules.toPresheaf Chart.ringCatSheaf.obj).map)
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 Chart.ringCatSheaf.obj)
      (P := restricted) (F := sheaf)).apply_symm_apply restrictedUnit)

theorem cotangentSheafRestrictionIso_inv_differentialSection {Chart SchemeModel Base : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Base) (domain : Chart.Opens)
    (regularFunction : Γ(Chart, domain)) :
    (CanonicalChart.cotangentSheafRestrictionIso inclusion structureMap).inv.val.app (op domain)
        (differentialSection (inclusion ≫ structureMap) domain regularFunction) =
      differentialSection structureMap (inclusion.opensFunctor.obj domain)
        ((inclusion.appIso domain).inv regularFunction) := by
  let comparison := CanonicalChart.cotangentPresheafRestrictionIso inclusion structureMap
  have mapped := sheafificationMap_unit_app comparison.hom domain
    (CommRingCat.KaehlerDifferential.d regularFunction)
  have restricted := congrArg (fun morphism => morphism.app (op domain)
      ((CanonicalChart.cotangentChartSectionIso inclusion structureMap (op domain)).hom
        (CommRingCat.KaehlerDifferential.d regularFunction)))
    (restrictionSheafificationComparison_unit inclusion (cotangentPresheaf structureMap))
  have differential := CanonicalChart.cotangentChartSectionIso_d inclusion structureMap
    (op domain) regularFunction
  refine (congrArg ((CanonicalChart.restrictionSheafificationComparison inclusion
    (cotangentPresheaf structureMap)).val.app (op domain)) mapped).trans ?_
  exact restricted.trans (congrArg ((cotangentUnit structureMap).app
    (op (inclusion.opensFunctor.obj domain))) differential)

theorem exteriorSheafRestrictionIso_inv_unit_wedge {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules) (degree : ℕ) (domain : Chart.Opens)
    (vectors : Fin degree → (modules.restrict inclusion).val.obj (op domain)) :
    (CanonicalFanChart.exteriorSheafRestrictionIso inclusion modules degree).inv.val.app
        (op domain)
        ((exteriorUnit (modules.restrict inclusion) degree).app (op domain)
          (exteriorPower.ιMulti Γ(Chart, domain) degree vectors)) =
      (exteriorUnit modules degree).app (op (inclusion.opensFunctor.obj domain))
        (exteriorPower.ιMulti Γ(SchemeModel, inclusion.opensFunctor.obj domain) degree
          (fun index => (vectors index : modules.val.obj
            (op (inclusion.opensFunctor.obj domain))))) := by
  let comparison := CanonicalFanChart.exteriorPresheafRestrictionIso inclusion modules.val degree
  have mapped := sheafificationMap_unit_app comparison.hom domain
    (exteriorPower.ιMulti Γ(Chart, domain) degree vectors)
  have restricted := congrArg (fun morphism => morphism.app (op domain)
      (comparison.hom.app (op domain) (exteriorPower.ιMulti Γ(Chart, domain) degree vectors)))
    (restrictionSheafificationComparison_unit inclusion (exteriorPresheaf modules.val degree))
  refine (congrArg ((CanonicalChart.restrictionSheafificationComparison inclusion
    (exteriorPresheaf modules.val degree)).val.app (op domain)) mapped).trans ?_
  exact restricted.trans
    (congrArg ((exteriorUnit modules degree).app (op (inclusion.opensFunctor.obj domain)))
      (CanonicalFanChart.exteriorRestrictionSectionIso_wedge inclusion modules.val degree
        (op domain) vectors))

theorem canonicalExteriorRestrictionIso_inv_differentialTopSection
    {Chart SchemeModel Base : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ) (domain : Chart.Opens)
    (coordinates : Fin degree → Γ(Chart, domain)) :
    (CanonicalFanChart.canonicalExteriorRestrictionIso inclusion structureMap degree).inv.val.app
        (op domain)
        (differentialTopSection (inclusion ≫ structureMap) degree domain coordinates) =
      differentialTopSection structureMap degree (inclusion.opensFunctor.obj domain)
        (fun index => (inclusion.appIso domain).inv (coordinates index)) := by
  let comparison := CanonicalChart.cotangentSheafRestrictionIso inclusion structureMap
  have mapped := exteriorSheafIso_unit_wedge comparison.symm degree domain
    (fun index => differentialSection (inclusion ≫ structureMap) domain (coordinates index))
  have restricted := exteriorSheafRestrictionIso_inv_unit_wedge inclusion
    (cotangentSheaf structureMap) degree domain
    (fun index => comparison.inv.val.app (op domain)
      (differentialSection (inclusion ≫ structureMap) domain (coordinates index)))
  refine (congrArg
    ((CanonicalFanChart.exteriorSheafRestrictionIso inclusion
      (cotangentSheaf structureMap) degree).inv.val.app (op domain)) mapped).trans ?_
  refine restricted.trans ?_
  apply congrArg ((exteriorUnit (cotangentSheaf structureMap) degree).app
    (op (inclusion.opensFunctor.obj domain)))
  apply congrArg (exteriorPower.ιMulti Γ(SchemeModel, inclusion.opensFunctor.obj domain) degree)
  funext index
  exact cotangentSheafRestrictionIso_inv_differentialSection inclusion structureMap domain
    (coordinates index)

theorem cotangentSpecTilde_unit (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] :
    cotangentUnit (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) ≫
        (CotangentTilde.cotangentSheafSpecTildeIso Base CoordinateRing).hom.val =
      (CotangentTilde.cotangentSpecPresheafIso Base CoordinateRing).hom ≫
        CotangentTilde.affineDifferentialToTilde Base CoordinateRing := by
  have naturality :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).unit.naturality
        (CotangentTilde.cotangentSpecPresheafIso Base CoordinateRing).hom
  change (CotangentTilde.cotangentSpecPresheafIso Base CoordinateRing).hom ≫
      CotangentTilde.affineDifferentialUnit Base CoordinateRing =
    cotangentUnit (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) ≫
      ((PresheafOfModules.sheafification (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).map
        (CotangentTilde.cotangentSpecPresheafIso Base CoordinateRing).hom).val at naturality
  unfold CotangentTilde.cotangentSheafSpecTildeIso
  change cotangentUnit _ ≫
      (((PresheafOfModules.sheafification (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).map
        (CotangentTilde.cotangentSpecPresheafIso Base CoordinateRing).hom).val ≫
          (CotangentTilde.affineDifferentialSheafToTilde Base CoordinateRing).val) = _
  rw [← Category.assoc, ← naturality, Category.assoc,
    CotangentTilde.affineDifferentialSheafToTilde_unit]

theorem cotangentSpecTilde_differentialSection (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] (denominator regularFunction : CoordinateRing) :
    (CotangentTilde.cotangentSheafSpecTildeIso Base CoordinateRing).hom.val.app
        (op (PrimeSpectrum.basicOpen denominator))
        (differentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
          (PrimeSpectrum.basicOpen denominator)
          (algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)
            regularFunction)) =
      CanonicalTopExterior.tildeToBasicOpen CoordinateRing
        (CanonicalAffine.differentialModule Base CoordinateRing) denominator
        (KaehlerDifferential.D Base CoordinateRing regularFunction) := by
  have unitValue := congrArg (fun morphism => morphism.app
    (op (PrimeSpectrum.basicOpen denominator))
    (CommRingCat.KaehlerDifferential.d
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)
        regularFunction))) (cotangentSpecTilde_unit Base CoordinateRing)
  change _ = (CotangentTilde.affineDifferentialToTilde Base CoordinateRing).app
    (op (PrimeSpectrum.basicOpen denominator))
    ((CotangentTilde.cotangentSpecSectionIso Base CoordinateRing
      (op (PrimeSpectrum.basicOpen denominator))).hom
      (CommRingCat.KaehlerDifferential.d
        (algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)
          regularFunction))) at unitValue
  refine unitValue.trans ?_
  rw [CotangentTilde.cotangentSpecSectionIso_d]
  have onBasis := CotangentTilde.extendBasisModuleHom_app CoordinateRing
    (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing)
    (tilde (CanonicalAffine.differentialModule Base CoordinateRing))
    (CotangentTilde.basisDifferentialAdditiveIso Base CoordinateRing).inv
    (CotangentTilde.basisDifferentialAdditiveIso_inv_smul Base CoordinateRing)
    denominator
    (CommRingCat.KaehlerDifferential.d
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)
        regularFunction))
  refine onBasis.trans ?_
  apply (ConcreteCategory.bijective_of_isIso
    ((CotangentTilde.basisDifferentialAdditiveIso Base CoordinateRing).hom.app
      (op denominator))).injective
  exact (Iso.inv_hom_id_apply
    ((CotangentTilde.basisDifferentialAdditiveIso Base CoordinateRing).app (op denominator))
    (CommRingCat.KaehlerDifferential.d
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)
        regularFunction))).trans
    (CanonicalAffine.basicOpenDifferentialEquiv_toOpen_D
      Base CoordinateRing denominator regularFunction).symm

theorem exteriorSheafTilde_frame (CoordinateRing : CommRingCat)
    (modules : ModuleCat CoordinateRing) {dimension : ℕ}
    (basis : Basis (Fin dimension) CoordinateRing modules) (denominator : CoordinateRing) :
    (CanonicalExteriorDescent.exteriorSheafTildeIso CoordinateRing modules basis).hom.val.app
        (op (PrimeSpectrum.basicOpen denominator))
        ((exteriorUnit (tilde modules) dimension).app (op (PrimeSpectrum.basicOpen denominator))
          (exteriorPower.ιMulti Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator) dimension
            (CanonicalTopExterior.tildeBasicOpenBasis CoordinateRing modules basis denominator))) =
      CanonicalExteriorDescent.tildeTopBasis CoordinateRing modules basis denominator 0 := by
  exact (CanonicalExteriorDescent.exteriorSheafToTilde_unit_app CoordinateRing modules basis
    denominator _).trans
    (CanonicalExteriorDescent.basicOpenTopEquiv_frame CoordinateRing modules basis denominator)

noncomputable def affineCoordinateDifferentialTopSection (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] (dimension : ℕ)
    (coordinates : Fin dimension → CoordinateRing) (denominator : CoordinateRing) :
    (canonicalExteriorSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) dimension).val.obj
        (op (PrimeSpectrum.basicOpen denominator)) :=
  differentialTopSection (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) dimension
    (PrimeSpectrum.basicOpen denominator)
    (fun index => algebraMap CoordinateRing
      Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator) (coordinates index))

theorem canonicalExteriorSpecTilde_coordinateFrame (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] {dimension : ℕ}
    (basis : Basis (Fin dimension) CoordinateRing (KaehlerDifferential Base CoordinateRing))
    (coordinates : Fin dimension → CoordinateRing)
    (coordinate_differentials : ∀ index, basis index =
      KaehlerDifferential.D Base CoordinateRing (coordinates index))
    (denominator : CoordinateRing) :
    (CanonicalExteriorDescent.canonicalExteriorSpecTildeIso Base CoordinateRing basis).hom.val.app
        (op (PrimeSpectrum.basicOpen denominator))
        (differentialTopSection
          (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) dimension
          (PrimeSpectrum.basicOpen denominator)
          (fun index => algebraMap CoordinateRing
            Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator) (coordinates index))) =
      CanonicalExteriorDescent.tildeTopBasis CoordinateRing
        (CanonicalAffine.differentialModule Base CoordinateRing) basis denominator 0 := by
  let comparison := CotangentTilde.cotangentSheafSpecTildeIso Base CoordinateRing
  have transported := exteriorSheafIso_unit_wedge comparison dimension
    (PrimeSpectrum.basicOpen denominator)
    (fun index => differentialSection
      (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
      (PrimeSpectrum.basicOpen denominator)
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)
        (coordinates index)))
  have frames :
      (fun index => comparison.hom.val.app (op (PrimeSpectrum.basicOpen denominator))
        (differentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
          (PrimeSpectrum.basicOpen denominator)
          (algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)
            (coordinates index)))) =
      CanonicalTopExterior.tildeBasicOpenBasis CoordinateRing
        (CanonicalAffine.differentialModule Base CoordinateRing) basis denominator := by
    funext index
    exact (cotangentSpecTilde_differentialSection Base CoordinateRing denominator
      (coordinates index)).trans
      ((congrArg (CanonicalTopExterior.tildeToBasicOpen CoordinateRing
        (CanonicalAffine.differentialModule Base CoordinateRing) denominator)
        (coordinate_differentials index).symm).trans
        (CanonicalTopExterior.tildeBasicOpenBasis_apply CoordinateRing
          (CanonicalAffine.differentialModule Base CoordinateRing) basis denominator index).symm)
  rw [frames] at transported
  exact (congrArg
    ((CanonicalExteriorDescent.exteriorSheafTildeIso CoordinateRing
      (CanonicalAffine.differentialModule Base CoordinateRing) basis).hom.val.app
        (op (PrimeSpectrum.basicOpen denominator))) transported).trans
    (exteriorSheafTilde_frame CoordinateRing
      (CanonicalAffine.differentialModule Base CoordinateRing) basis denominator)

noncomputable def affineRegularSection (CoordinateRing : CommRingCat)
    (denominator coordinate : CoordinateRing) :
    Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator) :=
  algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator) coordinate

noncomputable def affineDifferentialSectionMap (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] (denominator : CoordinateRing) :
    KaehlerDifferential Base CoordinateRing →ₛₗ[
      algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)]
      (cotangentSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))).val.obj
          (op (PrimeSpectrum.basicOpen denominator)) := by
  let localized := CanonicalTopExterior.tildeToBasicOpen CoordinateRing
    (CanonicalAffine.differentialModule Base CoordinateRing) denominator
  let comparison := (CotangentTilde.cotangentSheafSpecTildeIso Base CoordinateRing).inv.val.app
    (op (PrimeSpectrum.basicOpen denominator))
  exact
    { toFun := fun vector => comparison (localized vector)
      map_add' := fun first second => by rw [map_add, map_add]
      map_smul' := fun scalar vector => by
        change comparison (localized (scalar • vector)) =
          algebraMap CoordinateRing Γ(Spec CoordinateRing,
            PrimeSpectrum.basicOpen denominator) scalar • comparison (localized vector)
        rw [localized.hom.map_smul]
        exact comparison.hom.map_smul _ _ }

theorem affineDifferentialSectionMap_D (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] (denominator coordinate : CoordinateRing) :
    affineDifferentialSectionMap Base CoordinateRing denominator
        (KaehlerDifferential.D Base CoordinateRing coordinate) =
      differentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
        (PrimeSpectrum.basicOpen denominator)
        (algebraMap CoordinateRing Γ(Spec CoordinateRing,
          PrimeSpectrum.basicOpen denominator) coordinate) := by
  let comparison := CotangentTilde.cotangentSheafSpecTildeIso Base CoordinateRing
  refine (congrArg (comparison.inv.val.app (op (PrimeSpectrum.basicOpen denominator)))
    (cotangentSpecTilde_differentialSection Base CoordinateRing denominator coordinate).symm).trans ?_
  exact congrArg (fun morphism => morphism.val.app (op (PrimeSpectrum.basicOpen denominator))
    (differentialSection
      (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
      (PrimeSpectrum.basicOpen denominator)
      (algebraMap CoordinateRing Γ(Spec CoordinateRing,
        PrimeSpectrum.basicOpen denominator) coordinate))) comparison.hom_inv_id

noncomputable def affineTopExteriorSectionMap (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] (degree : ℕ) (denominator : CoordinateRing) :
    (⋀[CoordinateRing]^degree (KaehlerDifferential Base CoordinateRing)) →ₛₗ[
      algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)]
      (canonicalExteriorSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) degree).val.obj
          (op (PrimeSpectrum.basicOpen denominator)) := by
  let coefficientMap := algebraMap CoordinateRing
    Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)
  let differentialMap := affineDifferentialSectionMap Base CoordinateRing denominator
  let exteriorMap := SemilinearExterior.map degree coefficientMap differentialMap
  let unit := (exteriorUnit
    (cotangentSheaf (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))) degree).app
      (op (PrimeSpectrum.basicOpen denominator))
  exact unit.hom.comp exteriorMap

theorem affineTopExteriorSectionMap_wedge_D (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] (degree : ℕ) (denominator : CoordinateRing)
    (coordinates : Fin degree → CoordinateRing) :
    affineTopExteriorSectionMap Base CoordinateRing degree denominator
        (exteriorPower.ιMulti CoordinateRing degree
          (fun index => KaehlerDifferential.D Base CoordinateRing (coordinates index))) =
      affineCoordinateDifferentialTopSection Base CoordinateRing degree coordinates denominator := by
  unfold affineTopExteriorSectionMap
  change (exteriorUnit
    (cotangentSheaf (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))) degree).app
      (op (PrimeSpectrum.basicOpen denominator))
      (SemilinearExterior.map degree
        (algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator))
        (affineDifferentialSectionMap Base CoordinateRing denominator)
        (exteriorPower.ιMulti CoordinateRing degree
          (fun index => KaehlerDifferential.D Base CoordinateRing (coordinates index)))) = _
  rw [SemilinearExterior.map_wedge]
  unfold affineCoordinateDifferentialTopSection differentialTopSection
  apply congrArg ((exteriorUnit
    (cotangentSheaf (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))) degree).app
      (op (PrimeSpectrum.basicOpen denominator)))
  apply congrArg (exteriorPower.ιMulti
    Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator) degree)
  funext index
  exact affineDifferentialSectionMap_D Base CoordinateRing denominator (coordinates index)

end BondalThomsen.CanonicalRaySumSheaf

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def basisConeCanonicalDifferentialFrame (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice)
    (denominator : affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (BondalThomsen.canonicalExteriorSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 CoordinateRing))) dimension).val.obj
        (op (PrimeSpectrum.basicOpen denominator)) := by
  let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
    (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
  exact BondalThomsen.CanonicalRaySumSheaf.affineCoordinateDifferentialTopSection
    (CommRingCat.of 𝕜) CoordinateRing dimension
    (fun index => MonoidAlgebra.single
      (Multiplicative.ofAdd (fan.basisConeDualStep basis index)) (1 : 𝕜)) denominator

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def canonicalFaceDifferentialSheafFrame (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face) :
    let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face)
    (BondalThomsen.canonicalExteriorSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 CoordinateRing))) dimension).val.obj
        (op (PrimeSpectrum.basicOpen denominator)) :=
  BondalThomsen.CanonicalRaySumSheaf.affineTopExteriorSectionMap (CommRingCat.of 𝕜)
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face)) dimension denominator
    (fan.canonicalFaceCoordinateWedge 𝕜 basis face_of)

theorem canonicalFaceDifferentialSheafFrame_eq (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face) :
    fan.canonicalFaceDifferentialSheafFrame 𝕜 basis face_of denominator =
      BondalThomsen.CanonicalRaySumSheaf.affineCoordinateDifferentialTopSection (CommRingCat.of 𝕜)
        (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face)) dimension
        (fan.canonicalFaceCoordinate 𝕜 basis face_of) denominator :=
  BondalThomsen.CanonicalRaySumSheaf.affineTopExteriorSectionMap_wedge_D _ _ _ _ _

noncomputable def canonicalOrientedFaceDifferentialSheafFrame (fan : Fan embedding)
    (reference basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face) :
    let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face)
    (BondalThomsen.canonicalExteriorSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 CoordinateRing))) dimension).val.obj
        (op (PrimeSpectrum.basicOpen denominator)) :=
  BondalThomsen.CanonicalRaySumSheaf.affineTopExteriorSectionMap (CommRingCat.of 𝕜)
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face)) dimension denominator
    (fan.canonicalOrientedFaceCoordinateWedge 𝕜 reference basis face_of)

theorem canonicalOverlapOrientedDifferentialSheafFrame_transition (fan : Fan embedding)
    (regular : fan.IsRegular) (reference : Basis (Fin dimension) ℤ Lattice)
    (first : Basis (Fin dimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin dimension) ℤ Lattice) (second_cone : fan.IsConeBasis second)
    (denominator : affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
        PointedCone.hull ℝ (Set.range (fun index => embedding (second index))))) :
    let first_face := fan.inf_isFaceOf_left first_cone second_cone
    let second_face := fan.inf_isFaceOf_right first_cone second_cone
    let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
        PointedCone.hull ℝ (Set.range (fun index => embedding (second index)))))
    (fan.canonicalOrientedFaceDifferentialSheafFrame 𝕜) reference second second_face denominator =
      BondalThomsen.CanonicalRaySumSheaf.affineRegularSection CoordinateRing denominator
        (((fan.coneDivisorTransitionUnit 𝕜 first first_cone second second_cone
          (-fan.anticanonicalRayDivisor))⁻¹ : CoordinateRingˣ) : CoordinateRing) •
        fan.canonicalOrientedFaceDifferentialSheafFrame 𝕜 reference first first_face denominator := by
  let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
    (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
      PointedCone.hull ℝ (Set.range (fun index => embedding (second index)))))
  let realization := BondalThomsen.CanonicalRaySumSheaf.affineTopExteriorSectionMap
    (CommRingCat.of 𝕜) CoordinateRing dimension denominator
  have transition := fan.canonicalOverlapOrientedCoordinateWedge_transition 𝕜
    regular reference first first_cone second second_cone
  exact (congrArg realization transition).trans
    (realization.map_smulₛₗ _ _)

end TauCeti.Toric.Fan
