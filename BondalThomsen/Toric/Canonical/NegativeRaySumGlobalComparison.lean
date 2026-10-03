module

public import BondalThomsen.Toric.Canonical.NegativeRaySumDescent

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CanonicalNegativeRaySumGlobal

theorem openImmersionUnitRestrictionIso_inv_app {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf)
    (domain : (inclusion.opensRange : Scheme).Opens)
    (sectionValue : (modules.restrict inclusion.opensRange.ι).val.obj (op domain)) :
    (CanonicalInvertible.openImmersionUnitRestrictionIso inclusion modules coordinates).inv.val.app
        (op domain) sectionValue =
    (inclusion.isoOpensRange.inv.appIso domain).hom
      (coordinates.hom.val.app (op (inclusion.isoOpensRange.inv.opensFunctor.obj domain))
        (((Scheme.Modules.restrictFunctorComp inclusion.isoOpensRange.inv inclusion).hom.app
          modules).val.app (op domain)
          (((Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_inv_comp).inv.app
            modules).val.app (op domain) sectionValue))) := rfl

theorem openImmersionUnitOverIso_map_hom {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf) :
    (Scheme.Modules.overEquiv inclusion.opensRange).functor.map
      (CanonicalNegativeRaySum.openImmersionUnitOverIso inclusion modules coordinates).hom =
    ((Scheme.Modules.overFunctorEquiv inclusion.opensRange).app modules).hom ≫
      (CanonicalInvertible.openImmersionUnitRestrictionIso inclusion modules coordinates).inv := by
  unfold CanonicalNegativeRaySum.openImmersionUnitOverIso
  simp only [Iso.symm_hom, Functor.FullyFaithful.preimageIso_inv,
    Functor.FullyFaithful.map_preimage, Iso.trans_inv, Iso.symm_inv]

theorem openImmersionUnitOverIso_hom_overOpen {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf)
    (domain : (inclusion.opensRange : Scheme).Opens)
    (sectionValue : (modules.over inclusion.opensRange).val.obj
      (op (inclusion.opensRange.overEquivalence.inverse.obj domain))) :
    (CanonicalNegativeRaySum.openImmersionUnitOverIso inclusion modules coordinates).hom.val.app
      (op (inclusion.opensRange.overEquivalence.inverse.obj domain)) sectionValue =
    (inclusion.isoOpensRange.inv.appIso domain).hom
      (coordinates.hom.val.app (op (inclusion.isoOpensRange.inv.opensFunctor.obj domain))
        (((Scheme.Modules.restrictFunctorComp inclusion.isoOpensRange.inv inclusion).hom.app
          modules).val.app (op domain)
          (((Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_inv_comp).inv.app
            modules).val.app (op domain) sectionValue))) := by
  have actualMap := congrArg (fun morphism => morphism.val.app (op domain) sectionValue)
    (openImmersionUnitOverIso_map_hom inclusion modules coordinates)
  exact actualMap.trans
    (openImmersionUnitRestrictionIso_inv_app inclusion modules coordinates domain sectionValue)

theorem openChartSectionTransport {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules) (domain : (inclusion.opensRange : Scheme).Opens) :
    ((Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_inv_comp).inv.app
        modules).app domain ≫
      ((Scheme.Modules.restrictFunctorComp inclusion.isoOpensRange.inv inclusion).hom.app
        modules).app domain =
    modules.presheaf.map (eqToHom (show inclusion.opensFunctor.obj
        (inclusion.isoOpensRange.inv.opensFunctor.obj domain) =
          inclusion.opensRange.ι.opensFunctor.obj domain by
      simp only [← Scheme.Hom.comp_image, inclusion.isoOpensRange_inv_comp])).op := by
  rw [Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, ← Functor.map_comp]
  congr 1

theorem openChartImageEquality {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (domain : (inclusion.opensRange : Scheme).Opens) :
    inclusion.opensFunctor.obj (inclusion.isoOpensRange.inv.opensFunctor.obj domain) =
      inclusion.opensRange.ι.opensFunctor.obj domain := by
  simp only [← Scheme.Hom.comp_image, inclusion.isoOpensRange_inv_comp]

theorem moduleEqualityTransport_roundtrip {SchemeModel : Scheme}
    (modules : SchemeModel.Modules) {first second : SchemeModel.Opens}
    (domain_eq : first = second) (sectionValue : modules.val.obj (op first)) :
    modules.val.map (eqToHom domain_eq).op
      (modules.val.map (eqToHom domain_eq.symm).op sectionValue) = sectionValue := by
  cases domain_eq
  have identityMap := ConcreteCategory.congr_hom (modules.val.presheaf.map_id (op first))
    sectionValue
  change modules.val.presheaf.map (𝟙 _) (modules.val.presheaf.map (𝟙 _) sectionValue) = _
  exact (congrArg (modules.val.presheaf.map (𝟙 (op first))) identityMap).trans identityMap

noncomputable def openChartSection {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules) (domain : (inclusion.opensRange : Scheme).Opens)
    (sectionValue : (modules.restrict inclusion).val.obj
      (op (inclusion.isoOpensRange.inv.opensFunctor.obj domain))) :
    (modules.over inclusion.opensRange).val.obj
      (op (inclusion.opensRange.overEquivalence.inverse.obj domain)) :=
  modules.val.map (eqToHom (openChartImageEquality inclusion domain).symm).op sectionValue

theorem openImmersionUnitOverIso_hom_chartSection {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf)
    (domain : (inclusion.opensRange : Scheme).Opens)
    (sectionValue : (modules.restrict inclusion).val.obj
      (op (inclusion.isoOpensRange.inv.opensFunctor.obj domain))) :
    (CanonicalNegativeRaySum.openImmersionUnitOverIso inclusion modules coordinates).hom.val.app
      (op (inclusion.opensRange.overEquivalence.inverse.obj domain))
      (openChartSection inclusion modules domain sectionValue) =
    (inclusion.isoOpensRange.inv.appIso domain).hom
      (coordinates.hom.val.app (op (inclusion.isoOpensRange.inv.opensFunctor.obj domain))
        sectionValue) := by
  refine (openImmersionUnitOverIso_hom_overOpen inclusion modules coordinates domain _).trans ?_
  have transported := ConcreteCategory.congr_hom
    (openChartSectionTransport inclusion modules domain)
    (openChartSection inclusion modules domain sectionValue)
  have roundtrip := moduleEqualityTransport_roundtrip modules
    (openChartImageEquality inclusion domain) sectionValue
  exact congrArg (fun value => (inclusion.isoOpensRange.inv.appIso domain).hom
    (coordinates.hom.val.app (op (inclusion.isoOpensRange.inv.opensFunctor.obj domain)) value))
      (transported.trans roundtrip)

theorem openImmersionUnitOverIso_hom_chartFrame {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf)
    (domain : (inclusion.opensRange : Scheme).Opens)
    (sectionValue : (modules.restrict inclusion).val.obj
      (op (inclusion.isoOpensRange.inv.opensFunctor.obj domain)))
    (coordinate_one : coordinates.hom.val.app
      (op (inclusion.isoOpensRange.inv.opensFunctor.obj domain)) sectionValue =
        (1 : Γ(Chart, inclusion.isoOpensRange.inv.opensFunctor.obj domain))) :
    (CanonicalNegativeRaySum.openImmersionUnitOverIso inclusion modules coordinates).hom.val.app
      (op (inclusion.opensRange.overEquivalence.inverse.obj domain))
      (openChartSection inclusion modules domain sectionValue) =
      (1 : Γ(SchemeModel, (inclusion.opensRange.overEquivalence.inverse.obj domain).left)) := by
  exact (openImmersionUnitOverIso_hom_chartSection inclusion modules coordinates domain
    sectionValue).trans ((congrArg (inclusion.isoOpensRange.inv.appIso domain).hom
      coordinate_one).trans (map_one _))

theorem openChartSection_restrictedFrame_eq_map {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (frame : (modules.restrict inclusion).val.obj (op ⊤))
    (domain : (inclusion.opensRange : Scheme).Opens) :
    openChartSection inclusion modules domain
      ((modules.restrict inclusion).val.map
        (inclusion.isoOpensRange.inv.opensFunctor.obj domain).leTop.op frame) =
    modules.val.map (homOfLE (show
      (inclusion.opensRange.overEquivalence.inverse.obj domain).left ≤
        inclusion.opensFunctor.obj ⊤ from
      (inclusion.opensRange.overEquivalence.inverse.obj domain).hom.le.trans
        inclusion.image_top_eq_opensRange.symm.le)).op frame := by
  unfold openChartSection
  change modules.val.presheaf.map _ (modules.val.presheaf.map _ frame) =
    modules.val.presheaf.map _ frame
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

theorem orientedGlobalCanonicalChartUnitIso_topFrame {SchemeModel : Scheme}
    (Base CoordinateRing : CommRingCat) [Algebra Base CoordinateRing]
    (inclusion : Spec CoordinateRing ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Spec Base)
    (structure_eq : inclusion ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
    {degree : ℕ} (basis : Basis (Fin degree) CoordinateRing
      (KaehlerDifferential Base CoordinateRing)) (orientation : ℤˣ)
    (coordinates : Fin degree → CoordinateRing)
    (coordinate_differentials : ∀ index,
      basis index = KaehlerDifferential.D Base CoordinateRing (coordinates index)) :
    (CanonicalNegativeRaySum.orientedGlobalCanonicalChartUnitIso Base CoordinateRing inclusion
      structureMap structure_eq basis orientation).hom.val.app (op ⊤)
      ((orientation : ℤ) • CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing
        inclusion structureMap degree ⊤ coordinates) =
      (1 : Γ(Spec CoordinateRing, ⊤)) := by
  let frameProperty (domain : (Spec CoordinateRing).Opens) : Prop :=
    (CanonicalNegativeRaySum.orientedGlobalCanonicalChartUnitIso Base CoordinateRing inclusion
      structureMap structure_eq basis orientation).hom.val.app (op domain)
      ((orientation : ℤ) • CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing
        inclusion structureMap degree domain coordinates) = (1 : Γ(Spec CoordinateRing, domain))
  have principal : frameProperty (PrimeSpectrum.basicOpen (1 : CoordinateRing)) :=
    CanonicalNegativeRaySum.orientedGlobalCanonicalChartUnitIso_frame Base
    CoordinateRing inclusion structureMap structure_eq basis orientation coordinates
    coordinate_differentials (1 : CoordinateRing)
  exact Eq.mp (congrArg frameProperty (PrimeSpectrum.basicOpen_one (R := CoordinateRing))) principal

theorem unitChartIso_restrictedFrame {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf)
    (frame : (modules.restrict inclusion).val.obj (op ⊤))
    (frame_one : coordinates.hom.val.app (op ⊤) frame = (1 : Γ(Chart, ⊤)))
    (domain : Chart.Opens) :
    coordinates.hom.val.app (op domain)
      ((modules.restrict inclusion).val.map domain.leTop.op frame) =
        (1 : Γ(Chart, domain)) := by
  have naturality := PresheafOfModules.naturality_apply coordinates.hom.val domain.leTop.op frame
  exact naturality.trans
    ((congrArg ((SheafOfModules.unit Chart.ringCatSheaf).val.map domain.leTop.op)
      frame_one).trans (map_one (Chart.presheaf.map domain.leTop.op).hom))

theorem cartierAtlasFrameRestriction_eq_trivialization {SchemeModel : Scheme}
    [IsIntegral SchemeModel] (atlas : CartierEquationAtlas SchemeModel) (index : atlas.Index)
    (domain : SchemeModel.Opens) (contained : domain ≤ atlas.chart index) :
    CanonicalNegativeRaySum.cartierAtlasFrameRestriction atlas index domain contained =
      (atlas.chartTrivialization index).hom.val.app (op (Over.mk (homOfLE contained)))
        (1 : Γ(SchemeModel, domain)) := by
  have naturality := PresheafOfModules.naturality_apply (atlas.chartTrivialization index).hom.val
    (Over.homMk (homOfLE contained) : Over.mk (homOfLE contained) ⟶
      Over.mk (𝟙 (atlas.chart index))).op (1 : Γ(SchemeModel, atlas.chart index))
  have restrictedOne : ((SheafOfModules.unit SchemeModel.ringCatSheaf).over
      (atlas.chart index)).val.map
      (Over.homMk (homOfLE contained) : Over.mk (homOfLE contained) ⟶
        Over.mk (𝟙 (atlas.chart index))).op (1 : Γ(SchemeModel, atlas.chart index)) =
        (1 : Γ(SchemeModel, domain)) :=
    map_one (SchemeModel.presheaf.map (homOfLE contained).op).hom
  exact naturality.symm.trans (congrArg
    ((atlas.chartTrivialization index).hom.val.app (op (Over.mk (homOfLE contained)))) restrictedOne)

end BondalThomsen.CanonicalNegativeRaySumGlobal

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

theorem basisCone_reindex (_fan : Fan embedding)
    {firstSize secondSize : ℕ} (basis : Basis (Fin firstSize) ℤ Lattice)
    (indices : Fin firstSize ≃ Fin secondSize) :
    PointedCone.hull ℝ (Set.range (fun index => embedding ((basis.reindex indices) index))) =
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
  apply congrArg (PointedCone.hull ℝ)
  ext vector
  constructor
  · rintro ⟨index, rfl⟩
    exact ⟨indices.symm index, congrArg embedding (basis.reindex_apply indices index).symm⟩
  · rintro ⟨index, rfl⟩
    exact ⟨indices index, (congrArg embedding (basis.reindex_apply indices (indices index))).trans
      (congrArg (fun original => embedding (basis original)) (indices.symm_apply_apply index))⟩

noncomputable def canonicalDivisorChartRankBasis [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (cone : fan.cones) : Basis (Fin (Module.finrank ℤ Lattice)) ℤ Lattice := by
  let basisData := fan.divisorChartBasis complete regular cone
  have dimension_eq : basisData.val.1 = Module.finrank ℤ Lattice := by
    simpa using (Module.finrank_eq_card_basis basisData.val.2).symm
  exact basisData.val.2.reindex (finCongr dimension_eq)

theorem canonicalDivisorChartRankBasis_cone [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (cone : fan.cones) :
    PointedCone.hull ℝ (Set.range (fun index =>
      embedding (fan.canonicalDivisorChartRankBasis complete regular cone index))) =
      (fan.divisorChartCone complete regular cone).val := by
  unfold canonicalDivisorChartRankBasis
  exact fan.basisCone_reindex _ _

theorem canonicalDivisorChartRankBasis_isConeBasis [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (cone : fan.cones) : fan.IsConeBasis (fan.canonicalDivisorChartRankBasis complete regular cone) := by
  change PointedCone.hull ℝ (Set.range (fun index =>
    embedding (fan.canonicalDivisorChartRankBasis complete regular cone index))) ∈ fan.cones
  rw [fan.canonicalDivisorChartRankBasis_cone complete regular cone]
  exact (fan.divisorChartCone complete regular cone).property

theorem basisConeOrientedCanonicalUnitIso_topFrame (fan : Fan embedding)
    (regular : fan.IsRegular) (reference basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    (fan.basisConeOrientedCanonicalUnitIso 𝕜 regular reference basis cone_basis).hom.val.app (op ⊤)
      (fan.basisConeOrientedGlobalCanonicalFrame 𝕜 regular reference basis cone_basis) =
    (1 : Γ(affineToricScheme 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))), ⊤)) :=
  BondalThomsen.CanonicalNegativeRaySumGlobal.orientedGlobalCanonicalChartUnitIso_topFrame
    (CommRingCat.of 𝕜) (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))))
    (fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩) (fan.structureMap 𝕜 regular)
    (fan.chartι_comp_structureMap 𝕜 regular ⟨_, cone_basis⟩)
    (fan.basisConeDifferentialBasis 𝕜 basis) (fan.canonicalOrientationUnit reference basis)
    (fun index => MonoidAlgebra.single
      (Multiplicative.ofAdd (fan.basisConeDualStep basis index)) (1 : 𝕜))
    (fan.basisConeDifferentialBasis_apply 𝕜 basis)

end TauCeti.Toric.Fan

namespace BondalThomsen.CanonicalNegativeRaySumGlobal

theorem openImmersionUnitOverIso_hom_restrictedFrame {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf)
    (frame : (modules.restrict inclusion).val.obj (op ⊤))
    (frame_one : coordinates.hom.val.app (op ⊤) frame = (1 : Γ(Chart, ⊤)))
    (domain : SchemeModel.Opens) (contained : domain ≤ inclusion.opensRange) :
    (CanonicalNegativeRaySum.openImmersionUnitOverIso inclusion modules coordinates).hom.val.app
      (op (Over.mk (homOfLE contained)))
      (modules.val.map (homOfLE (contained.trans inclusion.image_top_eq_opensRange.symm.le)).op
        frame) = (1 : Γ(SchemeModel, domain)) := by
  let overDomain : Over inclusion.opensRange := Over.mk (homOfLE contained)
  let chartDomain := inclusion.opensRange.overEquivalence.functor.obj overDomain
  let comparison := CanonicalNegativeRaySum.openImmersionUnitOverIso inclusion modules coordinates
  have frameCoordinate := openImmersionUnitOverIso_hom_chartFrame inclusion modules coordinates
    chartDomain _ (unitChartIso_restrictedFrame inclusion modules coordinates frame frame_one _)
  have restrictedFrame := openChartSection_restrictedFrame_eq_map inclusion modules frame chartDomain
  have frameCoordinate' := (congrArg
    (comparison.hom.val.app (op (inclusion.opensRange.overEquivalence.inverse.obj chartDomain)))
    restrictedFrame.symm).trans frameCoordinate
  have naturality := PresheafOfModules.naturality_apply comparison.hom.val
    (inclusion.opensRange.overEquivalence.unitIso.app overDomain).hom.op
    (modules.val.map (homOfLE
      ((inclusion.opensRange.overEquivalence.inverse.obj chartDomain).hom.le.trans
        inclusion.image_top_eq_opensRange.symm.le)).op frame)
  have frameRestriction : (modules.over inclusion.opensRange).val.map
      (inclusion.opensRange.overEquivalence.unitIso.app overDomain).hom.op
      (modules.val.map (homOfLE
        ((inclusion.opensRange.overEquivalence.inverse.obj chartDomain).hom.le.trans
          inclusion.image_top_eq_opensRange.symm.le)).op frame) =
      modules.val.map (homOfLE (contained.trans inclusion.image_top_eq_opensRange.symm.le)).op
        frame := by
    change modules.val.presheaf.map _ (modules.val.presheaf.map _ frame) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  exact (congrArg (comparison.hom.val.app (op overDomain)) frameRestriction.symm).trans
    (naturality.trans ((congrArg
      ((SheafOfModules.unit SchemeModel.ringCatSheaf).over inclusion.opensRange |>.val.map
        (inclusion.opensRange.overEquivalence.unitIso.app overDomain).hom.op)
      frameCoordinate').trans (map_one (SchemeModel.presheaf.map
        (inclusion.opensRange.overEquivalence.unitIso.app overDomain).hom.left.op).hom)))

theorem normalizedChartIso_restrictedFrame_cartierGenerator {Chart SchemeModel : Scheme}
    [IsIntegral SchemeModel] (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf)
    (frame : (modules.restrict inclusion).val.obj (op ⊤))
    (frame_one : coordinates.hom.val.app (op ⊤) frame = (1 : Γ(Chart, ⊤)))
    (atlas : CartierEquationAtlas SchemeModel) (index : atlas.Index)
    (chart_eq : atlas.chart index = inclusion.opensRange)
    (domain : SchemeModel.Opens) (contained : domain ≤ inclusion.opensRange) :
    let localIso := CanonicalNegativeRaySum.openImmersionUnitOverIso inclusion modules coordinates ≪≫
      CanonicalGlobalRaySum.restrictLocalModuleIso chart_eq.symm.le
        (atlas.chartTrivialization index)
    localIso.hom.val.app (op (Over.mk (homOfLE contained)))
      (modules.val.map (homOfLE (contained.trans inclusion.image_top_eq_opensRange.symm.le)).op
        frame) =
    CanonicalNegativeRaySum.cartierAtlasFrameRestriction atlas index domain
      (contained.trans chart_eq.symm.le) := by
  dsimp only
  exact (congrArg
    ((CanonicalGlobalRaySum.restrictLocalModuleIso chart_eq.symm.le
      (atlas.chartTrivialization index)).hom.val.app (op (Over.mk (homOfLE contained))))
    (openImmersionUnitOverIso_hom_restrictedFrame inclusion modules coordinates frame frame_one
      domain contained)).trans
    (cartierAtlasFrameRestriction_eq_trivialization atlas index domain _).symm

end BondalThomsen.CanonicalNegativeRaySumGlobal

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

theorem normalizedCanonicalCartierIso_faceSection (fan : Fan embedding)
    (regular : fan.IsRegular) [IsIntegral (fan.algebraicRealization 𝕜 regular)]
    (reference basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (atlas : BondalThomsen.CartierEquationAtlas (fan.algebraicRealization 𝕜 regular)) (index : atlas.Index)
    (chart_eq : atlas.chart index = (fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩).opensRange)
    (face : fan.cones)
    (face_of : face.val.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face.val) :
    let inclusion := fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩
    let domain := (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj
      (PrimeSpectrum.basicOpen denominator)
    let contained := (fan.canonicalFaceChartLE 𝕜 regular (cone := ⟨_, cone_basis⟩) face_of
      (PrimeSpectrum.basicOpen denominator)).trans inclusion.image_top_eq_opensRange.le
    let localIso := BondalThomsen.CanonicalNegativeRaySum.openImmersionUnitOverIso inclusion
      (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension)
      (fan.basisConeOrientedCanonicalUnitIso 𝕜 regular reference basis cone_basis) ≪≫
      BondalThomsen.CanonicalGlobalRaySum.restrictLocalModuleIso chart_eq.symm.le
        (atlas.chartTrivialization index)
    localIso.hom.val.app (op (Over.mk (homOfLE contained)))
      (fan.globalOrientedFaceCanonicalSection 𝕜 regular reference basis face face_of denominator) =
    BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction atlas index domain
      (contained.trans chart_eq.symm.le) := by
  dsimp only
  have restriction := fan.basisConeOrientedGlobalCanonicalFrame_restriction 𝕜 regular reference
    basis cone_basis face face_of denominator
  have image := BondalThomsen.CanonicalNegativeRaySumGlobal.normalizedChartIso_restrictedFrame_cartierGenerator
    (fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩) (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension)
    (fan.basisConeOrientedCanonicalUnitIso 𝕜 regular reference basis cone_basis)
    (fan.basisConeOrientedGlobalCanonicalFrame 𝕜 regular reference basis cone_basis)
    (fan.basisConeOrientedCanonicalUnitIso_topFrame 𝕜 regular reference basis cone_basis)
    atlas index chart_eq _ ((fan.canonicalFaceChartLE 𝕜 regular (cone := ⟨_, cone_basis⟩) face_of
      (PrimeSpectrum.basicOpen denominator)).trans
        (fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩).image_top_eq_opensRange.le)
  exact (congrArg
    (((BondalThomsen.CanonicalNegativeRaySum.openImmersionUnitOverIso
      (fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩) (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension)
      (fan.basisConeOrientedCanonicalUnitIso 𝕜 regular reference basis cone_basis)) ≪≫
      BondalThomsen.CanonicalGlobalRaySum.restrictLocalModuleIso chart_eq.symm.le
        (atlas.chartTrivialization index)).hom.val.app (op (Over.mk (homOfLE
          ((fan.canonicalFaceChartLE 𝕜 regular (cone := ⟨_, cone_basis⟩) face_of
            (PrimeSpectrum.basicOpen denominator)).trans
            (fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩).image_top_eq_opensRange.le)))))
    restriction.symm).trans image

theorem coneDivisorCharacter_reindex (fan : Fan embedding)
    {firstSize secondSize : ℕ} (basis : Basis (Fin firstSize) ℤ Lattice)
    (indices : Fin firstSize ≃ Fin secondSize) (cone_basis : fan.IsConeBasis basis)
    (reindexed_cone : fan.IsConeBasis (basis.reindex indices))
    (divisor : fan.InvariantRayDivisor) :
    fan.coneDivisorCharacter (basis.reindex indices) reindexed_cone divisor =
      fan.coneDivisorCharacter basis cone_basis divisor := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  have basisValue : (basis.reindex indices) (indices index) = basis index := by
    exact (basis.reindex_apply indices (indices index)).trans
      (congrArg basis (indices.symm_apply_apply index))
  change fan.coneDivisorCharacter (basis.reindex indices) reindexed_cone divisor (basis index) =
    fan.coneDivisorCharacter basis cone_basis divisor (basis index)
  rw [← basisValue, fan.coneDivisorCharacter_basis]
  rw [basisValue, fan.coneDivisorCharacter_basis]
  congr 2
  exact Subtype.ext basisValue

theorem canonicalDivisorChartRankBasis_character [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (cone : fan.cones) (divisor : fan.InvariantRayDivisor) :
    fan.coneDivisorCharacter (fan.canonicalDivisorChartRankBasis complete regular cone)
      (fan.canonicalDivisorChartRankBasis_isConeBasis complete regular cone) divisor =
    fan.coneDivisorCharacter (fan.divisorChartBasis complete regular cone).val.2
      (fan.divisorChartBasis complete regular cone).property.1 divisor := by
  unfold canonicalDivisorChartRankBasis
  exact fan.coneDivisorCharacter_reindex _ _ _ _ divisor

theorem canonicalDivisorChartRankBasis_chart [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (cone : fan.cones) :
    (fan.affineToricChartι 𝕜 regular
      ⟨_, fan.canonicalDivisorChartRankBasis_isConeBasis complete regular cone⟩).opensRange =
    (fan.affineToricChartι 𝕜 regular (fan.divisorChartCone complete regular cone)).opensRange := by
  have coneEquality : (⟨_, fan.canonicalDivisorChartRankBasis_isConeBasis complete regular cone⟩ :
      fan.cones) = fan.divisorChartCone complete regular cone :=
    Subtype.ext (fan.canonicalDivisorChartRankBasis_cone complete regular cone)
  exact congrArg (fun actualCone => (fan.affineToricChartι 𝕜 regular actualCone).opensRange) coneEquality

noncomputable def canonicalNegativeRaySumRankLocalIso [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin (Module.finrank ℤ Lattice)) ℤ Lattice)
    (index : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).Index) :
    let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)
    (fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice)).over
      (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange ≅
    (fan.invariantDivisorLineBundle 𝕜 complete regular (-fan.anticanonicalRayDivisor)).obj.over
      (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange := by
  let cone := (Finite.equivFin fan.cones).symm index
  let basis := fan.canonicalDivisorChartRankBasis complete regular cone
  let basisCone := fan.canonicalDivisorChartRankBasis_isConeBasis complete regular cone
  let coordinates := fan.basisConeOrientedCanonicalUnitIso 𝕜 regular reference basis basisCone
  let localCoordinates := BondalThomsen.CanonicalNegativeRaySum.openImmersionUnitOverIso
    (fan.affineToricChartι 𝕜 regular ⟨_, basisCone⟩)
    (fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice)) coordinates
  exact BondalThomsen.CanonicalGlobalRaySum.restrictLocalModuleIso
    (fan.canonicalDivisorChartRankBasis_chart 𝕜 complete regular cone).symm.le localCoordinates ≪≫
      fan.invariantDivisorLineBundle_chartTrivialization 𝕜 complete regular
        (-fan.anticanonicalRayDivisor) index

end TauCeti.Toric.Fan

namespace BondalThomsen.CanonicalNegativeRaySumGlobal

theorem affineChartCoordinate_restriction {SchemeModel : Scheme}
    (CoordinateRing : CommRingCat) (inclusion : Spec CoordinateRing ⟶ SchemeModel)
    [IsOpenImmersion inclusion] (domain : (Spec CoordinateRing).Opens)
    (coordinate : CoordinateRing) :
    SchemeModel.presheaf.map (homOfLE
      ((inclusion.opensFunctor.map domain.leTop).le.trans inclusion.image_top_eq_opensRange.le)).op
      ((IsOpenImmersion.ΓIsoTop inclusion).hom
        ((Scheme.ΓSpecIso CoordinateRing).inv coordinate)) =
    (inclusion.appIso domain).inv
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, domain) coordinate) := by
  have naturality := ConcreteCategory.congr_hom
    (inclusion.appIso_inv_naturality domain.leTop.op)
    ((Scheme.ΓSpecIso CoordinateRing).inv coordinate)
  have affineRestriction : (Spec CoordinateRing).presheaf.map domain.leTop.op
      ((Scheme.ΓSpecIso CoordinateRing).inv coordinate) =
      algebraMap CoordinateRing Γ(Spec CoordinateRing, domain) coordinate := by
    rw [Scheme.ΓSpecIso_inv]
    exact ConcreteCategory.congr_hom
      (StructureSheaf.algebraMap_self_map (R := CoordinateRing) (op domain) (op ⊤)
        domain.leTop.op) coordinate
  refine Eq.trans ?_ ((congrArg (inclusion.appIso domain).inv affineRestriction).symm.trans
    naturality).symm
  change SchemeModel.presheaf.map _ (SchemeModel.presheaf.map _
      ((inclusion.appIso ⊤).inv ((Scheme.ΓSpecIso CoordinateRing).inv coordinate))) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end BondalThomsen.CanonicalNegativeRaySumGlobal

namespace TauCeti.Toric.Fan.CharacterEquationAtlas

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {fan : Fan embedding} {regular : fan.IsRegular}

theorem transition_principalOpen (atlas : CharacterEquationAtlas 𝕜 fan regular)
    (first second : atlas.Index)
    (denominator : affineCoordinateRing 𝕜 fan.lattice (atlas.cone first ⊓ atlas.cone second).val) :
    let face := atlas.cone first ⊓ atlas.cone second
    let domain := PrimeSpectrum.basicOpen denominator
    let contained := ((fan.affineToricChartι 𝕜 regular face).opensFunctor.map domain.leTop).le.trans
      ((fan.affineToricChartι 𝕜 regular face).image_top_eq_opensRange.le.trans
        (fan.chart_opensRange_intersection 𝕜 regular (atlas.cone first) (atlas.cone second)).le)
    (fan.algebraicRealization 𝕜 regular).presheaf.map (homOfLE contained).op
      (atlas.transition 𝕜 first second : Γ(fan.algebraicRealization 𝕜 regular,
        (fan.affineToricChartι 𝕜 regular (atlas.cone first)).opensRange ⊓
          (fan.affineToricChartι 𝕜 regular (atlas.cone second)).opensRange)) =
    ((fan.affineToricChartι 𝕜 regular face).appIso domain).inv
      (BondalThomsen.CanonicalRaySumSheaf.affineRegularSection
        (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face.val)) denominator
        (toricMonomialUnit 𝕜 fan.lattice face.val (atlas.character first - atlas.character second)
          (atlas.positive first second) (atlas.negative first second))) := by
  dsimp only
  have restriction := BondalThomsen.CanonicalNegativeRaySumGlobal.affineChartCoordinate_restriction
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice (atlas.cone first ⊓ atlas.cone second).val))
    (fan.affineToricChartι 𝕜 regular (atlas.cone first ⊓ atlas.cone second))
    (PrimeSpectrum.basicOpen denominator)
    (toricMonomialUnit 𝕜 fan.lattice (atlas.cone first ⊓ atlas.cone second).val
      (atlas.character first - atlas.character second) (atlas.positive first second)
      (atlas.negative first second))
  refine Eq.trans ?_ restriction
  change (fan.algebraicRealization 𝕜 regular).presheaf.map _
    ((fan.algebraicRealization 𝕜 regular).presheaf.map _ _) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end TauCeti.Toric.Fan.CharacterEquationAtlas

namespace BondalThomsen.CanonicalNegativeRaySumGlobal

theorem unitOverHom_ext_top {SchemeModel : Scheme} (chart : SchemeModel.Opens)
    (target : SchemeModel.Modules)
    (first second : (SheafOfModules.unit SchemeModel.ringCatSheaf).over chart ⟶ target.over chart)
    (top_eq : first.val.app (op (Over.mk (𝟙 chart))) (1 : Γ(SchemeModel, chart)) =
      second.val.app (op (Over.mk (𝟙 chart))) (1 : Γ(SchemeModel, chart))) :
    first = second := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext domain
  apply ModuleCat.hom_ext
  ext
  cases domain with
  | op domain =>
    have firstNatural := PresheafOfModules.naturality_apply first.val
      (Over.homMk domain.hom : domain ⟶ Over.mk (𝟙 chart)).op (1 : Γ(SchemeModel, chart))
    have secondNatural := PresheafOfModules.naturality_apply second.val
      (Over.homMk domain.hom : domain ⟶ Over.mk (𝟙 chart)).op (1 : Γ(SchemeModel, chart))
    have restrictedOne : ((SheafOfModules.unit SchemeModel.ringCatSheaf).over chart).val.map
        (Over.homMk domain.hom : domain ⟶ Over.mk (𝟙 chart)).op (1 : Γ(SchemeModel, chart)) =
        (1 : Γ(SchemeModel, domain.left)) := map_one (SchemeModel.presheaf.map domain.hom.op).hom
    have one_eq := (congrArg (first.val.app (op domain)) restrictedOne.symm).trans
      (firstNatural.trans ((congrArg ((target.over chart).val.map
        (Over.homMk domain.hom : domain ⟶ Over.mk (𝟙 chart)).op) top_eq).trans
        (secondNatural.symm.trans (congrArg (second.val.app (op domain)) restrictedOne))))
    exact one_eq

theorem localHom_ext_frame {SchemeModel : Scheme} (chart : SchemeModel.Opens)
    (source target : SchemeModel.Modules)
    (coordinates : source.over chart ≅ (SheafOfModules.unit SchemeModel.ringCatSheaf).over chart)
    (frame : source.val.obj (op chart))
    (coordinate_one : coordinates.hom.val.app (op (Over.mk (𝟙 chart))) frame =
      (1 : Γ(SchemeModel, chart)))
    (first second : source.over chart ⟶ target.over chart)
    (frame_eq : first.val.app (op (Over.mk (𝟙 chart))) frame =
      second.val.app (op (Over.mk (𝟙 chart))) frame) : first = second := by
  apply (cancel_epi coordinates.inv).mp
  apply unitOverHom_ext_top chart target
  have inverseFrame : coordinates.inv.val.app (op (Over.mk (𝟙 chart))) (1 : Γ(SchemeModel, chart)) =
      frame := by
    have inverseIdentity := congrArg (fun morphism =>
      morphism.val.app (op (Over.mk (𝟙 chart))) frame) coordinates.hom_inv_id
    exact (congrArg (coordinates.inv.val.app (op (Over.mk (𝟙 chart)))) coordinate_one.symm).trans
      inverseIdentity
  exact (congrArg (first.val.app (op (Over.mk (𝟙 chart)))) inverseFrame).trans
    (frame_eq.trans (congrArg (second.val.app (op (Over.mk (𝟙 chart)))) inverseFrame.symm))

end BondalThomsen.CanonicalNegativeRaySumGlobal
