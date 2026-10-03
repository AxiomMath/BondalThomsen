module

public import BondalThomsen.Toric.Canonical.GlobalRaySumIso
public import BondalThomsen.Toric.Canonical.Invertible

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CanonicalNegativeRaySum

noncomputable def canonicalStructureIso {SchemeModel Base : Scheme}
    {first second : SchemeModel ⟶ Base} (structure_eq : first = second) (degree : ℕ) :
    canonicalExteriorSheaf first degree ≅ canonicalExteriorSheaf second degree := by
  cases structure_eq
  exact Iso.refl _

theorem canonicalStructureIso_inv_differentialTopSection {SchemeModel Base : Scheme}
    {first second : SchemeModel ⟶ Base} (structure_eq : first = second) (degree : ℕ)
    (domain : SchemeModel.Opens) (coordinates : Fin degree → Γ(SchemeModel, domain)) :
    (canonicalStructureIso structure_eq degree).inv.val.app (op domain)
        (CanonicalRaySumSheaf.differentialTopSection second degree domain coordinates) =
      CanonicalRaySumSheaf.differentialTopSection first degree domain coordinates := by
  cases structure_eq
  rfl

noncomputable def canonicalChartIso {Chart SchemeModel Base : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Base) (chartStructure : Chart ⟶ Base)
    (structure_eq : inclusion ≫ structureMap = chartStructure) (degree : ℕ) :
    (canonicalExteriorSheaf structureMap degree).restrict inclusion ≅
      canonicalExteriorSheaf chartStructure degree :=
  CanonicalFanChart.canonicalExteriorRestrictionIso inclusion structureMap degree ≪≫
    canonicalStructureIso structure_eq degree

theorem canonicalChartIso_inv_differentialTopSection {Chart SchemeModel Base : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Base) (chartStructure : Chart ⟶ Base)
    (structure_eq : inclusion ≫ structureMap = chartStructure) (degree : ℕ)
    (domain : Chart.Opens) (coordinates : Fin degree → Γ(Chart, domain)) :
    (canonicalChartIso inclusion structureMap chartStructure structure_eq degree).inv.val.app
        (op domain)
        (CanonicalRaySumSheaf.differentialTopSection chartStructure degree domain coordinates) =
      CanonicalGlobalRaySum.chartDifferentialTopSection inclusion structureMap degree domain
        coordinates := by
  have transported := canonicalStructureIso_inv_differentialTopSection structure_eq degree
    domain coordinates
  exact (congrArg
    ((CanonicalFanChart.canonicalExteriorRestrictionIso inclusion structureMap degree).inv.val.app
      (op domain)) transported).trans
    (CanonicalRaySumSheaf.canonicalExteriorRestrictionIso_inv_differentialTopSection
      inclusion structureMap degree domain coordinates)

theorem tildeToBasicOpen_map (CoordinateRing : CommRingCat)
    {source target : ModuleCat CoordinateRing} (morphism : source ⟶ target)
    (denominator : CoordinateRing) (vector : source) :
    (tilde.map morphism).val.app (op (PrimeSpectrum.basicOpen denominator))
        (CanonicalTopExterior.tildeToBasicOpen CoordinateRing source denominator vector) =
      CanonicalTopExterior.tildeToBasicOpen CoordinateRing target denominator (morphism vector) := by
  exact ConcreteCategory.congr_hom
    (tilde.toOpen_map_app morphism (PrimeSpectrum.basicOpen denominator)) vector

theorem tildeToBasicOpen_one (CoordinateRing : CommRingCat) (denominator : CoordinateRing) :
    CanonicalTopExterior.tildeToBasicOpen CoordinateRing (ModuleCat.of CoordinateRing CoordinateRing)
        denominator (1 : CoordinateRing) =
      (1 : Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)) := by
  change algebraMap CoordinateRing Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator) 1 = 1
  exact map_one _

theorem tildeTopTrivialization_frame (CoordinateRing : CommRingCat)
    (modules : ModuleCat CoordinateRing) {degree : ℕ}
    (basis : Basis (Fin degree) CoordinateRing modules) (denominator : CoordinateRing) :
    ((tilde.functor CoordinateRing).mapIso (TopExterior.trivialization basis).toModuleIso).hom.val.app
        (op (PrimeSpectrum.basicOpen denominator))
        (CanonicalExteriorDescent.tildeTopBasis CoordinateRing modules basis denominator 0) =
      (1 : Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)) := by
  have top_frame := CanonicalTopExterior.tildeBasicOpenBasis_apply CoordinateRing
    (CanonicalExteriorDescent.topExteriorModule CoordinateRing modules (dimension := degree))
    (CanonicalExteriorDescent.topExteriorBasis CoordinateRing modules basis) denominator 0
  have frame_vector := CanonicalExteriorDescent.topExteriorBasis_apply CoordinateRing modules basis
  refine (congrArg
    (((tilde.functor CoordinateRing).mapIso (TopExterior.trivialization basis).toModuleIso).hom.val.app
      (op (PrimeSpectrum.basicOpen denominator))) top_frame).trans ?_
  refine (tildeToBasicOpen_map CoordinateRing (TopExterior.trivialization basis).toModuleIso.hom
    denominator _).trans ?_
  exact (congrArg (CanonicalTopExterior.tildeToBasicOpen CoordinateRing
    (ModuleCat.of CoordinateRing CoordinateRing) denominator)
    ((congrArg (TopExterior.trivialization basis) frame_vector).trans
      (TopExterior.trivialization_frame basis))).trans (tildeToBasicOpen_one CoordinateRing denominator)

noncomputable def affineCanonicalUnitIso (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] {degree : ℕ}
    (basis : Basis (Fin degree) CoordinateRing (KaehlerDifferential Base CoordinateRing)) :
    canonicalExteriorSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) degree ≅
      SheafOfModules.unit (Spec CoordinateRing).ringCatSheaf :=
  CanonicalExteriorDescent.canonicalExteriorSpecTildeIso Base CoordinateRing basis ≪≫
    (tilde.functor CoordinateRing).mapIso (TopExterior.trivialization basis).toModuleIso ≪≫ tildeSelf

theorem affineCanonicalUnitIso_coordinateFrame (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] {degree : ℕ}
    (basis : Basis (Fin degree) CoordinateRing (KaehlerDifferential Base CoordinateRing))
    (coordinates : Fin degree → CoordinateRing)
    (coordinate_differentials : ∀ index,
      basis index = KaehlerDifferential.D Base CoordinateRing (coordinates index))
    (denominator : CoordinateRing) :
    (affineCanonicalUnitIso Base CoordinateRing basis).hom.val.app
        (op (PrimeSpectrum.basicOpen denominator))
        (CanonicalRaySumSheaf.affineCoordinateDifferentialTopSection Base CoordinateRing degree
          coordinates denominator) = (1 : Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)) := by
  have compared := CanonicalRaySumSheaf.canonicalExteriorSpecTilde_coordinateFrame
    Base CoordinateRing basis coordinates coordinate_differentials denominator
  exact (congrArg
    (((tilde.functor CoordinateRing).mapIso (TopExterior.trivialization basis).toModuleIso).hom.val.app
      (op (PrimeSpectrum.basicOpen denominator))) compared).trans
    (tildeTopTrivialization_frame CoordinateRing (CanonicalAffine.differentialModule Base CoordinateRing)
      basis denominator)

theorem affineChartTopSection_inv_frame {SchemeModel : Scheme}
    (Base CoordinateRing : CommRingCat) [Algebra Base CoordinateRing]
    (inclusion : Spec CoordinateRing ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Spec Base)
    (structure_eq : inclusion ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
    (degree : ℕ) (denominator : CoordinateRing) (coordinates : Fin degree → CoordinateRing) :
    (canonicalChartIso inclusion structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) structure_eq degree).inv.val.app
      (op (PrimeSpectrum.basicOpen denominator))
      (CanonicalRaySumSheaf.affineCoordinateDifferentialTopSection Base CoordinateRing degree
        coordinates denominator) =
    CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing inclusion structureMap
      degree (PrimeSpectrum.basicOpen denominator) coordinates := by
  exact canonicalChartIso_inv_differentialTopSection inclusion structureMap
    (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) structure_eq degree
    (PrimeSpectrum.basicOpen denominator)
    (fun index => algebraMap CoordinateRing Γ(Spec CoordinateRing,
      PrimeSpectrum.basicOpen denominator) (coordinates index))

noncomputable def globalCanonicalChartUnitIso {SchemeModel : Scheme}
    (Base CoordinateRing : CommRingCat) [Algebra Base CoordinateRing]
    (inclusion : Spec CoordinateRing ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Spec Base)
    (structure_eq : inclusion ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
    {degree : ℕ} (basis : Basis (Fin degree) CoordinateRing
      (KaehlerDifferential Base CoordinateRing)) :
    (canonicalExteriorSheaf structureMap degree).restrict inclusion ≅
      SheafOfModules.unit (Spec CoordinateRing).ringCatSheaf :=
  canonicalChartIso inclusion structureMap
    (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) structure_eq degree ≪≫
      affineCanonicalUnitIso Base CoordinateRing basis

theorem globalCanonicalChartUnitIso_frame {SchemeModel : Scheme}
    (Base CoordinateRing : CommRingCat) [Algebra Base CoordinateRing]
    (inclusion : Spec CoordinateRing ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Spec Base)
    (structure_eq : inclusion ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
    {degree : ℕ} (basis : Basis (Fin degree) CoordinateRing
      (KaehlerDifferential Base CoordinateRing))
    (coordinates : Fin degree → CoordinateRing)
    (coordinate_differentials : ∀ index,
      basis index = KaehlerDifferential.D Base CoordinateRing (coordinates index))
    (denominator : CoordinateRing) :
    (globalCanonicalChartUnitIso Base CoordinateRing inclusion structureMap structure_eq basis).hom.val.app
      (op (PrimeSpectrum.basicOpen denominator))
      (CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing inclusion structureMap
        degree (PrimeSpectrum.basicOpen denominator) coordinates) =
    (1 : Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)) := by
  let comparison := canonicalChartIso inclusion structureMap
    (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) structure_eq degree
  have frame := affineChartTopSection_inv_frame Base CoordinateRing inclusion structureMap structure_eq
    degree denominator coordinates
  have compared : comparison.hom.val.app (op (PrimeSpectrum.basicOpen denominator))
      (CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing inclusion structureMap
        degree (PrimeSpectrum.basicOpen denominator) coordinates) =
      CanonicalRaySumSheaf.affineCoordinateDifferentialTopSection Base CoordinateRing degree
        coordinates denominator := by
    refine (congrArg (comparison.hom.val.app (op (PrimeSpectrum.basicOpen denominator))) frame.symm).trans ?_
    exact congrArg (fun morphism => morphism.val.app (op (PrimeSpectrum.basicOpen denominator))
      (CanonicalRaySumSheaf.affineCoordinateDifferentialTopSection Base CoordinateRing degree
        coordinates denominator)) comparison.inv_hom_id
  exact (congrArg ((affineCanonicalUnitIso Base CoordinateRing basis).hom.val.app
    (op (PrimeSpectrum.basicOpen denominator))) compared).trans
    (affineCanonicalUnitIso_coordinateFrame Base CoordinateRing basis coordinates
      coordinate_differentials denominator)

end BondalThomsen.CanonicalNegativeRaySum

namespace BondalThomsen.CanonicalNegativeRaySum

theorem affineChartTopSection_congr {SchemeModel Base : Scheme}
    (CoordinateRing : CommRingCat)
    {first second : Spec CoordinateRing ⟶ SchemeModel}
    [IsOpenImmersion first] [IsOpenImmersion second] (inclusion_eq : first = second)
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ)
    (domain : (Spec CoordinateRing).Opens) (coordinates : Fin degree → CoordinateRing) :
    (canonicalExteriorSheaf structureMap degree).val.map (eqToHom (show
      second.opensFunctor.obj domain = first.opensFunctor.obj domain by cases inclusion_eq; rfl)).op
      (CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing first structureMap
        degree domain coordinates) =
      CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing second structureMap
        degree domain coordinates := by
  cases inclusion_eq
  change (canonicalExteriorSheaf structureMap degree).val.map (𝟙 _)
    (CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing first structureMap
      degree domain coordinates) = _
  exact ConcreteCategory.congr_hom ((canonicalExteriorSheaf structureMap degree).val.map_id _) _

end BondalThomsen.CanonicalNegativeRaySum

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def canonicalOrientationUnit (fan : Fan embedding)
    (reference basis : Basis (Fin dimension) ℤ Lattice) : ℤˣ :=
  (BondalThomsen.CanonicalRaySum.integralDeterminantUnit
    (fan.canonicalCharacterBasis reference) (fan.canonicalCharacterBasis basis))⁻¹

noncomputable def canonicalRaySumChartIso (fan : Fan embedding)
    (regular : fan.IsRegular) (cone : fan.cones) (dimension : ℕ) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).restrict
        (fan.affineToricChartι 𝕜 regular cone) ≅
      BondalThomsen.canonicalExteriorSheaf (Spec.map (CommRingCat.ofHom
        (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val)))) dimension :=
  BondalThomsen.CanonicalNegativeRaySum.canonicalChartIso (fan.affineToricChartι 𝕜 regular cone)
    (fan.structureMap 𝕜 regular) _ (fan.chartι_comp_structureMap 𝕜 regular cone) dimension

theorem canonicalRaySumChartIso_inv_frame (fan : Fan embedding)
    (regular : fan.IsRegular) (cone : fan.cones) (dimension : ℕ)
    (denominator : affineCoordinateRing 𝕜 fan.lattice cone.val)
    (coordinates : Fin dimension → affineCoordinateRing 𝕜 fan.lattice cone.val) :
    (fan.canonicalRaySumChartIso 𝕜 regular cone dimension).inv.val.app
      (op (PrimeSpectrum.basicOpen denominator))
      (BondalThomsen.CanonicalRaySumSheaf.affineCoordinateDifferentialTopSection (CommRingCat.of 𝕜)
        (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val)) dimension coordinates denominator) =
      fan.chartGlobalDifferentialTopSection 𝕜 regular cone dimension
        (PrimeSpectrum.basicOpen denominator) coordinates :=
  BondalThomsen.CanonicalNegativeRaySum.affineChartTopSection_inv_frame (CommRingCat.of 𝕜)
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val))
    (fan.affineToricChartι 𝕜 regular cone) (fan.structureMap 𝕜 regular)
    (fan.chartι_comp_structureMap 𝕜 regular cone) dimension denominator coordinates

end TauCeti.Toric.Fan

namespace BondalThomsen.CanonicalNegativeRaySum

noncomputable def unitIntegralAutomorphism (SchemeModel : Scheme) (scalar : ℤˣ) :
    SheafOfModules.unit SchemeModel.ringCatSheaf ≅
      SheafOfModules.unit SchemeModel.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget SchemeModel.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun domain =>
      (LinearEquiv.smulOfUnit (M := Γ(SchemeModel, unop domain))
        (Units.map (Int.castRingHom Γ(SchemeModel, unop domain)).toMonoidHom scalar)).toModuleIso)
      (by
        intro first second inclusion
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro value
        change Γ(SchemeModel, unop first) at value
        change ((scalar : ℤ) : Γ(SchemeModel, unop second)) *
            SchemeModel.presheaf.map inclusion value =
          SchemeModel.presheaf.map inclusion (((scalar : ℤ) : Γ(SchemeModel, unop first)) * value)
        simp only [map_mul, map_intCast]))

noncomputable def openImmersionUnitOverIso {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (modules : SchemeModel.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Chart.ringCatSheaf) :
    modules.over inclusion.opensRange ≅
      (SheafOfModules.unit SchemeModel.ringCatSheaf).over inclusion.opensRange := by
  let comparison : (SheafOfModules.unit SchemeModel.ringCatSheaf).over inclusion.opensRange ≅
      modules.over inclusion.opensRange :=
    (Scheme.Modules.overEquiv inclusion.opensRange).fullyFaithfulFunctor.preimageIso
      (CanonicalInvertible.openImmersionUnitRestrictionIso inclusion modules coordinates ≪≫
        ((Scheme.Modules.overFunctorEquiv inclusion.opensRange).app modules).symm)
  exact comparison.symm

theorem unitIntegralAutomorphism_hom_apply (SchemeModel : Scheme) (scalar : ℤˣ)
    (domain : SchemeModel.Opens) (value : Γ(SchemeModel, domain)) :
    (unitIntegralAutomorphism SchemeModel scalar).hom.val.app (op domain) value =
      (((scalar : ℤ) : Γ(SchemeModel, domain)) * value) := rfl

noncomputable def orientedGlobalCanonicalChartUnitIso {SchemeModel : Scheme}
    (Base CoordinateRing : CommRingCat) [Algebra Base CoordinateRing]
    (inclusion : Spec CoordinateRing ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Spec Base)
    (structure_eq : inclusion ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
    {degree : ℕ} (basis : Basis (Fin degree) CoordinateRing
      (KaehlerDifferential Base CoordinateRing)) (orientation : ℤˣ) :
    (canonicalExteriorSheaf structureMap degree).restrict inclusion ≅
      SheafOfModules.unit (Spec CoordinateRing).ringCatSheaf :=
  globalCanonicalChartUnitIso Base CoordinateRing inclusion structureMap structure_eq basis ≪≫
    unitIntegralAutomorphism (Spec CoordinateRing) orientation⁻¹

theorem orientedGlobalCanonicalChartUnitIso_frame {SchemeModel : Scheme}
    (Base CoordinateRing : CommRingCat) [Algebra Base CoordinateRing]
    (inclusion : Spec CoordinateRing ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Spec Base)
    (structure_eq : inclusion ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))
    {degree : ℕ} (basis : Basis (Fin degree) CoordinateRing
      (KaehlerDifferential Base CoordinateRing)) (orientation : ℤˣ)
    (coordinates : Fin degree → CoordinateRing)
    (coordinate_differentials : ∀ index,
      basis index = KaehlerDifferential.D Base CoordinateRing (coordinates index))
    (denominator : CoordinateRing) :
    (orientedGlobalCanonicalChartUnitIso Base CoordinateRing inclusion structureMap structure_eq
      basis orientation).hom.val.app (op (PrimeSpectrum.basicOpen denominator))
      ((orientation : ℤ) • CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing
        inclusion structureMap degree (PrimeSpectrum.basicOpen denominator) coordinates) =
      (1 : Γ(Spec CoordinateRing, PrimeSpectrum.basicOpen denominator)) := by
  let domain := PrimeSpectrum.basicOpen denominator
  let coordinatesIso := globalCanonicalChartUnitIso Base CoordinateRing inclusion structureMap
    structure_eq basis
  have coordinateFrame := globalCanonicalChartUnitIso_frame Base CoordinateRing inclusion
    structureMap structure_eq basis coordinates coordinate_differentials denominator
  change (unitIntegralAutomorphism (Spec CoordinateRing) orientation⁻¹).hom.val.app (op domain)
    (coordinatesIso.hom.val.app (op domain) ((orientation : ℤ) •
      CanonicalGlobalRaySum.affineChartDifferentialTopSection CoordinateRing inclusion structureMap
        degree domain coordinates)) = _
  have normalized := (map_zsmul (coordinatesIso.hom.val.app (op domain)).hom (orientation : ℤ)
    _).trans (congrArg (fun value : Γ(Spec CoordinateRing, domain) => (orientation : ℤ) • value)
      coordinateFrame)
  refine (congrArg ((unitIntegralAutomorphism (Spec CoordinateRing) orientation⁻¹).hom.val.app
    (op domain)) normalized).trans ?_
  rw [unitIntegralAutomorphism_hom_apply, ← Int.cast_smul_eq_zsmul
    Γ(Spec CoordinateRing, domain), smul_eq_mul, mul_one]
  change (((orientation⁻¹ : ℤˣ) : ℤ) : Γ(Spec CoordinateRing, domain)) *
    ((orientation : ℤ) : Γ(Spec CoordinateRing, domain)) =
      (1 : Γ(Spec CoordinateRing, domain))
  exact (map_mul (Int.castRingHom Γ(Spec CoordinateRing, domain)) orientation.inv
    (orientation : ℤ)).symm.trans
      ((congrArg (Int.castRingHom Γ(Spec CoordinateRing, domain)) orientation.inv_val).trans
        (map_one _))

end BondalThomsen.CanonicalNegativeRaySum

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def basisConeOrientedCanonicalUnitIso (fan : Fan embedding)
    (regular : fan.IsRegular) (reference basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).restrict
      (fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩) ≅
    SheafOfModules.unit (affineToricScheme 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))).ringCatSheaf :=
  BondalThomsen.CanonicalNegativeRaySum.orientedGlobalCanonicalChartUnitIso (CommRingCat.of 𝕜)
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))))
    (fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩) (fan.structureMap 𝕜 regular)
    (fan.chartι_comp_structureMap 𝕜 regular ⟨_, cone_basis⟩)
    (fan.basisConeDifferentialBasis 𝕜 basis) (fan.canonicalOrientationUnit reference basis)

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def canonicalFaceChartRestriction (fan : Fan embedding)
    (regular : fan.IsRegular) {face cone : fan.cones} (face_of : face.val.IsFaceOf cone.val)
    (degree : ℕ) (domain : (affineToricScheme 𝕜 fan.lattice face.val).Opens)
    (sectionValue : (fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.obj
      (op ((fan.affineToricChartι 𝕜 regular cone).opensFunctor.obj ⊤))) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.obj
      (op ((fan.affineToricChartι 𝕜 regular face).opensFunctor.obj domain)) := by
  letI : IsOpenImmersion (faceAffineToricSchemeMap 𝕜 fan.lattice face_of) :=
    (regular cone.property).isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _
  let refinement := faceAffineToricSchemeMap 𝕜 fan.lattice face_of
  let inclusion := fan.affineToricChartι 𝕜 regular cone
  let composite := refinement ≫ inclusion
  let inclusion_eq := fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 regular face_of
  exact (fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.map
    (eqToHom (show (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj domain =
      composite.opensFunctor.obj domain by
        simp only [composite, refinement, inclusion, inclusion_eq])).op
    ((fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.map
      (eqToHom (Scheme.Hom.comp_image refinement inclusion domain)).op
      ((fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.map
        (inclusion.opensFunctor.map (homOfLE
          (le_top : refinement.opensFunctor.obj domain ≤ ⊤))).op sectionValue))

theorem canonicalFaceChartRestriction_coordinateSection (fan : Fan embedding)
    (regular : fan.IsRegular) {face cone : fan.cones} (face_of : face.val.IsFaceOf cone.val)
    (degree : ℕ) (domain : (affineToricScheme 𝕜 fan.lattice face.val).Opens)
    (coordinates : Fin degree → affineCoordinateRing 𝕜 fan.lattice cone.val) :
    fan.canonicalFaceChartRestriction 𝕜 regular face_of degree domain
      (fan.chartGlobalDifferentialTopSection 𝕜 regular cone degree ⊤ coordinates) =
    fan.chartGlobalDifferentialTopSection 𝕜 regular face degree domain
      (fun index => faceAffineCoordinateRingMap 𝕜 fan.lattice face_of (coordinates index)) := by
  let : IsOpenImmersion (faceAffineToricSchemeMap 𝕜 fan.lattice face_of) :=
    (regular cone.property).isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _
  let inclusion_eq := fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 regular face_of
  have refined := fan.chartGlobalDifferentialTopSection_face 𝕜 regular face_of degree domain coordinates
  refine (congrArg ((fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.map
    (eqToHom (show (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj domain =
      (faceAffineToricSchemeMap 𝕜 fan.lattice face_of ≫ fan.affineToricChartι 𝕜 regular cone).opensFunctor.obj
        domain by simp only [inclusion_eq])).op) refined).trans ?_
  exact BondalThomsen.CanonicalNegativeRaySum.affineChartTopSection_congr
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face.val)) inclusion_eq
    (fan.structureMap 𝕜 regular) degree domain _

theorem canonicalFaceChartLE (fan : Fan embedding) (regular : fan.IsRegular)
    {face cone : fan.cones} (face_of : face.val.IsFaceOf cone.val)
    (domain : (affineToricScheme 𝕜 fan.lattice face.val).Opens) :
    (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj domain ≤
      (fan.affineToricChartι 𝕜 regular cone).opensFunctor.obj ⊤ := by
  let : IsOpenImmersion (faceAffineToricSchemeMap 𝕜 fan.lattice face_of) :=
    (regular cone.property).isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _
  have contained := (fan.affineToricChartι 𝕜 regular cone).opensFunctor.map
    (homOfLE (le_top : (faceAffineToricSchemeMap 𝕜 fan.lattice face_of).opensFunctor.obj domain ≤ ⊤)) |>.le
  have image_eq := Scheme.Hom.comp_image (faceAffineToricSchemeMap 𝕜 fan.lattice face_of)
    (fan.affineToricChartι 𝕜 regular cone) domain
  have face_eq := fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 regular face_of
  have source_eq : (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj domain =
      (fan.affineToricChartι 𝕜 regular cone).opensFunctor.obj
        ((faceAffineToricSchemeMap 𝕜 fan.lattice face_of).opensFunctor.obj domain) := by
    simpa only [face_eq] using image_eq
  exact source_eq.le.trans contained

theorem canonicalFaceChartRestriction_eq_map (fan : Fan embedding)
    (regular : fan.IsRegular) {face cone : fan.cones} (face_of : face.val.IsFaceOf cone.val)
    (degree : ℕ) (domain : (affineToricScheme 𝕜 fan.lattice face.val).Opens)
    (sectionValue : (fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.obj
      (op ((fan.affineToricChartι 𝕜 regular cone).opensFunctor.obj ⊤))) :
    fan.canonicalFaceChartRestriction 𝕜 regular face_of degree domain sectionValue =
      (fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.map
        (homOfLE (fan.canonicalFaceChartLE 𝕜 regular face_of domain)).op sectionValue := by
  unfold canonicalFaceChartRestriction
  change (fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.presheaf.map _
    ((fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.presheaf.map _
      ((fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.presheaf.map _ sectionValue)) =
    (fan.toricCanonicalExteriorSheaf 𝕜 regular degree).val.presheaf.map _ sectionValue
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

theorem canonicalOrientedFaceDifferentialSheafFrame_eq_smul (fan : Fan embedding)
    (reference basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face) :
    fan.canonicalOrientedFaceDifferentialSheafFrame 𝕜 reference basis face_of denominator =
      BondalThomsen.CanonicalRaySumSheaf.affineRegularSection
        (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face)) denominator
        ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ) •
          fan.canonicalFaceDifferentialSheafFrame 𝕜 basis face_of denominator := by
  unfold canonicalOrientedFaceDifferentialSheafFrame canonicalOrientedFaceCoordinateWedge
  rw [← map_inv]
  change BondalThomsen.CanonicalRaySumSheaf.affineTopExteriorSectionMap (CommRingCat.of 𝕜)
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face)) dimension denominator
    (((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ) •
      fan.canonicalFaceCoordinateWedge 𝕜 basis face_of) = _
  exact (BondalThomsen.CanonicalRaySumSheaf.affineTopExteriorSectionMap (CommRingCat.of 𝕜)
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face)) dimension denominator).map_smulₛₗ _ _

end TauCeti.Toric.Fan

namespace BondalThomsen.CanonicalNegativeRaySum

open TauCeti.AlgebraicGeometry.Scheme

noncomputable def cartierAtlasFrame {SchemeModel : Scheme} [IsIntegral SchemeModel]
    (atlas : CartierEquationAtlas SchemeModel) (index : atlas.Index) :
    atlas.invertibleSheaf.obj.val.obj (op (atlas.chart index)) :=
  (atlas.chartTrivialization index).hom.val.app
    (op (Over.mk (𝟙 (atlas.chart index)))) (1 : Γ(SchemeModel, atlas.chart index))

theorem cartierAtlasFrame_rational {SchemeModel : Scheme} [IsIntegral SchemeModel]
    (atlas : CartierEquationAtlas SchemeModel) (index : atlas.Index) :
    letI := atlas.nonempty_chart index
    rationalFunctionsEquiv (atlas.chart index)
      (atlas.cartierDivisor.sheafι.val.app (op (atlas.chart index))
        (cartierAtlasFrame atlas index)) = ((atlas.equation index)⁻¹ : SchemeModel.functionFieldˣ) := by
  let := atlas.nonempty_chart index
  have included := congrArg (fun morphism => morphism.val.app
    (op (Over.mk (𝟙 (atlas.chart index))))
    ((TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor
      SchemeModel (atlas.equation index)).hom.val.app
      (op (atlas.chart index)) (1 : Γ(SchemeModel, atlas.chart index))))
    (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafOverIsoOfRestrictEq_hom_ι
      (principalCartierDivisor SchemeModel (atlas.equation index)) atlas.cartierDivisor
      (atlas.chart index)
      ((principalCartierDivisor_restrict SchemeModel (atlas.equation index)
        (atlas.chart index)).trans (atlas.cartierDivisor_restrict index).symm))
  refine (congrArg (rationalFunctionsEquiv (atlas.chart index)) included).trans ?_
  have principal := TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitToSheafPrincipalCartierDivisor_app
    (atlas.equation index) (atlas.chart index) (1 : Γ(SchemeModel, atlas.chart index))
  refine (congrArg (rationalFunctionsEquiv (atlas.chart index)) principal).trans ?_
  exact (rationalFunctionsEquiv_rationalFunctionsMul_app
    (((atlas.equation index)⁻¹ : SchemeModel.functionFieldˣ) : SchemeModel.functionField)
    (atlas.chart index) _).trans
    ((congrArg (fun scalar : SchemeModel.functionField =>
      (((atlas.equation index)⁻¹ : SchemeModel.functionFieldˣ) : SchemeModel.functionField) * scalar)
      ((rationalFunctionsEquiv_toRationalFunctions_app (atlas.chart index)
        (1 : Γ(SchemeModel, atlas.chart index))).trans (map_one _))).trans (mul_one _))

noncomputable def cartierAtlasFrameRestriction {SchemeModel : Scheme} [IsIntegral SchemeModel]
    (atlas : CartierEquationAtlas SchemeModel) (index : atlas.Index)
    (domain : SchemeModel.Opens) (contained : domain ≤ atlas.chart index) :
    atlas.invertibleSheaf.obj.val.obj (op domain) :=
  atlas.invertibleSheaf.obj.val.map (homOfLE contained).op (cartierAtlasFrame atlas index)

theorem cartierAtlasFrame_restriction_rational {SchemeModel : Scheme} [IsIntegral SchemeModel]
    (atlas : CartierEquationAtlas SchemeModel) (index : atlas.Index)
    (domain : SchemeModel.Opens) [Nonempty domain] (contained : domain ≤ atlas.chart index) :
    rationalFunctionsEquiv domain
      (atlas.cartierDivisor.sheafι.val.app (op domain)
        (cartierAtlasFrameRestriction atlas index domain contained)) =
      ((atlas.equation index)⁻¹ : SchemeModel.functionFieldˣ) := by
  let := atlas.nonempty_chart index
  have naturality := PresheafOfModules.naturality_apply atlas.cartierDivisor.sheafι.val
    (homOfLE contained).op (cartierAtlasFrame atlas index)
  exact (congrArg (rationalFunctionsEquiv domain) naturality).trans
    ((rationalFunctionsEquiv_map (homOfLE contained) _).trans (cartierAtlasFrame_rational atlas index))

theorem cartierAtlasFrame_transition {SchemeModel : Scheme} [IsIntegral SchemeModel]
    (atlas : CartierEquationAtlas SchemeModel) (first second : atlas.Index) :
    cartierAtlasFrameRestriction atlas second (atlas.chart first ⊓ atlas.chart second) inf_le_right =
    (atlas.transition first second : Γ(SchemeModel, atlas.chart first ⊓ atlas.chart second)) •
      cartierAtlasFrameRestriction atlas first (atlas.chart first ⊓ atlas.chart second) inf_le_left := by
  let := atlas.nonempty_chart first
  let := atlas.nonempty_chart second
  let := nonempty_integral_open_intersection (atlas.chart first) (atlas.chart second)
  let domain := atlas.chart first ⊓ atlas.chart second
  apply TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafι_app_injective atlas.cartierDivisor domain
  apply (rationalFunctionsEquiv domain).injective
  have first_value := cartierAtlasFrame_restriction_rational atlas first domain inf_le_left
  have second_value := cartierAtlasFrame_restriction_rational atlas second domain inf_le_right
  have equation := congrArg Units.val (atlas.transition_equation first second)
  change SchemeModel.germToFunctionField domain (atlas.transition first second) *
      (atlas.equation second : SchemeModel.functionField) =
      (atlas.equation first : SchemeModel.functionField) at equation
  change rationalFunctionsEquiv domain
      (atlas.cartierDivisor.sheafι.val.app (op domain)
        (cartierAtlasFrameRestriction atlas second domain inf_le_right)) =
    rationalFunctionsEquiv domain
      (atlas.cartierDivisor.sheafι.val.app (op domain)
        ((atlas.transition first second : Γ(SchemeModel, domain)) •
          cartierAtlasFrameRestriction atlas first domain inf_le_left))
  refine second_value.trans ?_
  refine Eq.trans ?_ ((congrArg (rationalFunctionsEquiv domain)
    ((atlas.cartierDivisor.sheafι.val.app (op domain)).hom.map_smul
      (atlas.transition first second : Γ(SchemeModel, domain))
      (cartierAtlasFrameRestriction atlas first domain inf_le_left))).trans
    ((rationalFunctionsEquiv domain).map_smul _ _)).symm
  refine Eq.trans ?_ (congrArg (fun value : SchemeModel.functionField =>
    (atlas.transition first second : Γ(SchemeModel, domain)) • value) first_value).symm
  change (((atlas.equation second)⁻¹ : SchemeModel.functionFieldˣ) : SchemeModel.functionField) =
    SchemeModel.germToFunctionField domain (atlas.transition first second) *
      (((atlas.equation first)⁻¹ : SchemeModel.functionFieldˣ) : SchemeModel.functionField)
  apply (Units.eq_mul_inv_iff_mul_eq (atlas.equation first)).mpr
  calc
    (((atlas.equation second)⁻¹ : SchemeModel.functionFieldˣ) : SchemeModel.functionField) *
        (atlas.equation first : SchemeModel.functionField) =
      (((atlas.equation second)⁻¹ : SchemeModel.functionFieldˣ) : SchemeModel.functionField) *
        (SchemeModel.germToFunctionField domain (atlas.transition first second) *
          (atlas.equation second : SchemeModel.functionField)) := congrArg _ equation.symm
    _ = SchemeModel.germToFunctionField domain (atlas.transition first second) := by
      rw [mul_left_comm, Units.inv_mul, mul_one]

end BondalThomsen.CanonicalNegativeRaySum

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

theorem canonicalRaySumChartIso_inv_faceFrame (fan : Fan embedding)
    (regular : fan.IsRegular) (basis : Basis (Fin dimension) ℤ Lattice)
    (face : fan.cones) (face_of : face.val.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face.val) :
    (fan.canonicalRaySumChartIso 𝕜 regular face dimension).inv.val.app
      (op (PrimeSpectrum.basicOpen denominator))
      (fan.canonicalFaceDifferentialSheafFrame 𝕜 basis face_of denominator) =
    fan.chartGlobalDifferentialTopSection 𝕜 regular face dimension
      (PrimeSpectrum.basicOpen denominator) (fan.canonicalFaceCoordinate 𝕜 basis face_of) := by
  have frame := fan.canonicalFaceDifferentialSheafFrame_eq 𝕜 basis face_of denominator
  exact (congrArg ((fan.canonicalRaySumChartIso 𝕜 regular face dimension).inv.val.app
    (op (PrimeSpectrum.basicOpen denominator))) frame).trans
    (fan.canonicalRaySumChartIso_inv_frame 𝕜 regular face dimension denominator
      (fan.canonicalFaceCoordinate 𝕜 basis face_of))

noncomputable def globalOrientedFaceCanonicalSection (fan : Fan embedding)
    (regular : fan.IsRegular) (reference basis : Basis (Fin dimension) ℤ Lattice)
    (face : fan.cones) (face_of : face.val.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face.val) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).val.obj
      (op ((fan.affineToricChartι 𝕜 regular face).opensFunctor.obj
        (PrimeSpectrum.basicOpen denominator))) :=
  ((fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).restrictAppIso
    (fan.affineToricChartι 𝕜 regular face) (PrimeSpectrum.basicOpen denominator)).hom
      ((fan.canonicalRaySumChartIso 𝕜 regular face dimension).inv.val.app
        (op (PrimeSpectrum.basicOpen denominator))
        (fan.canonicalOrientedFaceDifferentialSheafFrame 𝕜 reference basis face_of denominator))

theorem globalOrientedOverlapCanonicalSection_transition (fan : Fan embedding)
    (regular : fan.IsRegular) (reference : Basis (Fin dimension) ℤ Lattice)
    (first : Basis (Fin dimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin dimension) ℤ Lattice) (second_cone : fan.IsConeBasis second)
    (denominator : affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
        PointedCone.hull ℝ (Set.range (fun index => embedding (second index))))) :
    let face : fan.cones := ⟨_, fan.inf_mem first_cone second_cone⟩
    let first_face := fan.inf_isFaceOf_left first_cone second_cone
    let second_face := fan.inf_isFaceOf_right first_cone second_cone
    let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face.val)
    let domain := PrimeSpectrum.basicOpen denominator
    let scalar := BondalThomsen.CanonicalRaySumSheaf.affineRegularSection CoordinateRing denominator
      (((fan.coneDivisorTransitionUnit 𝕜 first first_cone second second_cone
        (-fan.anticanonicalRayDivisor))⁻¹ : CoordinateRingˣ) : CoordinateRing)
    (fan.globalOrientedFaceCanonicalSection 𝕜) regular reference second face second_face denominator =
      ((fan.affineToricChartι 𝕜 regular face).appIso domain).inv scalar •
        fan.globalOrientedFaceCanonicalSection 𝕜 regular reference first face first_face denominator := by
  let face : fan.cones := ⟨_, fan.inf_mem first_cone second_cone⟩
  let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face.val)
  let domain := PrimeSpectrum.basicOpen denominator
  let scalar := BondalThomsen.CanonicalRaySumSheaf.affineRegularSection CoordinateRing denominator
    (((fan.coneDivisorTransitionUnit 𝕜 first first_cone second second_cone
      (-fan.anticanonicalRayDivisor))⁻¹ : CoordinateRingˣ) : CoordinateRing)
  let comparison := fan.canonicalRaySumChartIso 𝕜 regular face dimension
  let transport := (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).restrictAppIso
    (fan.affineToricChartι 𝕜 regular face) domain
  have transition := fan.canonicalOverlapOrientedDifferentialSheafFrame_transition 𝕜
    regular reference first first_cone second second_cone denominator
  refine (congrArg (fun sectionValue => transport.hom (comparison.inv.val.app (op domain)
    sectionValue)) transition).trans ?_
  exact (congrArg transport.hom ((comparison.inv.val.app (op domain)).hom.map_smul scalar _)).trans
    (Scheme.Modules.smul_restrictAppIso_hom_apply _ _ _ _ _)

theorem globalOrientedFaceCanonicalSection_eq_zsmul (fan : Fan embedding)
    (regular : fan.IsRegular) (reference basis : Basis (Fin dimension) ℤ Lattice)
    (face : fan.cones) (face_of : face.val.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face.val) :
    fan.globalOrientedFaceCanonicalSection 𝕜 regular reference basis face face_of denominator =
      ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ) •
        fan.chartGlobalDifferentialTopSection 𝕜 regular face dimension
          (PrimeSpectrum.basicOpen denominator) (fan.canonicalFaceCoordinate 𝕜 basis face_of) := by
  let domain := PrimeSpectrum.basicOpen denominator
  let comparison := fan.canonicalRaySumChartIso 𝕜 regular face dimension
  let transport := (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).restrictAppIso
    (fan.affineToricChartι 𝕜 regular face) domain
  have frame := fan.canonicalOrientedFaceDifferentialSheafFrame_eq_smul 𝕜 reference basis face_of
    denominator
  have integralFrame : fan.canonicalOrientedFaceDifferentialSheafFrame 𝕜 reference basis face_of
      denominator = ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ) •
        fan.canonicalFaceDifferentialSheafFrame 𝕜 basis face_of denominator := by
    simpa only [BondalThomsen.CanonicalRaySumSheaf.affineRegularSection, map_intCast,
      Int.cast_smul_eq_zsmul] using frame
  refine (congrArg (fun sectionValue => transport.hom
    (comparison.inv.val.app (op domain) sectionValue)) integralFrame).trans ?_
  refine (congrArg transport.hom (map_zsmul (comparison.inv.val.app (op domain)).hom
    ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ) _)).trans ?_
  refine (map_zsmul transport.hom.hom ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ)
    _).trans ?_
  exact congrArg (fun sectionValue => ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ) •
    transport.hom sectionValue) (fan.canonicalRaySumChartIso_inv_faceFrame 𝕜 regular basis face
      face_of denominator)

noncomputable def basisConeOrientedGlobalCanonicalFrame (fan : Fan embedding)
    (regular : fan.IsRegular) (reference basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).val.obj
      (op ((fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩).opensFunctor.obj ⊤)) :=
  ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ) •
    fan.basisConeGlobalCanonicalFrame 𝕜 regular basis cone_basis

theorem basisConeOrientedGlobalCanonicalFrame_restriction (fan : Fan embedding)
    (regular : fan.IsRegular) (reference basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (face : fan.cones)
    (face_of : face.val.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice face.val) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).val.map
      (homOfLE (fan.canonicalFaceChartLE 𝕜 regular (cone := ⟨_, cone_basis⟩) face_of
        (PrimeSpectrum.basicOpen denominator))).op
      (fan.basisConeOrientedGlobalCanonicalFrame 𝕜 regular reference basis cone_basis) =
    fan.globalOrientedFaceCanonicalSection 𝕜 regular reference basis face face_of denominator := by
  let domain := PrimeSpectrum.basicOpen denominator
  let restriction := (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).val.map
    (homOfLE (fan.canonicalFaceChartLE 𝕜 regular (cone := ⟨_, cone_basis⟩) face_of domain)).op
  have refined := fan.canonicalFaceChartRestriction_coordinateSection 𝕜 regular
    (cone := ⟨_, cone_basis⟩) face_of dimension
    domain (fun index => MonoidAlgebra.single
      (Multiplicative.ofAdd (fan.basisConeDualStep basis index)) (1 : 𝕜))
  have restricted := fan.canonicalFaceChartRestriction_eq_map 𝕜 regular
    (cone := ⟨_, cone_basis⟩) face_of dimension domain
    (fan.basisConeGlobalCanonicalFrame 𝕜 regular basis cone_basis)
  have coordinateFrame : restriction (fan.basisConeGlobalCanonicalFrame 𝕜 regular basis cone_basis) =
      fan.chartGlobalDifferentialTopSection 𝕜 regular face dimension domain
        (fan.canonicalFaceCoordinate 𝕜 basis face_of) := restricted.symm.trans refined
  exact (map_zsmul restriction.hom ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ)
    _).trans ((congrArg (fun sectionValue =>
      ((fan.canonicalOrientationUnit reference basis : ℤˣ) : ℤ) • sectionValue)
      coordinateFrame).trans (fan.globalOrientedFaceCanonicalSection_eq_zsmul 𝕜 regular reference
        basis face face_of denominator).symm)

end TauCeti.Toric.Fan
