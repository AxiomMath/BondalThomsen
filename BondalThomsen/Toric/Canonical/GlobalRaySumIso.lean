module

public import BondalThomsen.Toric.Canonical.RaySumSheafIso
public import BondalThomsen.ProjectiveBundle.GlobalRelativeQuotient

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CanonicalGlobalRaySum

theorem chartCoordinate_restriction {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    {domain smaller : Chart.Opens} (restriction : smaller ⟶ domain)
    (coordinate : Γ(Chart, domain)) :
    SchemeModel.presheaf.map (inclusion.opensFunctor.map restriction).op
        ((inclusion.appIso domain).inv coordinate) =
      (inclusion.appIso smaller).inv (Chart.presheaf.map restriction.op coordinate) := by
  exact (ConcreteCategory.congr_hom
    (inclusion.appIso_inv_naturality restriction.op) coordinate).symm

noncomputable def chartDifferentialTopSection {Chart SchemeModel Base : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ) (domain : Chart.Opens)
    (coordinates : Fin degree → Γ(Chart, domain)) :
    (canonicalExteriorSheaf structureMap degree).val.obj
      (op (inclusion.opensFunctor.obj domain)) :=
  CanonicalRaySumSheaf.differentialTopSection structureMap degree
    (inclusion.opensFunctor.obj domain)
    (fun index => (inclusion.appIso domain).inv (coordinates index))

theorem refinementCoordinate_restriction {Face Chart SchemeModel : Scheme}
    (refinement : Face ⟶ Chart) [IsOpenImmersion refinement]
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (domain : Face.Opens) (coordinate : Γ(Chart, ⊤)) :
    SchemeModel.presheaf.map
        (inclusion.opensFunctor.map (homOfLE (le_top : refinement.opensFunctor.obj domain ≤ ⊤))).op
        ((inclusion.appIso ⊤).inv coordinate) =
      (inclusion.appIso (refinement.opensFunctor.obj domain)).inv
        ((refinement.appIso domain).inv (refinement.appLE ⊤ domain (by simp) coordinate)) := by
  have localized := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_appIso_inv refinement
      (show domain ≤ refinement ⁻¹ᵁ ⊤ by simp)) coordinate
  simp only [ConcreteCategory.comp_apply] at localized
  exact (chartCoordinate_restriction inclusion (homOfLE le_top) coordinate).trans
    (congrArg (inclusion.appIso (refinement.opensFunctor.obj domain)).inv localized.symm)

theorem refinementDifferentialTopSection_restriction {Face Chart SchemeModel Base : Scheme}
    (refinement : Face ⟶ Chart) [IsOpenImmersion refinement]
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ) (domain : Face.Opens)
    (coordinates : Fin degree → Γ(Chart, ⊤)) :
    (canonicalExteriorSheaf structureMap degree).val.map
        (inclusion.opensFunctor.map (homOfLE (le_top : refinement.opensFunctor.obj domain ≤ ⊤))).op
        (chartDifferentialTopSection inclusion structureMap degree ⊤ coordinates) =
      chartDifferentialTopSection inclusion structureMap degree (refinement.opensFunctor.obj domain)
        (fun index => (refinement.appIso domain).inv
          (refinement.appLE ⊤ domain (by simp) (coordinates index))) := by
  refine (CanonicalRaySumSheaf.differentialTopSection_restriction structureMap degree
    (inclusion.opensFunctor.map (homOfLE le_top))
    (fun index => (inclusion.appIso ⊤).inv (coordinates index))).trans ?_
  apply congrArg (CanonicalRaySumSheaf.differentialTopSection structureMap degree
    (inclusion.opensFunctor.obj (refinement.opensFunctor.obj domain)))
  funext index
  exact refinementCoordinate_restriction refinement inclusion domain (coordinates index)

theorem differentialTopSection_eqToHom {SchemeModel Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ)
    {domain smaller : SchemeModel.Opens} (domain_eq : domain = smaller)
    (coordinates : Fin degree → Γ(SchemeModel, domain)) :
    (canonicalExteriorSheaf structureMap degree).val.map (eqToHom domain_eq.symm).op
        (CanonicalRaySumSheaf.differentialTopSection structureMap degree domain coordinates) =
      CanonicalRaySumSheaf.differentialTopSection structureMap degree smaller
        (fun index => SchemeModel.presheaf.map (eqToHom domain_eq.symm).op (coordinates index)) :=
  CanonicalRaySumSheaf.differentialTopSection_restriction structureMap degree
    (eqToHom domain_eq.symm) coordinates

theorem chartCoordinate_comp {Face Chart SchemeModel : Scheme}
    (refinement : Face ⟶ Chart) [IsOpenImmersion refinement]
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (domain : Face.Opens) (coordinate : Γ(Face, domain)) :
    SchemeModel.presheaf.map (eqToHom (show
        (refinement ≫ inclusion).opensFunctor.obj domain =
          inclusion.opensFunctor.obj (refinement.opensFunctor.obj domain) by simp)).op
        ((inclusion.appIso (refinement.opensFunctor.obj domain)).inv
          ((refinement.appIso domain).inv coordinate)) =
      ((refinement ≫ inclusion).appIso domain).inv coordinate := by
  rw [Scheme.Hom.comp_appIso]
  rfl

theorem chartDifferentialTopSection_comp {Face Chart SchemeModel Base : Scheme}
    (refinement : Face ⟶ Chart) [IsOpenImmersion refinement]
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ) (domain : Face.Opens)
    (coordinates : Fin degree → Γ(Face, domain)) :
    (canonicalExteriorSheaf structureMap degree).val.map (eqToHom (show
        (refinement ≫ inclusion).opensFunctor.obj domain =
          inclusion.opensFunctor.obj (refinement.opensFunctor.obj domain) by simp)).op
        (chartDifferentialTopSection inclusion structureMap degree
          (refinement.opensFunctor.obj domain)
          (fun index => (refinement.appIso domain).inv (coordinates index))) =
      chartDifferentialTopSection (refinement ≫ inclusion) structureMap degree domain coordinates := by
  refine (differentialTopSection_eqToHom structureMap degree (by simp)
    (fun index => (inclusion.appIso (refinement.opensFunctor.obj domain)).inv
      ((refinement.appIso domain).inv (coordinates index)))).trans ?_
  apply congrArg (CanonicalRaySumSheaf.differentialTopSection structureMap degree
    ((refinement ≫ inclusion).opensFunctor.obj domain))
  funext index
  exact chartCoordinate_comp refinement inclusion domain (coordinates index)

theorem affineRefinement_coordinate (SourceRing TargetRing : CommRingCat)
    (coefficientMap : SourceRing ⟶ TargetRing) (domain : (Spec TargetRing).Opens)
    (coordinate : SourceRing) :
    (Spec.map coefficientMap).appLE ⊤ domain (by simp)
        ((Scheme.ΓSpecIso SourceRing).inv coordinate) =
      (Spec TargetRing).presheaf.map domain.leTop.op
        ((Scheme.ΓSpecIso TargetRing).inv (coefficientMap coordinate)) := by
  have naturality := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality coefficientMap) coordinate
  change (Scheme.ΓSpecIso TargetRing).inv (coefficientMap coordinate) =
    (Spec.map coefficientMap).appTop ((Scheme.ΓSpecIso SourceRing).inv coordinate) at naturality
  exact (congrArg ((Spec TargetRing).presheaf.map domain.leTop.op) naturality).symm

noncomputable def affineChartDifferentialTopSection {SchemeModel Base : Scheme}
    (CoordinateRing : CommRingCat) (inclusion : Spec CoordinateRing ⟶ SchemeModel)
    [IsOpenImmersion inclusion] (structureMap : SchemeModel ⟶ Base) (degree : ℕ)
    (domain : (Spec CoordinateRing).Opens) (coordinates : Fin degree → CoordinateRing) :
    (canonicalExteriorSheaf structureMap degree).val.obj
      (op (inclusion.opensFunctor.obj domain)) :=
  chartDifferentialTopSection inclusion structureMap degree domain
    (fun index => (Spec CoordinateRing).presheaf.map domain.leTop.op
      ((Scheme.ΓSpecIso CoordinateRing).inv (coordinates index)))

theorem affineChartDifferentialTopSection_refinement {SchemeModel Base : Scheme}
    (SourceRing TargetRing : CommRingCat) (coefficientMap : SourceRing ⟶ TargetRing)
    [IsOpenImmersion (Spec.map coefficientMap)]
    (inclusion : Spec SourceRing ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ) (domain : (Spec TargetRing).Opens)
    (coordinates : Fin degree → SourceRing) :
    (canonicalExteriorSheaf structureMap degree).val.map (eqToHom (show
        (Spec.map coefficientMap ≫ inclusion).opensFunctor.obj domain =
          inclusion.opensFunctor.obj ((Spec.map coefficientMap).opensFunctor.obj domain)
        by simp)).op
      ((canonicalExteriorSheaf structureMap degree).val.map
        (inclusion.opensFunctor.map
          (homOfLE (le_top : (Spec.map coefficientMap).opensFunctor.obj domain ≤ ⊤))).op
        (affineChartDifferentialTopSection SourceRing inclusion structureMap degree ⊤ coordinates)) =
      affineChartDifferentialTopSection TargetRing (Spec.map coefficientMap ≫ inclusion)
        structureMap degree domain (fun index => coefficientMap (coordinates index)) := by
  let sourceCoordinates : Fin degree → Γ(Spec SourceRing, ⊤) :=
    fun index => (Scheme.ΓSpecIso SourceRing).inv (coordinates index)
  have refined := refinementDifferentialTopSection_restriction
    (Spec.map coefficientMap) inclusion structureMap degree domain sourceCoordinates
  change (canonicalExteriorSheaf structureMap degree).val.map _
    ((canonicalExteriorSheaf structureMap degree).val.map _
      (chartDifferentialTopSection inclusion structureMap degree ⊤ sourceCoordinates)) = _
  rw [refined]
  have coordinate_eq :
      (fun index => (Spec.map coefficientMap).appLE ⊤ domain (by simp)
        (sourceCoordinates index)) =
      (fun index => (Spec TargetRing).presheaf.map domain.leTop.op
        ((Scheme.ΓSpecIso TargetRing).inv (coefficientMap (coordinates index)))) := by
    funext index
    exact affineRefinement_coordinate SourceRing TargetRing coefficientMap domain (coordinates index)
  have frame_eq := congrArg
    (fun frameCoordinates => chartDifferentialTopSection inclusion structureMap degree
      ((Spec.map coefficientMap).opensFunctor.obj domain)
      (fun index => ((Spec.map coefficientMap).appIso domain).inv (frameCoordinates index)))
    coordinate_eq
  refine (congrArg ((canonicalExteriorSheaf structureMap degree).val.map
    (eqToHom (show (Spec.map coefficientMap ≫ inclusion).opensFunctor.obj domain =
      inclusion.opensFunctor.obj ((Spec.map coefficientMap).opensFunctor.obj domain) by simp)).op)
    frame_eq).trans ?_
  exact chartDifferentialTopSection_comp (Spec.map coefficientMap) inclusion structureMap degree domain _

end BondalThomsen.CanonicalGlobalRaySum

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def chartGlobalDifferentialTopSection (fan : Fan embedding)
    (regular : fan.IsRegular) (cone : fan.cones) (dimension : ℕ)
    (domain : (affineToricScheme 𝕜 fan.lattice cone.val).Opens)
    (coordinates : Fin dimension → affineCoordinateRing 𝕜 fan.lattice cone.val) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).val.obj
      (op ((fan.affineToricChartι 𝕜 regular cone).opensFunctor.obj domain)) :=
  BondalThomsen.CanonicalGlobalRaySum.affineChartDifferentialTopSection
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val))
    (fan.affineToricChartι 𝕜 regular cone) (fan.structureMap 𝕜 regular) dimension
    domain coordinates

theorem chartGlobalDifferentialTopSection_face (fan : Fan embedding)
    (regular : fan.IsRegular) {face cone : fan.cones} (face_of : face.val.IsFaceOf cone.val)
    (dimension : ℕ) (domain : (affineToricScheme 𝕜 fan.lattice face.val).Opens)
    (coordinates : Fin dimension → affineCoordinateRing 𝕜 fan.lattice cone.val) :
    letI : IsOpenImmersion (faceAffineToricSchemeMap 𝕜 fan.lattice face_of) :=
      (regular cone.property).isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _
    let refinement := faceAffineToricSchemeMap 𝕜 fan.lattice face_of
    let inclusion := fan.affineToricChartι 𝕜 regular cone
    let composite := refinement ≫ inclusion
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).val.map
      (eqToHom (show composite.opensFunctor.obj domain =
        inclusion.opensFunctor.obj (refinement.opensFunctor.obj domain) from
          Scheme.Hom.comp_image refinement inclusion domain)).op
      ((fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).val.map
        (inclusion.opensFunctor.map (homOfLE
          (le_top : refinement.opensFunctor.obj domain ≤ ⊤))).op
        (fan.chartGlobalDifferentialTopSection 𝕜 regular cone dimension ⊤ coordinates)) =
      BondalThomsen.CanonicalGlobalRaySum.affineChartDifferentialTopSection
        (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face.val)) composite
        (fan.structureMap 𝕜 regular) dimension domain
        (fun index => faceAffineCoordinateRingMap 𝕜 fan.lattice face_of (coordinates index)) := by
  let : IsOpenImmersion (faceAffineToricSchemeMap 𝕜 fan.lattice face_of) :=
    (regular cone.property).isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _
  let : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of).toRingHom)) :=
    inferInstanceAs (IsOpenImmersion (faceAffineToricSchemeMap 𝕜 fan.lattice face_of))
  exact BondalThomsen.CanonicalGlobalRaySum.affineChartDifferentialTopSection_refinement
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val))
    (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice face.val))
    (CommRingCat.ofHom (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of).toRingHom)
    (fan.affineToricChartι 𝕜 regular cone) (fan.structureMap 𝕜 regular) dimension domain coordinates

noncomputable def basisConeGlobalCanonicalFrame (fan : Fan embedding)
    (regular : fan.IsRegular) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).val.obj
      (op ((fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩).opensFunctor.obj ⊤)) :=
  fan.chartGlobalDifferentialTopSection 𝕜 regular ⟨_, cone_basis⟩ dimension ⊤
    (fun index => MonoidAlgebra.single
      (Multiplicative.ofAdd (fan.basisConeDualStep basis index)) (1 : 𝕜))

end TauCeti.Toric.Fan

namespace BondalThomsen.CanonicalGlobalRaySum

noncomputable def restrictLocalModuleIso {SchemeModel : Scheme}
    {source target : SchemeModel.Modules} {smaller larger : SchemeModel.Opens}
    (contained : smaller ≤ larger) (comparison : source.over larger ≅ target.over larger) :
    source.over smaller ≅ target.over smaller :=
  ((SheafOfModules.overFunctorMap SchemeModel.ringCatSheaf
    (homOfLE contained)).app source).symm ≪≫
    (SheafOfModules.overMap SchemeModel.ringCatSheaf (homOfLE contained)).mapIso comparison ≪≫
    (SheafOfModules.overFunctorMap SchemeModel.ringCatSheaf (homOfLE contained)).app target

theorem localModuleIso_inverse_compatible {SchemeModel : Scheme}
    {source target : SchemeModel.Modules} {Index : Type}
    (charts : Index → SchemeModel.Opens)
    (localIso : ∀ index, source.over (charts index) ≅ target.over (charts index))
    (compatible : ∀ first second,
      restrictLocalModuleHom (inf_le_left : charts first ⊓ charts second ≤ charts first)
          (localIso first).hom =
        restrictLocalModuleHom (inf_le_right : charts first ⊓ charts second ≤ charts second)
          (localIso second).hom) :
    ∀ first second,
      restrictLocalModuleHom (inf_le_left : charts first ⊓ charts second ≤ charts first)
          (localIso first).inv =
        restrictLocalModuleHom (inf_le_right : charts first ⊓ charts second ≤ charts second)
          (localIso second).inv := by
  intro first second
  exact (Iso.inv_eq_inv
    (restrictLocalModuleIso (inf_le_left : charts first ⊓ charts second ≤ charts first)
      (localIso first))
    (restrictLocalModuleIso (inf_le_right : charts first ⊓ charts second ≤ charts second)
      (localIso second))).mpr (compatible first second)

noncomputable def glueLocalModuleIso {SchemeModel : Scheme}
    {source target : SchemeModel.Modules} {Index : Type}
    (charts : Index → SchemeModel.Opens) (covers : IsOpenCover charts)
    (localIso : ∀ index, source.over (charts index) ≅ target.over (charts index))
    (compatible : ∀ first second,
      restrictLocalModuleHom (inf_le_left : charts first ⊓ charts second ≤ charts first)
          (localIso first).hom =
        restrictLocalModuleHom (inf_le_right : charts first ⊓ charts second ≤ charts second)
          (localIso second).hom) : source ≅ target where
  hom := LocalModuleGluing.glue charts covers (fun index => (localIso index).hom) compatible
  inv := LocalModuleGluing.glue charts covers (fun index => (localIso index).inv)
    (localModuleIso_inverse_compatible charts localIso compatible)
  hom_inv_id := by
    apply LocalModuleGluing.hom_ext charts covers
    intro index
    change (LocalModuleGluing.glue charts covers (fun index => (localIso index).hom)
        compatible).over (charts index) ≫
      (LocalModuleGluing.glue charts covers (fun index => (localIso index).inv)
        (localModuleIso_inverse_compatible charts localIso compatible)).over (charts index) = 𝟙 _
    rw [LocalModuleGluing.glue_over, LocalModuleGluing.glue_over]
    exact (localIso index).hom_inv_id
  inv_hom_id := by
    apply LocalModuleGluing.hom_ext charts covers
    intro index
    change (LocalModuleGluing.glue charts covers (fun index => (localIso index).inv)
        (localModuleIso_inverse_compatible charts localIso compatible)).over (charts index) ≫
      (LocalModuleGluing.glue charts covers (fun index => (localIso index).hom)
        compatible).over (charts index) = 𝟙 _
    rw [LocalModuleGluing.glue_over, LocalModuleGluing.glue_over]
    exact (localIso index).inv_hom_id

end BondalThomsen.CanonicalGlobalRaySum
