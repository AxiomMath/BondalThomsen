module

public import BondalThomsen.Toric.Divisor.LineBundleGluing
public import BondalThomsen.Toric.Scheme.Integral
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf
public import BondalThomsen.Collection.BondalThomsenClasses
public import BondalThomsen.Toric.Divisor.SupportClasses

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

universe schemeUniverse

theorem openImmersion_sectionsIso_inv {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] :
    (IsOpenImmersion.ΓIsoTop inclusion).inv = inclusion.appLE inclusion.opensRange ⊤
      (by rw [← inclusion.image_top_eq_opensRange, inclusion.preimage_image_eq]) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
    eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

theorem openImmersion_sectionsIso_appLE {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (domain : Target.Opens) (contained : ⊤ ≤ inclusion ⁻¹ᵁ domain) :
    inclusion.appLE domain ⊤ contained ≫ (IsOpenImmersion.ΓIsoTop inclusion).hom =
      Target.presheaf.map (homOfLE (show inclusion.opensRange ≤ domain from by
        rintro point ⟨local_point, rfl⟩
        exact contained (show local_point ∈ (⊤ : Source.Opens) from trivial))).op := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom, eqToHom_op]
  rw [← Category.assoc, Scheme.Hom.appLE_appIso_inv, ← Functor.map_comp]
  rfl

variable {SchemeModel : Scheme.{schemeUniverse}} [IsIntegral SchemeModel]

noncomputable def openImmersionGerm {Source : Scheme.{schemeUniverse}}
    [Nonempty Source] (inclusion : Source ⟶ SchemeModel) [IsOpenImmersion inclusion] :
    Γ(Source, ⊤) →+* SchemeModel.functionField := by
  letI : Nonempty inclusion.opensRange := by
    obtain ⟨local_point⟩ := (inferInstance : Nonempty Source)
    exact ⟨⟨_, ⟨local_point, rfl⟩⟩⟩
  exact (SchemeModel.germToFunctionField inclusion.opensRange).hom.comp
    (IsOpenImmersion.ΓIsoTop inclusion).hom.hom

omit [IsIntegral SchemeModel] in

theorem openImmersion_sectionsIso_comp {Source Middle : Scheme.{schemeUniverse}}
    (inner : Source ⟶ Middle) (outer : Middle ⟶ SchemeModel)
    [IsOpenImmersion inner] [IsOpenImmersion outer] :
    inner.appTop ≫ (IsOpenImmersion.ΓIsoTop (inner ≫ outer)).hom =
      (IsOpenImmersion.ΓIsoTop outer).hom ≫ SchemeModel.presheaf.map
        (homOfLE (show (inner ≫ outer).opensRange ≤ outer.opensRange from by
          rintro point ⟨local_point, rfl⟩
          exact ⟨inner local_point, rfl⟩)).op := by
  have outer_contains : ⊤ ≤ outer ⁻¹ᵁ outer.opensRange := by
    rintro point _
    exact ⟨point, rfl⟩
  have inner_contains : ⊤ ≤ inner ⁻¹ᵁ (⊤ : Middle.Opens) := le_top
  have composite_contains : ⊤ ≤ (inner ≫ outer) ⁻¹ᵁ outer.opensRange := by
    rintro point _
    exact ⟨inner point, rfl⟩
  have maps_comp := Scheme.Hom.appLE_comp_appLE inner outer outer.opensRange ⊤ ⊤
    outer_contains inner_contains
  have top_app : inner.appLE ⊤ ⊤ inner_contains = inner.appTop := by
    exact inner.appLE_eq_app
  rw [← openImmersion_sectionsIso_inv outer, top_app] at maps_comp
  calc
    inner.appTop ≫ (IsOpenImmersion.ΓIsoTop (inner ≫ outer)).hom =
        (IsOpenImmersion.ΓIsoTop outer).hom ≫
          ((IsOpenImmersion.ΓIsoTop outer).inv ≫ inner.appTop) ≫
            (IsOpenImmersion.ΓIsoTop (inner ≫ outer)).hom := by simp
    _ = (IsOpenImmersion.ΓIsoTop outer).hom ≫
        (inner ≫ outer).appLE outer.opensRange ⊤ composite_contains ≫
          (IsOpenImmersion.ΓIsoTop (inner ≫ outer)).hom := by rw [maps_comp]
    _ = _ := by rw [openImmersion_sectionsIso_appLE]

theorem openImmersionGerm_comp {Source Middle : Scheme.{schemeUniverse}}
    [Nonempty Source] [Nonempty Middle]
    (inner : Source ⟶ Middle) (outer : Middle ⟶ SchemeModel)
    [IsOpenImmersion inner] [IsOpenImmersion outer] (section_value : Γ(Middle, ⊤)) :
    openImmersionGerm (inner ≫ outer) (inner.appTop section_value) =
      openImmersionGerm outer section_value := by
  unfold openImmersionGerm
  dsimp only [RingHom.comp_apply]
  have sections_same := ConcreteCategory.congr_hom
    (openImmersion_sectionsIso_comp inner outer) section_value
  simp only [ConcreteCategory.comp_apply] at sections_same
  rw [sections_same]
  exact SchemeModel.presheaf.germ_res_apply _ _ _ _

theorem nonempty_integral_open_intersection (first second : SchemeModel.Opens)
    [Nonempty first] [Nonempty second] : Nonempty (first ⊓ second : SchemeModel.Opens) := by
  simpa using nonempty_preirreducible_inter first.isOpen second.isOpen
    (by simpa using (inferInstance : Nonempty first))
    (by simpa using (inferInstance : Nonempty second))

theorem regularUnitGerm_eqToHom {first second : SchemeModel.Opens}
    [Nonempty first] [Nonempty second] (same_open : first = second)
    (unit : Γ(SchemeModel, first)ˣ) :
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel second
        (Units.map (SchemeModel.presheaf.map (eqToHom same_open.symm).op).hom.toMonoidHom unit) =
      TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel first unit := by
  subst second
  apply Units.ext
  change SchemeModel.germToFunctionField first
      ((SchemeModel.presheaf.map (eqToHom (rfl : first = first)).op) (unit : Γ(SchemeModel, first))) =
    SchemeModel.germToFunctionField first (unit : Γ(SchemeModel, first))
  simp only [eqToHom_refl, op_id]
  exact congrArg (SchemeModel.germToFunctionField first)
    (ConcreteCategory.congr_hom (SchemeModel.presheaf.map_id (op first))
      (unit : Γ(SchemeModel, first)))

structure CartierEquationAtlas (SchemeModel : Scheme.{schemeUniverse}) [IsIntegral SchemeModel] where
  Index : Type schemeUniverse
  chart : Index → SchemeModel.Opens
  covers : IsOpenCover chart
  nonempty_chart : ∀ index, Nonempty (chart index)
  equation : Index → SchemeModel.functionFieldˣ
  transition : ∀ first second, Γ(SchemeModel, chart first ⊓ chart second)ˣ
  transition_equation : ∀ first second,
    letI := nonempty_chart first
    letI := nonempty_chart second
    letI := nonempty_integral_open_intersection (chart first) (chart second)
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel
      (chart first ⊓ chart second) (transition first second) * equation second = equation first

namespace CartierEquationAtlas

variable (atlas : CartierEquationAtlas SchemeModel)

noncomputable def localClass (index : atlas.Index) :
    ((TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf SchemeModel).obj.obj
      (op (atlas.chart index)) : Type schemeUniverse) :=
  haveI := atlas.nonempty_chart index
  TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass SchemeModel (atlas.chart index)
    (Additive.ofMul (atlas.equation index))

theorem localClass_compatible : TopCat.Presheaf.IsCompatible
    (TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf SchemeModel).obj
    atlas.chart atlas.localClass := by
  intro first second
  let := atlas.nonempty_chart first
  let := atlas.nonempty_chart second
  let := nonempty_integral_open_intersection (atlas.chart first) (atlas.chart second)
  have first_restriction := TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict
    SchemeModel (U := atlas.chart first) (V := atlas.chart first ⊓ atlas.chart second)
    inf_le_left (Additive.ofMul (atlas.equation first))
  have second_restriction := TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict
    SchemeModel (U := atlas.chart second) (V := atlas.chart first ⊓ atlas.chart second)
    inf_le_right (Additive.ofMul (atlas.equation second))
  have equal_classes := (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
    SchemeModel (atlas.chart first ⊓ atlas.chart second)
    (atlas.equation first) (atlas.equation second)).mpr
      ⟨atlas.transition first second, atlas.transition_equation first second⟩
  exact first_restriction.trans (equal_classes.trans second_restriction.symm)

theorem existsUnique_cartierDivisor :
    ∃! divisor : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor SchemeModel,
      ∀ index, divisor |_ atlas.chart index = atlas.localClass index := by
  exact (TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf SchemeModel).existsUnique_gluing'
    atlas.chart ⊤ (fun _ => homOfLE le_top)
    (by rw [atlas.covers.iSup_eq_top]) atlas.localClass atlas.localClass_compatible

noncomputable def cartierDivisor :
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor SchemeModel :=
  atlas.existsUnique_cartierDivisor.exists.choose

theorem cartierDivisor_restrict (index : atlas.Index) :
    atlas.cartierDivisor |_ atlas.chart index = atlas.localClass index :=
  atlas.existsUnique_cartierDivisor.exists.choose_spec index

noncomputable def invertibleSheaf : TauCeti.AlgebraicGeometry.InvertibleSheaf SchemeModel :=
  atlas.cartierDivisor.toInvertibleSheaf

noncomputable def chartTrivialization (index : atlas.Index) :
    (SheafOfModules.unit SchemeModel.ringCatSheaf).over (atlas.chart index) ≅
      atlas.invertibleSheaf.obj.over (atlas.chart index) := by
  letI := atlas.nonempty_chart index
  exact (SheafOfModules.overFunctor SchemeModel.ringCatSheaf (atlas.chart index)).mapIso
      (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor
        SchemeModel (atlas.equation index)) ≪≫
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafOverIsoOfRestrictEq
      _ atlas.cartierDivisor (atlas.chart index)
      ((TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_restrict
        SchemeModel (atlas.equation index) (atlas.chart index)).trans
          (atlas.cartierDivisor_restrict index).symm)

theorem equation_isLocalEquationAt (index : atlas.Index) (point : SchemeModel)
    (contains : point ∈ atlas.chart index) :
    atlas.cartierDivisor.IsLocalEquationAt point (atlas.equation index) := by
  let := atlas.nonempty_chart index
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
    (atlas.cartierDivisor_restrict index).symm contains

end CartierEquationAtlas

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def denseTorusCharacterUnit (fan : Fan embedding)
    (character : Lattice →+ ℤ) : (affineCoordinateRing 𝕜 fan.lattice ⊥)ˣ :=
  toricMonomialUnit 𝕜 fan.lattice ⊥ character
    (by rw [dualSemigroup_bot]; trivial)
    (by rw [dualSemigroup_bot]; trivial)

theorem denseTorusCharacterUnit_add (fan : Fan embedding) (first second : Lattice →+ ℤ) :
    fan.denseTorusCharacterUnit 𝕜 (first + second) =
      fan.denseTorusCharacterUnit 𝕜 first * fan.denseTorusCharacterUnit 𝕜 second := by
  unfold denseTorusCharacterUnit
  exact (toricMonomialUnit_add 𝕜 _ _ _ _ _ _ _ _).symm

noncomputable def rationalCharacterUnit (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.algebraicRealization 𝕜 regular).functionFieldˣ := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  letI := fan.denseTorus_isIntegral 𝕜
  exact Units.map (BondalThomsen.openImmersionGerm (fan.denseTorusι 𝕜 regular nonempty)).toMonoidHom
    (Units.map (BondalThomsen.affineGlobalSectionsEquiv
      (affineCoordinateRing 𝕜 fan.lattice ⊥)).toMonoidHom (fan.denseTorusCharacterUnit 𝕜 character))

theorem rationalCharacterUnit_add (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (first second : Lattice →+ ℤ) :
    fan.rationalCharacterUnit 𝕜 regular nonempty (first + second) =
      fan.rationalCharacterUnit 𝕜 regular nonempty first *
        fan.rationalCharacterUnit 𝕜 regular nonempty second := by
  unfold rationalCharacterUnit
  rw [denseTorusCharacterUnit_add, map_mul, map_mul]

noncomputable def chartCoordinateSectionsEquiv (fan : Fan embedding)
    (regular : fan.IsRegular) (cone : fan.cones) :
    affineCoordinateRing 𝕜 fan.lattice cone.val ≃+*
      Γ(fan.algebraicRealization 𝕜 regular, (fan.affineToricChartι 𝕜 regular cone).opensRange) :=
  (BondalThomsen.affineGlobalSectionsEquiv (affineCoordinateRing 𝕜 fan.lattice cone.val)).trans
    (IsOpenImmersion.ΓIsoTop (fan.affineToricChartι 𝕜 regular cone)).commRingCatIsoToRingEquiv

noncomputable def chartCoordinateGerm (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (affineCoordinateRing 𝕜) fan.lattice cone.val →+* (fan.algebraicRealization 𝕜 regular).functionField := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  letI := fan.affineToricChart_isIntegral 𝕜 cone
  exact (BondalThomsen.openImmersionGerm (fan.affineToricChartι 𝕜 regular cone)).comp
    (BondalThomsen.affineGlobalSectionsEquiv (affineCoordinateRing 𝕜 fan.lattice cone.val)).toRingHom

theorem chartCoordinateGerm_torus (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (coordinate : affineCoordinateRing 𝕜 fan.lattice cone.val) :
    fan.chartCoordinateGerm 𝕜 regular nonempty cone coordinate =
      fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty)
        (faceAffineCoordinateRingMap 𝕜 fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf) coordinate) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.denseTorus_isIntegral 𝕜
  let := fan.affineToricChart_isIntegral 𝕜 cone
  let face_map := faceAffineToricSchemeMap 𝕜 fan.lattice
    ((fan.isToricCone cone.property).salient.bot_isFaceOf)
  let : IsOpenImmersion face_map :=
    (regular cone.property).isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _
  have same_inclusion := (fan.denseTorusι_eq 𝕜 regular nonempty (Nonempty.intro cone)).trans
    (fan.denseTorusι_face 𝕜 regular cone)
  change fan.denseTorusι 𝕜 regular nonempty = face_map ≫ fan.affineToricChartι 𝕜 regular cone
    at same_inclusion
  have naturality := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (faceAffineCoordinateRingMap 𝕜 fan.lattice
      ((fan.isToricCone cone.property).salient.bot_isFaceOf)).toRingHom)
  have naturality_value := ConcreteCategory.congr_hom naturality coordinate
  simp only [ConcreteCategory.comp_apply] at naturality_value
  change (Scheme.ΓSpecIso _).inv
      (faceAffineCoordinateRingMap 𝕜 fan.lattice
        ((fan.isToricCone cone.property).salient.bot_isFaceOf) coordinate) =
    face_map.appTop ((Scheme.ΓSpecIso _).inv coordinate) at naturality_value
  unfold chartCoordinateGerm
  dsimp only [RingHom.comp_apply, BondalThomsen.affineGlobalSectionsEquiv]
  change BondalThomsen.openImmersionGerm (fan.affineToricChartι 𝕜 regular cone)
      ((Scheme.ΓSpecIso _).inv coordinate) =
    BondalThomsen.openImmersionGerm (fan.denseTorusι 𝕜 regular nonempty)
      ((Scheme.ΓSpecIso _).inv
        (faceAffineCoordinateRingMap 𝕜 fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf) coordinate))
  have restriction_same := (BondalThomsen.openImmersionGerm_comp face_map
    (fan.affineToricChartι 𝕜 regular cone) ((Scheme.ΓSpecIso _).inv coordinate)).symm
  have restriction_same' :
      BondalThomsen.openImmersionGerm (fan.affineToricChartι 𝕜 regular cone)
          ((Scheme.ΓSpecIso _).inv coordinate) =
        BondalThomsen.openImmersionGerm (fan.denseTorusι 𝕜 regular nonempty)
          (face_map.appTop ((Scheme.ΓSpecIso _).inv coordinate)) := by
    simpa only [← same_inclusion] using restriction_same
  exact restriction_same'.trans
    (congrArg (BondalThomsen.openImmersionGerm (fan.denseTorusι 𝕜 regular nonempty))
      naturality_value).symm

theorem chartCoordinateGerm_monomialUnit (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup fan.lattice cone.val)
    (negative : -character ∈ dualSemigroup fan.lattice cone.val) :
    Units.map (fan.chartCoordinateGerm 𝕜 regular nonempty cone).toMonoidHom
        (toricMonomialUnit 𝕜 fan.lattice cone.val character positive negative) =
      fan.rationalCharacterUnit 𝕜 regular nonempty character := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  apply Units.ext
  simp only [Units.coe_map]
  change fan.chartCoordinateGerm 𝕜 regular nonempty cone
      (toricMonomialUnit 𝕜 fan.lattice cone.val character positive negative :
        affineCoordinateRing 𝕜 fan.lattice cone.val) = _
  rw [fan.chartCoordinateGerm_torus 𝕜 regular nonempty cone]
  have restricted := toricMonomialUnit_face_restriction 𝕜 fan.lattice
    ((fan.isToricCone cone.property).salient.bot_isFaceOf) character positive negative
  have restricted_value := congrArg Units.val restricted
  simp only [Units.coe_map] at restricted_value
  exact (congrArg (fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty))
    restricted_value).trans (by rfl)

theorem chart_opensRange_intersection (fan : Fan embedding) (regular : fan.IsRegular)
    (first second : fan.cones) :
    (fan.affineToricChartι 𝕜 regular (first ⊓ second)).opensRange =
      (fan.affineToricChartι 𝕜 regular first).opensRange ⊓
        (fan.affineToricChartι 𝕜 regular second).opensRange := by
  ext point
  constructor
  · rintro ⟨local_point, rfl⟩
    constructor
    · refine ⟨fan.affineToricOverlapLeft 𝕜 first second local_point, ?_⟩
      exact congrArg (fun morphism => morphism local_point)
        (fan.affineToricOverlapLeft_comp_affineToricChartι 𝕜 regular first second)
    · refine ⟨fan.affineToricOverlapRight 𝕜 first second local_point, ?_⟩
      exact congrArg (fun morphism => morphism local_point)
        (fan.affineToricOverlapRight_comp_affineToricChartι 𝕜 regular first second)
  · rintro ⟨⟨first_point, first_image⟩, ⟨second_point, second_image⟩⟩
    obtain ⟨common_point, common_first, _⟩ :=
      (fan.affineToricChartι_eq_affineToricChartι_iff 𝕜 regular first_point second_point).mp
        (first_image.trans second_image.symm)
    refine ⟨common_point, ?_⟩
    calc
      fan.affineToricChartι 𝕜 regular (first ⊓ second) common_point =
          fan.affineToricChartι 𝕜 regular first
            (fan.affineToricOverlapLeft 𝕜 first second common_point) :=
        (congrArg (fun morphism => morphism common_point)
          (fan.affineToricOverlapLeft_comp_affineToricChartι 𝕜 regular first second)).symm
      _ = point := by rw [common_first, first_image]

theorem chartOpen_nonempty (fan : Fan embedding) (regular : fan.IsRegular)
    (cone : fan.cones) : Nonempty (fan.affineToricChartι 𝕜 regular cone).opensRange := by
  let := fan.affineToricChart_isIntegral 𝕜 cone
  obtain ⟨local_point⟩ := (inferInstance : Nonempty (fan.affineToricChart 𝕜 cone))
  exact ⟨⟨_, ⟨local_point, rfl⟩⟩⟩

theorem chartCoordinateGerm_regularUnit (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (unit : (affineCoordinateRing 𝕜 fan.lattice cone.val)ˣ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField
        (fan.algebraicRealization 𝕜 regular) (fan.affineToricChartι 𝕜 regular cone).opensRange
        (Units.map (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).toMonoidHom unit) =
      Units.map (fan.chartCoordinateGerm 𝕜 regular nonempty cone).toMonoidHom unit := by
  apply Units.ext
  rfl

theorem denseTorusCharacterUnit_zero (fan : Fan embedding) :
    fan.denseTorusCharacterUnit 𝕜 0 = 1 := by
  apply Units.ext
  change MonoidAlgebra.single (Multiplicative.ofAdd (0 : dualSemigroup fan.lattice ⊥)) 1 = 1
  rfl

theorem rationalCharacterUnit_zero (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) : fan.rationalCharacterUnit 𝕜 regular nonempty 0 = 1 := by
  unfold rationalCharacterUnit
  rw [denseTorusCharacterUnit_zero, map_one, map_one]

theorem rationalCharacterUnit_neg (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (character : Lattice →+ ℤ) :
    fan.rationalCharacterUnit 𝕜 regular nonempty (-character) =
      (fan.rationalCharacterUnit 𝕜 regular nonempty character)⁻¹ := by
  have cancels := fan.rationalCharacterUnit_add 𝕜 regular nonempty character (-character)
  rw [add_neg_cancel, rationalCharacterUnit_zero] at cancels
  exact mul_eq_one_iff_eq_inv.mp
    (by simpa only [mul_comm] using cancels.symm)

theorem rationalCharacterUnit_sub_mul (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (first second : Lattice →+ ℤ) :
    fan.rationalCharacterUnit 𝕜 regular nonempty (first - second) *
        fan.rationalCharacterUnit 𝕜 regular nonempty second =
      fan.rationalCharacterUnit 𝕜 regular nonempty first := by
  rw [← rationalCharacterUnit_add, sub_add_cancel]

structure CharacterEquationAtlas (fan : Fan embedding) (regular : fan.IsRegular) where
  Index : Type
  cone : Index → fan.cones
  covers : IsOpenCover (fun index => (fan.affineToricChartι 𝕜 regular (cone index)).opensRange)
  character : Index → Lattice →+ ℤ
  positive : ∀ first second, character first - character second ∈
    dualSemigroup fan.lattice (cone first ⊓ cone second).val
  negative : ∀ first second, -(character first - character second) ∈
    dualSemigroup fan.lattice (cone first ⊓ cone second).val

namespace CharacterEquationAtlas

variable {fan : Fan embedding} {regular : fan.IsRegular}

noncomputable def transition (atlas : CharacterEquationAtlas 𝕜 fan regular)
    (first second : atlas.Index) :
    Γ(fan.algebraicRealization 𝕜 regular,
      (fan.affineToricChartι 𝕜 regular (atlas.cone first)).opensRange ⊓
        (fan.affineToricChartι 𝕜 regular (atlas.cone second)).opensRange)ˣ :=
  Units.map ((fan.algebraicRealization 𝕜 regular).presheaf.map
      (eqToHom (fan.chart_opensRange_intersection 𝕜 regular
        (atlas.cone first) (atlas.cone second)).symm).op).hom.toMonoidHom
    (Units.map (fan.chartCoordinateSectionsEquiv 𝕜 regular
      (atlas.cone first ⊓ atlas.cone second)).toMonoidHom
      (toricMonomialUnit 𝕜 fan.lattice _ (atlas.character first - atlas.character second)
        (atlas.positive first second) (atlas.negative first second)))

theorem transition_germ (atlas : CharacterEquationAtlas 𝕜 fan regular)
    (nonempty : Nonempty fan.cones) (first second : atlas.Index) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    letI := fan.chartOpen_nonempty 𝕜 regular (atlas.cone first)
    letI := fan.chartOpen_nonempty 𝕜 regular (atlas.cone second)
    letI := BondalThomsen.nonempty_integral_open_intersection
      (fan.affineToricChartι 𝕜 regular (atlas.cone first)).opensRange
      (fan.affineToricChartι 𝕜 regular (atlas.cone second)).opensRange
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField
        (fan.algebraicRealization 𝕜 regular) _ (atlas.transition 𝕜 first second) =
      fan.rationalCharacterUnit 𝕜 regular nonempty (atlas.character first - atlas.character second) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.chartOpen_nonempty 𝕜 regular (atlas.cone first)
  let := fan.chartOpen_nonempty 𝕜 regular (atlas.cone second)
  let := BondalThomsen.nonempty_integral_open_intersection
    (fan.affineToricChartι 𝕜 regular (atlas.cone first)).opensRange
    (fan.affineToricChartι 𝕜 regular (atlas.cone second)).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular (atlas.cone first ⊓ atlas.cone second)
  have transported := fan.chartCoordinateGerm_regularUnit 𝕜 regular nonempty
    (atlas.cone first ⊓ atlas.cone second)
    (toricMonomialUnit 𝕜 fan.lattice _ (atlas.character first - atlas.character second)
      (atlas.positive first second) (atlas.negative first second))
  have monomial := fan.chartCoordinateGerm_monomialUnit 𝕜 regular nonempty
    (atlas.cone first ⊓ atlas.cone second) (atlas.character first - atlas.character second)
    (atlas.positive first second) (atlas.negative first second)
  have same_open := fan.chart_opensRange_intersection 𝕜 regular (atlas.cone first) (atlas.cone second)
  unfold transition
  exact (BondalThomsen.regularUnitGerm_eqToHom same_open _).trans (transported.trans monomial)

noncomputable def cartierEquationAtlas (atlas : CharacterEquationAtlas 𝕜 fan regular)
    (nonempty : Nonempty fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    BondalThomsen.CartierEquationAtlas (fan.algebraicRealization 𝕜 regular) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact {
    Index := atlas.Index
    chart := fun index => (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange
    covers := atlas.covers
    nonempty_chart := fun index => fan.chartOpen_nonempty 𝕜 regular (atlas.cone index)
    equation := fun index => fan.rationalCharacterUnit 𝕜 regular nonempty (atlas.character index)
    transition := atlas.transition 𝕜
    transition_equation := fun first second => by
      rw [atlas.transition_germ 𝕜 nonempty]
      exact fan.rationalCharacterUnit_sub_mul 𝕜 regular nonempty _ _ }

noncomputable def invertibleSheaf (atlas : CharacterEquationAtlas 𝕜 fan regular)
    (nonempty : Nonempty fan.cones) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact (atlas.cartierEquationAtlas 𝕜 nonempty).invertibleSheaf

end CharacterEquationAtlas

variable [FiniteDimensional ℝ Ambient]

omit [FiniteDimensional ℝ Ambient] in

theorem completeFan_nonemptyCones (fan : Fan embedding) (complete : fan.IsComplete) :
    Nonempty fan.cones := by
  obtain ⟨cone, member, _⟩ := fan.isComplete_iff.mp complete (0 : Ambient)
  exact ⟨⟨cone, member⟩⟩

noncomputable def divisorChartBasis (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (cone : fan.cones) :
    { basisData : Σ size : ℕ, Module.Basis (Fin size) ℤ Lattice //
      fan.IsConeBasis basisData.2 ∧ cone.val.IsFaceOf
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basisData.2 index)))) } := by
  let existence := fan.exists_coneBasis_above complete regular cone.val cone.property
  let size := existence.choose
  let basis := existence.choose_spec.choose
  exact ⟨⟨size, basis⟩, existence.choose_spec.choose_spec⟩

noncomputable def divisorChartCone (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (cone : fan.cones) : fan.cones :=
  ⟨PointedCone.hull ℝ (Set.range (fun index =>
    embedding ((fan.divisorChartBasis complete regular cone).val.2 index))),
    (fan.divisorChartBasis complete regular cone).property.1⟩

theorem divisorChartCone_covers (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) : IsOpenCover
      (fun cone => (fan.affineToricChartι 𝕜 regular (fan.divisorChartCone complete regular cone)).opensRange) := by
  apply IsOpenCover.mk
  apply top_unique
  intro point _
  obtain ⟨cone, local_point, local_image⟩ :=
    fan.exists_affineToricChartι_apply_eq 𝕜 regular point
  let containing := fan.divisorChartCone complete regular cone
  have face_of : cone.val.IsFaceOf containing.val :=
    (fan.divisorChartBasis complete regular cone).property.2
  refine Opens.mem_iSup.mpr ⟨cone, ?_⟩
  refine ⟨faceAffineToricSchemeMap 𝕜 fan.lattice face_of local_point, ?_⟩
  exact (congrArg (fun morphism => morphism local_point)
    (fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 regular face_of)).trans local_image

noncomputable def invariantDivisorCharacterAtlas (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    CharacterEquationAtlas 𝕜 fan regular := by
  let indices := (Finite.equivFin fan.cones).symm
  refine {
    Index := Fin (Nat.card fan.cones)
    cone := fun index => fan.divisorChartCone complete regular (indices index)
    covers := ?_
    character := fun index => fan.coneDivisorCharacter
      (fan.divisorChartBasis complete regular (indices index)).val.2
      (fan.divisorChartBasis complete regular (indices index)).property.1 divisor
    positive := ?_
    negative := ?_ }
  · apply IsOpenCover.mk
    apply top_unique
    intro point _
    have in_cover : point ∈ iSup
        (fun cone => (fan.affineToricChartι 𝕜 regular
          (fan.divisorChartCone complete regular cone)).opensRange) := by
      rw [(fan.divisorChartCone_covers 𝕜 complete regular).iSup_eq_top]
      trivial
    obtain ⟨cone, member⟩ := Opens.mem_iSup.mp in_cover
    exact Opens.mem_iSup.mpr ⟨(Finite.equivFin fan.cones) cone,
      by
        have same_cone : indices ((Finite.equivFin fan.cones) cone) = cone :=
          (Finite.equivFin fan.cones).symm_apply_apply cone
        exact same_cone.symm ▸ member⟩
  · intro first second
    exact
    (fan.coneDivisorCharacter_transition_dualSemigroup
      (fan.divisorChartBasis complete regular (indices first)).val.2
      (fan.divisorChartBasis complete regular (indices first)).property.1
      (fan.divisorChartBasis complete regular (indices second)).val.2
      (fan.divisorChartBasis complete regular (indices second)).property.1 divisor).1
  · intro first second
    exact
    (fan.coneDivisorCharacter_transition_dualSemigroup
      (fan.divisorChartBasis complete regular (indices first)).val.2
      (fan.divisorChartBasis complete regular (indices first)).property.1
      (fan.divisorChartBasis complete regular (indices second)).val.2
      (fan.divisorChartBasis complete regular (indices second)).property.1 divisor).2

noncomputable def CharacterEquationAtlas.neg {fan : Fan embedding} {regular : fan.IsRegular}
    (atlas : CharacterEquationAtlas 𝕜 fan regular) : CharacterEquationAtlas 𝕜 fan regular where
  Index := atlas.Index
  cone := atlas.cone
  covers := atlas.covers
  character := fun index => -atlas.character index
  positive := fun first second => by
    convert atlas.negative first second using 1; abel
  negative := fun first second => by
    convert atlas.positive first second using 1; abel

noncomputable def invariantDivisorCartier (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor (fan.algebraicRealization 𝕜 regular) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)).cartierDivisor

noncomputable def invariantDivisorLineBundle (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (fan.invariantDivisorCartier 𝕜 complete regular divisor).toInvertibleSheaf

theorem invariantDivisorCartier_restrict (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).Index) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor
    letI := fan.chartOpen_nonempty 𝕜 regular (atlas.cone index)
    (fan.invariantDivisorCartier 𝕜 complete regular divisor) |_
        (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-atlas.character index))) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)).cartierDivisor_restrict index

noncomputable def invariantDivisorLineBundle_chartTrivialization (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).Index) :
    let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor
    (SheafOfModules.unit (fan.algebraicRealization 𝕜 regular).ringCatSheaf).over
        (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.over
        (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)).chartTrivialization index

theorem invariantDivisorCartier_isLocalEquationAt (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).Index)
    (point : fan.algebraicRealization 𝕜 regular)
    (contains : point ∈ (fan.affineToricChartι 𝕜 regular
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).cone index)).opensRange) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.invariantDivisorCartier 𝕜 complete regular divisor).IsLocalEquationAt point
      (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (-(fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).character index)) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)).equation_isLocalEquationAt index point contains

omit [FiniteDimensional ℝ Ambient] in

theorem coneDivisorCharacter_zero (fan : Fan embedding) {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    fan.coneDivisorCharacter basis cone_basis 0 = 0 := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change fan.coneDivisorCharacter basis cone_basis 0 (basis index) = 0
  simp only [coneDivisorCharacter_basis, Finsupp.zero_apply, neg_zero]

noncomputable def divisorLocalCharacter (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) : Lattice →+ ℤ :=
  (fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).character index

theorem divisorLocalCharacter_add (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (first second : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    fan.divisorLocalCharacter 𝕜 complete regular (first + second) index =
      fan.divisorLocalCharacter 𝕜 complete regular first index +
        fan.divisorLocalCharacter 𝕜 complete regular second index :=
  fan.coneDivisorCharacter_add _ _ first second

noncomputable def divisorLocalCone (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (index : Fin (Nat.card fan.cones)) : fan.cones :=
  (fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).cone index

theorem invariantDivisorCartier_localEquation (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let chart := (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
    letI := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
    (fan.invariantDivisorCartier 𝕜 complete regular divisor) |_ chart =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular) chart
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-fan.divisorLocalCharacter 𝕜 complete regular divisor index))) :=
  fan.invariantDivisorCartier_restrict 𝕜 complete regular divisor index

theorem cartierDivisor_eq_of_divisorCharts (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    ∀ first second : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor (fan.algebraicRealization 𝕜 regular),
      (∀ index : Fin (Nat.card fan.cones),
        first |_ (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange =
          second |_ (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange) →
      first = second := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  intro first second equal_on_charts
  exact (TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf
      (fan.algebraicRealization 𝕜 regular)).eq_of_locally_eq'
    (fun index : Fin (Nat.card fan.cones) =>
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange)
    ⊤ (fun _ => homOfLE le_top)
    (by
      change ⊤ ≤ ⨆ index,
        (fan.affineToricChartι 𝕜 regular
          ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).cone index)).opensRange
      rw [(fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).covers.iSup_eq_top])
    first second equal_on_charts

theorem invariantDivisorCartier_zero (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) : fan.invariantDivisorCartier 𝕜 complete regular 0 = 0 := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  apply fan.cartierDivisor_eq_of_divisorCharts 𝕜 complete regular
  intro index
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  have character_zero : fan.divisorLocalCharacter 𝕜 complete regular 0 index = 0 :=
    fan.coneDivisorCharacter_zero _ _
  rw [fan.invariantDivisorCartier_localEquation 𝕜 complete regular 0 index, character_zero,
    neg_zero, rationalCharacterUnit_zero]
  simp only [show Additive.ofMul (1 : (fan.algebraicRealization 𝕜 regular).functionFieldˣ) = 0 from rfl,
    TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_zero]

theorem invariantDivisorCartier_add (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (first second : fan.InvariantRayDivisor) :
    fan.invariantDivisorCartier 𝕜 complete regular (first + second) =
      fan.invariantDivisorCartier 𝕜 complete regular first +
        fan.invariantDivisorCartier 𝕜 complete regular second := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  apply fan.cartierDivisor_eq_of_divisorCharts 𝕜 complete regular
  intro index
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  rw [TopCat.Presheaf.restrict_sum,
    fan.invariantDivisorCartier_localEquation 𝕜 complete regular (first + second) index,
    fan.invariantDivisorCartier_localEquation 𝕜 complete regular first index,
    fan.invariantDivisorCartier_localEquation 𝕜 complete regular second index,
    divisorLocalCharacter_add, neg_add, rationalCharacterUnit_add,
    ofMul_mul, map_add]

noncomputable def invariantDivisorCartierHom (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    fan.InvariantRayDivisor →+
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor (fan.algebraicRealization 𝕜 regular) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact {
    toFun := fan.invariantDivisorCartier 𝕜 complete regular
    map_zero' := fan.invariantDivisorCartier_zero 𝕜 complete regular
    map_add' := fan.invariantDivisorCartier_add 𝕜 complete regular }

theorem invariantDivisorCartier_principal (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.invariantDivisorCartier 𝕜) complete regular (fan.principalRayDivisor character) =
      TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor (fan.algebraicRealization 𝕜 regular)
        (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) character) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  apply fan.cartierDivisor_eq_of_divisorCharts 𝕜 complete regular
  intro index
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  have local_principal : fan.divisorLocalCharacter 𝕜 complete regular
      (fan.principalRayDivisor character) index = -character :=
    fan.coneDivisorCharacter_principal _ _ character
  rw [fan.invariantDivisorCartier_localEquation 𝕜 complete regular _ index, local_principal,
    neg_neg, TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_restrict]

noncomputable def invariantDivisorPicardRealization (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    fan.InvariantRayDivisorClass →+
      Additive (TauCeti.AlgebraicGeometry.LineBundleClass (fan.algebraicRealization 𝕜 regular)) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact fan.cartierInvariantDivisorClassRealization
    (fan.invariantDivisorCartierHom 𝕜 complete regular) (fun character =>
      ⟨fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) character,
        fan.invariantDivisorCartier_principal 𝕜 complete regular character⟩)

@[simp] theorem invariantDivisorPicardRealization_apply (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    fan.invariantDivisorPicardRealization 𝕜 complete regular
      (fan.invariantRayDivisorClass divisor) =
        Additive.ofMul (TauCeti.AlgebraicGeometry.LineBundleClass.mk
          (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  unfold invariantDivisorPicardRealization cartierInvariantDivisorClassRealization
  exact fan.invariantDivisorClassToLineBundleClass_apply _ _ divisor

noncomputable def floorDivisorInvertibleSheaf (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (pairing : Lattice →+ ℚ) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular) :=
  fan.invariantDivisorLineBundle 𝕜 complete regular (fan.floorRayDivisor pairing)

end TauCeti.Toric.Fan
