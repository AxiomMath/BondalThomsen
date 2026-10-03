module

public import BondalThomsen.Toric.Frobenius.FrobeniusFinite
public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Multiplicative

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

universe schemeUniverse

variable {SchemeModel : Scheme.{schemeUniverse}} [IsIntegral SchemeModel]

noncomputable def rationalPullback (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel) :
    SchemeModel.functionField →+* SchemeModel.functionField :=
  (eqToHom (congrArg SchemeModel.presheaf.stalk generic.symm) ≫
    morphism.stalkMap (genericPoint SchemeModel)).hom

omit [IsIntegral SchemeModel] in
private theorem germ_transport (domain : SchemeModel.Opens) {first second : SchemeModel}
    (equal : first = second) (member : first ∈ domain) :
    SchemeModel.presheaf.germ domain first member ≫
        eqToHom (congrArg SchemeModel.presheaf.stalk equal) =
      SchemeModel.presheaf.germ domain second (equal ▸ member) := by
  subst second
  simp

theorem rationalPullback_germ (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) [Nonempty domain] [Nonempty (morphism ⁻¹ᵁ domain)]
    (regularSection : Γ(SchemeModel, domain)) :
    rationalPullback morphism generic (SchemeModel.germToFunctionField domain regularSection) =
      SchemeModel.germToFunctionField (morphism ⁻¹ᵁ domain)
        (morphism.app domain regularSection) := by
  have member := TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem domain
  have pulled_member : morphism (genericPoint SchemeModel) ∈ domain := generic.symm ▸ member
  have equation := morphism.germ_stalkMap_apply domain (genericPoint SchemeModel)
    pulled_member regularSection
  have transported := germ_transport domain generic.symm member
  change (morphism.stalkMap (genericPoint SchemeModel)).hom
      ((eqToHom (congrArg SchemeModel.presheaf.stalk generic.symm)).hom
        (SchemeModel.germToFunctionField domain regularSection)) = _
  have applied := congrArg (fun map => map.hom regularSection) transported
  have applied' : (eqToHom (congrArg SchemeModel.presheaf.stalk generic.symm)).hom
      (SchemeModel.germToFunctionField domain regularSection) =
    SchemeModel.presheaf.germ domain (morphism (genericPoint SchemeModel)) pulled_member
      regularSection := applied
  rw [applied']
  exact equation

theorem genericPoint_fixed_of_surjective (morphism : SchemeModel ⟶ SchemeModel)
    (surjective : Function.Surjective morphism) :
    morphism (genericPoint SchemeModel) = genericPoint SchemeModel := by
  apply IsGenericPoint.eq _ (genericPoint_spec SchemeModel)
  convert (genericPoint_spec SchemeModel).image morphism.continuous using 1
  rw [Set.image_univ, surjective.range_eq, closure_univ]

theorem rationalPullback_germLE (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain source : SchemeModel.Opens) [Nonempty domain] [Nonempty source]
    (contained : source ≤ morphism ⁻¹ᵁ domain) (regularSection : Γ(SchemeModel, domain)) :
    rationalPullback morphism generic (SchemeModel.germToFunctionField domain regularSection) =
      SchemeModel.germToFunctionField source
        (morphism.appLE domain source contained regularSection) := by
  let : Nonempty (morphism ⁻¹ᵁ domain) := by
    obtain ⟨point⟩ := (inferInstance : Nonempty source)
    exact ⟨⟨point.val, contained point.property⟩⟩
  rw [rationalPullback_germ morphism generic]
  exact (SchemeModel.presheaf.germ_res_apply (homOfLE contained)
    (genericPoint SchemeModel) (TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem source)
      (morphism.app domain regularSection)).symm

theorem rationalPullback_openImmersionGerm {Chart : Scheme.{schemeUniverse}}
    [Nonempty Chart] (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (chartMap : Chart ⟶ Chart) (square : inclusion ≫ morphism = chartMap ≫ inclusion)
    (preserved : morphism ⁻¹ᵁ inclusion.opensRange = inclusion.opensRange)
    (regularSection : Γ(Chart, ⊤)) :
    rationalPullback morphism generic (openImmersionGerm inclusion regularSection) =
      openImmersionGerm inclusion (chartMap.appTop regularSection) := by
  let : Nonempty inclusion.opensRange := by
    obtain ⟨point⟩ := (inferInstance : Nonempty Chart)
    exact ⟨⟨inclusion point, point, rfl⟩⟩
  have inclusion_contains : ⊤ ≤ inclusion ⁻¹ᵁ inclusion.opensRange := by
    rintro point _
    exact ⟨point, rfl⟩
  have preserved_contains : inclusion.opensRange ≤ morphism ⁻¹ᵁ inclusion.opensRange :=
    preserved.symm.le
  have first := Scheme.Hom.appLE_comp_appLE inclusion morphism
    inclusion.opensRange inclusion.opensRange ⊤ preserved_contains inclusion_contains
  have second := Scheme.Hom.appLE_comp_appLE chartMap inclusion
    inclusion.opensRange ⊤ ⊤ inclusion_contains le_top
  simp only [square] at first
  have composite : morphism.appLE inclusion.opensRange inclusion.opensRange preserved_contains ≫
      (IsOpenImmersion.ΓIsoTop inclusion).inv =
    (IsOpenImmersion.ΓIsoTop inclusion).inv ≫ chartMap.appTop := by
    rw [openImmersion_sectionsIso_inv]
    have top_map : chartMap.appLE ⊤ ⊤ le_top = chartMap.appTop := by
      exact chartMap.appLE_eq_app
    rw [top_map] at second
    exact first.trans second.symm
  have identified : (IsOpenImmersion.ΓIsoTop inclusion).hom ≫
      morphism.appLE inclusion.opensRange inclusion.opensRange preserved_contains =
    chartMap.appTop ≫ (IsOpenImmersion.ΓIsoTop inclusion).hom := by
    rw [← Iso.comp_inv_eq, Category.assoc, composite]
    simp
  unfold openImmersionGerm
  dsimp only [RingHom.comp_apply]
  rw [rationalPullback_germLE morphism generic inclusion.opensRange inclusion.opensRange
    preserved_contains]
  exact congrArg (fun map => SchemeModel.germToFunctionField inclusion.opensRange
    (map.hom regularSection)) identified

namespace CartierEquationAtlas

noncomputable def pullbackPreserved (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index) :
    CartierEquationAtlas SchemeModel where
  Index := atlas.Index
  chart := atlas.chart
  covers := atlas.covers
  nonempty_chart := atlas.nonempty_chart
  equation index := Units.map (rationalPullback morphism generic).toMonoidHom
    (atlas.equation index)
  transition first second :=
    Units.map (morphism.appLE (atlas.chart first ⊓ atlas.chart second)
      (atlas.chart first ⊓ atlas.chart second) (by
        rw [Scheme.Hom.preimage_inf, preserved first, preserved second])).hom.toMonoidHom
      (atlas.transition first second)
  transition_equation first second := by
    let := atlas.nonempty_chart first
    let := atlas.nonempty_chart second
    let := nonempty_integral_open_intersection (atlas.chart first) (atlas.chart second)
    have contained : atlas.chart first ⊓ atlas.chart second ≤
        morphism ⁻¹ᵁ (atlas.chart first ⊓ atlas.chart second) := by
      rw [Scheme.Hom.preimage_inf, preserved first, preserved second]
    have regular_unit : TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel
        (atlas.chart first ⊓ atlas.chart second)
          (Units.map (morphism.appLE _ _ contained).hom.toMonoidHom
            (atlas.transition first second)) =
      Units.map (rationalPullback morphism generic).toMonoidHom
        (TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel
          (atlas.chart first ⊓ atlas.chart second) (atlas.transition first second)) := by
      apply Units.ext
      exact (rationalPullback_germLE morphism generic _ _ contained
        (atlas.transition first second)).symm
    rw [regular_unit, ← map_mul, atlas.transition_equation]

theorem pullbackPreserved_restrict (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (index : atlas.Index) :
    letI := atlas.nonempty_chart index
    (atlas.pullbackPreserved morphism generic preserved).cartierDivisor |_ atlas.chart index =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass SchemeModel (atlas.chart index)
        (Additive.ofMul (Units.map (rationalPullback morphism generic).toMonoidHom
          (atlas.equation index))) :=
  (atlas.pullbackPreserved morphism generic preserved).cartierDivisor_restrict index

end CartierEquationAtlas

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem toricMultiplication_genericPoint (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) {degree : ℕ} (positive : 0 < degree) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.toricMultiplication 𝕜) regular degree (genericPoint (fan.algebraicRealization 𝕜 regular)) =
      genericPoint (fan.algebraicRealization 𝕜 regular) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact BondalThomsen.genericPoint_fixed_of_surjective _
    (fan.toricMultiplication_surjective 𝕜 regular positive)

noncomputable def toricMultiplicationFunctionField (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    {degree : ℕ} (positive : 0 < degree) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.algebraicRealization 𝕜 regular).functionField →+*
      (fan.algebraicRealization 𝕜 regular).functionField := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact BondalThomsen.rationalPullback (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular nonempty positive)

theorem toricMultiplicationFunctionField_chartCoordinate (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    {degree : ℕ} (positive : 0 < degree) (cone : fan.cones)
    (coordinate : affineCoordinateRing 𝕜 fan.lattice cone.val) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.toricMultiplicationFunctionField 𝕜) regular nonempty positive
        (fan.chartCoordinateGerm 𝕜 regular nonempty cone coordinate) =
      fan.chartCoordinateGerm 𝕜 regular nonempty cone
        (fan.toricMultiplicationRing 𝕜 degree cone.val coordinate) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.affineToricChart_isIntegral 𝕜 cone
  have square := fan.affineToricChartι_comp_toricMultiplication 𝕜 regular positive cone
  have preserved := fan.toricMultiplication_preimage_chart_open 𝕜 regular positive cone
  have germ := BondalThomsen.rationalPullback_openImmersionGerm
    (fan.affineToricChartι 𝕜 regular cone) (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular nonempty positive)
    (fan.toricMultiplicationChart 𝕜 degree cone) square preserved
    (BondalThomsen.affineGlobalSectionsEquiv (affineCoordinateRing 𝕜 fan.lattice cone.val) coordinate)
  have affine := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree cone.val).toRingHom)
  have affine_apply := (ConcreteCategory.congr_hom affine coordinate).symm
  simp only [ConcreteCategory.comp_apply] at affine_apply
  change (fan.toricMultiplicationChart 𝕜 degree cone).appTop
      (BondalThomsen.affineGlobalSectionsEquiv (affineCoordinateRing 𝕜 fan.lattice cone.val) coordinate) =
    BondalThomsen.affineGlobalSectionsEquiv (affineCoordinateRing 𝕜 fan.lattice cone.val)
      (fan.toricMultiplicationRing 𝕜 degree cone.val coordinate) at affine_apply
  exact germ.trans (congrArg (BondalThomsen.openImmersionGerm
    (fan.affineToricChartι 𝕜 regular cone)) affine_apply)

theorem toricMultiplicationFunctionField_character (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    {degree : ℕ} (positive : 0 < degree) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    Units.map (fan.toricMultiplicationFunctionField 𝕜 regular nonempty positive).toMonoidHom
        (fan.rationalCharacterUnit 𝕜 regular nonempty character) =
      fan.rationalCharacterUnit 𝕜 regular nonempty character ^ degree := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  apply Units.ext
  change fan.toricMultiplicationFunctionField 𝕜 regular nonempty positive
    (fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty)
      (fan.denseTorusCharacterUnit 𝕜 character : affineCoordinateRing 𝕜 fan.lattice ⊥)) = _
  rw [fan.toricMultiplicationFunctionField_chartCoordinate 𝕜 regular nonempty positive]
  have power := fan.toricMultiplicationRing_character 𝕜 degree ⊥
    (⟨character, by rw [dualSemigroup_bot]; trivial⟩ : dualSemigroup fan.lattice ⊥)
  have mapped := congrArg
    (fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty)) power
  exact mapped.trans (by rw [map_pow]; rfl)

theorem rationalCharacterUnit_nsmul (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (degree : ℕ) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.rationalCharacterUnit 𝕜) regular nonempty (degree • character) =
      fan.rationalCharacterUnit 𝕜 regular nonempty character ^ degree := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  induction degree with
  | zero => simp [fan.rationalCharacterUnit_zero 𝕜 regular nonempty]
  | succ degree induction =>
    rw [succ_nsmul, fan.rationalCharacterUnit_add 𝕜, induction, pow_succ]

variable [FiniteDimensional ℝ Ambient]

theorem divisorLocalCharacter_nsmul (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (degree : ℕ) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    fan.divisorLocalCharacter 𝕜 complete regular (degree • divisor) index =
      degree • fan.divisorLocalCharacter 𝕜 complete regular divisor index := by
  induction degree with
  | zero =>
    have additive := fan.divisorLocalCharacter_add 𝕜 complete regular 0 0 index
    simp only [zero_add] at additive
    simpa only [zero_nsmul] using (add_eq_left.mp additive.symm)
  | succ degree induction =>
    rw [succ_nsmul, fan.divisorLocalCharacter_add 𝕜, induction, succ_nsmul]

theorem toricMultiplication_invariantDivisor_equation (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let chart := (fan.affineToricChartι 𝕜 regular
      (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
    letI := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
    (fan.invariantDivisorCartier 𝕜 complete regular (degree • divisor)) |_ chart =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular) chart
        (Additive.ofMul (Units.map
          (fan.toricMultiplicationFunctionField 𝕜 regular
            (fan.completeFan_nonemptyCones complete) positive).toMonoidHom
          (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
            (-fan.divisorLocalCharacter 𝕜 complete regular divisor index)))) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  dsimp only
  rw [fan.invariantDivisorCartier_localEquation 𝕜, fan.divisorLocalCharacter_nsmul 𝕜,
    ← smul_neg, fan.rationalCharacterUnit_nsmul 𝕜,
    fan.toricMultiplicationFunctionField_character 𝕜]

noncomputable def toricMultiplicationInvariantCartierPullback (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (divisor : fan.InvariantRayDivisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor (fan.algebraicRealization 𝕜 regular) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let atlas := ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)
  exact (atlas.pullbackPreserved (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive)
    (fun index => fan.toricMultiplication_preimage_chart_open 𝕜 regular positive
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).cone index))).cartierDivisor

theorem toricMultiplicationInvariantCartierPullback_eq (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (divisor : fan.InvariantRayDivisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.toricMultiplicationInvariantCartierPullback 𝕜) complete regular positive divisor =
      fan.invariantDivisorCartier 𝕜 complete regular (degree • divisor) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  apply fan.cartierDivisor_eq_of_divisorCharts 𝕜 complete regular
  intro index
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  rw [fan.toricMultiplication_invariantDivisor_equation 𝕜 complete regular positive divisor index]
  let atlas := ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)
  exact atlas.pullbackPreserved_restrict (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive)
    (fun chartIndex => fan.toricMultiplication_preimage_chart_open 𝕜 regular positive
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).cone chartIndex)) index

end TauCeti.Toric.Fan
