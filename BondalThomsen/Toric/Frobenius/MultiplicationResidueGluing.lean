module

public import BondalThomsen.Toric.Frobenius.MultiplicationResidueSummands
public import BondalThomsen.ProjectiveBundle.FrameCompatibility
public import BondalThomsen.Toric.Frobenius.MultiplicationDivisorPullback
public import BondalThomsen.Toric.Frobenius.MultiplicationLineBundlePullback
public import BondalThomsen.Toric.Divisor.DivisorSheafSections

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable def residueFactorLinearMap {Scalars Source Middle Target : Type*}
    [Semiring Scalars] [AddCommMonoid Source] [AddCommMonoid Middle]
    [AddCommMonoid Target] [Module Scalars Source] [Module Scalars Middle]
    [Module Scalars Target] (morphism : Source →ₗ[Scalars] Target)
    (inclusion : Middle →ₗ[Scalars] Target) (injective : Function.Injective inclusion)
    (in_range : ∀ element, morphism element ∈ inclusion.range) :
    Source →ₗ[Scalars] Middle :=
  (LinearEquiv.ofInjective inclusion injective).symm.toLinearMap.comp
    (morphism.codRestrict inclusion.range in_range)

theorem residueFactorLinearMap_inclusion {Scalars Source Middle Target : Type*}
    [Semiring Scalars] [AddCommMonoid Source] [AddCommMonoid Middle]
    [AddCommMonoid Target] [Module Scalars Source] [Module Scalars Middle]
    [Module Scalars Target] (morphism : Source →ₗ[Scalars] Target)
    (inclusion : Middle →ₗ[Scalars] Target) (injective : Function.Injective inclusion)
    (in_range : ∀ element, morphism element ∈ inclusion.range) (element : Source) :
    inclusion (residueFactorLinearMap morphism inclusion injective in_range element) =
      morphism element :=
  LinearEquiv.ofInjective_symm_apply inclusion (h := injective) _

noncomputable def residueFactorSheafHom {SchemeModel : Scheme}
    {Source Middle Target : SchemeModel.Modules} (morphism : Source ⟶ Target)
    (inclusion : Middle ⟶ Target)
    (injective : ∀ domain, Function.Injective (Scheme.Modules.Hom.app inclusion domain))
    (in_range : ∀ domain element,
      morphism.val.app (op domain) element ∈
        (inclusion.val.app (op domain)).hom.range) : Source ⟶ Middle where
  val :=
    { app := fun domain => ModuleCat.ofHom
        (residueFactorLinearMap (morphism.val.app domain).hom
          (inclusion.val.app domain).hom
          (injective domain.unop) (in_range domain.unop))
      naturality := by
        intro domain smaller restriction
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro element
        apply injective smaller.unop
        have inclusion_naturality := ConcreteCategory.congr_hom
          (inclusion.mapPresheaf.naturality restriction)
          (residueFactorLinearMap (morphism.val.app domain).hom
            (inclusion.val.app domain).hom
            (injective domain.unop) (in_range domain.unop) element)
        have morphism_naturality := ConcreteCategory.congr_hom
          (morphism.mapPresheaf.naturality restriction) element
        simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app]
          at inclusion_naturality morphism_naturality
        change Scheme.Modules.Hom.app inclusion smaller.unop
            (residueFactorLinearMap (morphism.val.app smaller).hom
              (inclusion.val.app smaller).hom
              (injective smaller.unop) (in_range smaller.unop)
              (Source.presheaf.map restriction element)) =
          Scheme.Modules.Hom.app inclusion smaller.unop
            (Middle.presheaf.map restriction
              ((residueFactorLinearMap (morphism.val.app domain).hom
                (inclusion.val.app domain).hom
                (injective domain.unop) (in_range domain.unop)) element))
        have smaller_factor := residueFactorLinearMap_inclusion
          (morphism.val.app smaller).hom (inclusion.val.app smaller).hom
          (injective smaller.unop) (in_range smaller.unop)
          (Source.presheaf.map restriction element)
        have domain_factor := residueFactorLinearMap_inclusion
          (morphism.val.app domain).hom (inclusion.val.app domain).hom
          (injective domain.unop) (in_range domain.unop) element
        exact smaller_factor.trans (morphism_naturality.trans
          ((congrArg (Target.presheaf.map restriction) domain_factor).symm.trans
            inclusion_naturality.symm)) }

theorem residueFactorSheafHom_inclusion {SchemeModel : Scheme}
    {Source Middle Target : SchemeModel.Modules} (morphism : Source ⟶ Target)
    (inclusion : Middle ⟶ Target)
    (injective : ∀ domain, Function.Injective (Scheme.Modules.Hom.app inclusion domain))
    (in_range : ∀ domain element,
      morphism.val.app (op domain) element ∈
        (inclusion.val.app (op domain)).hom.range) :
    residueFactorSheafHom morphism inclusion injective in_range ≫ inclusion = morphism := by
  apply Scheme.Modules.hom_ext
  intro domain
  ext element
  exact residueFactorLinearMap_inclusion (morphism.val.app (op domain)).hom
    (inclusion.val.app (op domain)).hom (injective domain) (in_range domain) element

theorem affineResidueSheaf_frame_inclusion {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (residue : Index) :
    letI := Module.compHom Source ring_map.hom
    (affineResidueSheafUnitIso ring_map basis residue).hom ≫
      affineResidueSheafInclusion ring_map basis residue =
    tildeSelf.inv ≫ (tilde.functor Target).map
      (ModuleCat.ofHom (basisResidueInclusion basis residue)) ≫
      (affinePushforwardStructureTildeIso ring_map).hom := by
  let := Module.compHom Source ring_map.hom
  simp only [affineResidueSheafUnitIso, affineResidueSheafInclusion,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc ((tilde.functor Target).map _), ← Functor.map_comp]
  have composite : (basisResidueEquiv basis residue).toModuleIso.hom ≫
      ModuleCat.ofHom (basisResidueSubmodule basis residue).subtype =
    ModuleCat.ofHom (basisResidueInclusion basis residue) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change ↑(basisResidueEquiv basis residue coefficient) =
      basisResidueInclusion basis residue coefficient
    exact LinearEquiv.ofInjective_apply
      (h := basisResidueInclusion_injective basis residue) _ _
  rw [composite]
  rfl

theorem affineResidueSheaf_generator_sections {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (residue : Index) (coefficient : Target) :
    letI := Module.compHom Source ring_map.hom
    affinePushforwardStructureSectionsEquiv ring_map
      ((Scheme.Modules.Hom.app ((affineResidueSheafUnitIso ring_map basis residue).hom ≫
        affineResidueSheafInclusion ring_map basis residue) ⊤)
          (tilde.toOpen (ModuleCat.of Target Target) ⊤ coefficient)) =
      basisResidueInclusion basis residue coefficient := by
  let := Module.compHom Source ring_map.hom
  rw [affineResidueSheaf_frame_inclusion]
  let pushforward := (Scheme.Modules.pushforward (Spec.map ring_map)).obj
    (SheafOfModules.unit (Spec Source).ringCatSheaf)
  let inclusion := ModuleCat.ofHom (basisResidueInclusion basis residue)
  let comparison := (affinePushforwardStructureSectionsEquiv ring_map).symm.toModuleIso.hom
  have naturality := tilde.toOpen_map_app inclusion ⊤
  have comparison_naturality := tilde.toOpen_map_app comparison ⊤
  have counit := Scheme.Modules.toOpen_fromTildeΓ_app pushforward ⊤
  have section_eq := ConcreteCategory.congr_hom naturality coefficient
  have comparison_eq := ConcreteCategory.congr_hom comparison_naturality
    (inclusion coefficient)
  have counit_eq := ConcreteCategory.congr_hom counit
    (comparison (inclusion coefficient))
  simp only [ConcreteCategory.comp_apply] at section_eq comparison_eq counit_eq
  change affinePushforwardStructureSectionsEquiv ring_map
    ((modulesSpecToSheaf.map pushforward.fromTildeΓ).hom.app (op ⊤)
      ((modulesSpecToSheaf.map (tilde.map comparison)).hom.app (op ⊤)
        ((modulesSpecToSheaf.map (tilde.map inclusion)).hom.app (op ⊤)
          (tilde.toOpen (ModuleCat.of Target Target) ⊤ coefficient)))) = _
  rw [section_eq, comparison_eq]
  change affinePushforwardStructureSectionsEquiv ring_map
    ((modulesSpecToSheaf.map pushforward.fromTildeΓ).hom.app (op ⊤)
      (tilde.toOpen ((modulesSpecToSheaf.obj pushforward).presheaf.obj (op ⊤)) ⊤
        (comparison (inclusion coefficient)))) = _
  rw [counit_eq]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]
  exact (affinePushforwardStructureSectionsEquiv ring_map).apply_symm_apply _

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def residueFloorDivisor (fan : Fan embedding) (degree : ℕ)
    (character : Lattice →+ ℤ) : fan.InvariantRayDivisor :=
  fan.floorRayDivisor ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)

noncomputable def residueFloorAtlas (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (degree : ℕ) (character : Lattice →+ ℤ) :
    CharacterEquationAtlas 𝕜 fan regular :=
  fan.invariantDivisorCharacterAtlas 𝕜 complete regular (fan.residueFloorDivisor degree character)

noncomputable def residueFloorChartBasis (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (degree : ℕ) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index) :=
  fan.divisorChartBasis complete regular ((Finite.equivFin fan.cones).symm index)

theorem residueFloorAtlas_character (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (degree : ℕ) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index) :
    (fan.residueFloorAtlas 𝕜 complete regular degree character).character index =
      -residueFloorCharacter
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
        degree character :=
  fan.coneDivisorCharacter_floor_eq _ _ degree character

noncomputable def residueFloorFrame (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (degree : ℕ) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index) :
    (SheafOfModules.unit (fan.algebraicRealization 𝕜 regular).ringCatSheaf).over
        (fan.affineToricChartι 𝕜 regular
          ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)).opensRange ≅
      (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
        ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj.over
        (fan.affineToricChartι 𝕜 regular
          ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)).opensRange :=
  fan.invariantDivisorLineBundle_chartTrivialization 𝕜 complete regular
    (fan.residueFloorDivisor degree character) index

theorem residueFloorFrame_rational (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (degree : ℕ) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let chart := (fan.affineToricChartι 𝕜 regular
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)).opensRange
    (fan.residueFloorFrame 𝕜 complete regular degree character index).hom ≫
      (fan.invariantDivisorCartier 𝕜 complete regular
        (fan.residueFloorDivisor degree character)).sheafι.over chart =
      (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions (fan.algebraicRealization 𝕜 regular) ≫
        TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul (fan.algebraicRealization 𝕜 regular)
          (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
            (-residueFloorCharacter
              (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
              degree character) : (fan.algebraicRealization 𝕜 regular).functionField)).over chart := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let atlas := fan.residueFloorAtlas 𝕜 complete regular degree character
  have frame := ((atlas.neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)).frame_hom_ι index
  change (fan.residueFloorFrame 𝕜 complete regular degree character index).hom ≫
      (fan.invariantDivisorCartier 𝕜 complete regular
        (fan.residueFloorDivisor degree character)).sheafι.over _ =
    (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions (fan.algebraicRealization 𝕜 regular) ≫
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul (fan.algebraicRealization 𝕜 regular)
        ((fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-atlas.character index) : (fan.algebraicRealization 𝕜 regular).functionField)⁻¹)).over _ at frame
  rw [fan.residueFloorAtlas_character 𝕜] at frame
  simp only [fan.rationalCharacterUnit_neg 𝕜 regular
    (fan.completeFan_nonemptyCones complete), Units.val_inv_eq_inv_val]
  simpa only [neg_neg] using frame

omit [FiniteDimensional ℝ Ambient] in
theorem normalizedResidueMonomial_germ (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (positive : 0 < degree)
    (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.chartCoordinateGerm 𝕜) regular nonempty ⟨_, cone_basis⟩
      (fan.normalizedResidueMonomial 𝕜 basis positive character) =
      (fan.rationalCharacterUnit 𝕜 regular nonempty
        (normalizedResidueCharacter basis degree character) :
          (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  rw [← fan.laurentRationalMap_coneLaurentMap 𝕜]
  change fan.laurentRationalMap 𝕜 regular nonempty
    (fan.coneLaurentMap 𝕜 _
      (MonoidAlgebra.single (Multiplicative.ofAdd
        ⟨normalizedResidueCharacter basis degree character, _⟩) 1)) = _
  rw [fan.coneLaurentMap_single 𝕜]
  exact fan.laurentRationalMap_characterMonomial 𝕜 regular nonempty _

omit [FiniteDimensional ℝ Ambient] in
theorem residueFloorChart_coordinate_rational (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (positive : 0 < degree)
    (character : Lattice →+ ℤ)
    (coefficient : affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.chartCoordinateGerm 𝕜) regular nonempty ⟨_, cone_basis⟩
      (fan.toricMultiplicationRing 𝕜 degree _ coefficient *
        fan.normalizedResidueMonomial 𝕜 basis positive character) =
      fan.toricMultiplicationFunctionField 𝕜 regular nonempty positive
        (fan.chartCoordinateGerm 𝕜 regular nonempty ⟨_, cone_basis⟩ coefficient *
          (fan.rationalCharacterUnit 𝕜 regular nonempty
            (-residueFloorCharacter basis degree character) :
              (fan.algebraicRealization 𝕜 regular).functionField)) *
        (fan.rationalCharacterUnit 𝕜 regular nonempty character :
          (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  rw [map_mul, fan.normalizedResidueMonomial_germ 𝕜,
    map_mul, fan.toricMultiplicationFunctionField_chartCoordinate 𝕜]
  have scaled := congrArg Units.val
    (fan.toricMultiplicationFunctionField_character 𝕜 regular nonempty positive
      (-residueFloorCharacter basis degree character))
  simp only [Units.coe_map, Units.val_pow_eq_pow_val] at scaled
  change fan.toricMultiplicationFunctionField 𝕜 regular nonempty positive
      (fan.rationalCharacterUnit 𝕜 regular nonempty (-residueFloorCharacter basis degree character) :
        (fan.algebraicRealization 𝕜 regular).functionField) = _ at scaled
  rw [scaled]
  have exponent : degree • (-residueFloorCharacter basis degree character) + character =
      normalizedResidueCharacter basis degree character := by
    simp only [normalizedResidueCharacter, smul_neg]
    abel
  have product := congrArg Units.val
    (fan.rationalCharacterUnit_add 𝕜 regular nonempty
      (degree • (-residueFloorCharacter basis degree character)) character)
  rw [fan.rationalCharacterUnit_nsmul 𝕜] at product
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, exponent] at product
  rw [mul_assoc, ← product]

omit [FiniteDimensional ℝ Ambient] in
theorem residueFloorEquation_normalized (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (positive : 0 < degree) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.toricMultiplicationFunctionField 𝕜) regular nonempty positive
      (fan.rationalCharacterUnit 𝕜 regular nonempty
        (residueFloorCharacter basis degree character) :
          (fan.algebraicRealization 𝕜 regular).functionField) *
      (fan.rationalCharacterUnit 𝕜 regular nonempty
        (normalizedResidueCharacter basis degree character) :
          (fan.algebraicRealization 𝕜 regular).functionField) =
      (fan.rationalCharacterUnit 𝕜 regular nonempty character :
        (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  have pulled := congrArg Units.val
    (fan.toricMultiplicationFunctionField_character 𝕜 regular nonempty positive
      (residueFloorCharacter basis degree character))
  change fan.toricMultiplicationFunctionField 𝕜 regular nonempty positive
      (fan.rationalCharacterUnit 𝕜 regular nonempty
        (residueFloorCharacter basis degree character) :
          (fan.algebraicRealization 𝕜 regular).functionField) =
    (fan.rationalCharacterUnit 𝕜 regular nonempty
      (residueFloorCharacter basis degree character) ^ degree :
        (fan.algebraicRealization 𝕜 regular).functionField) at pulled
  rw [pulled]
  rw [← Units.val_pow_eq_pow_val, ← fan.rationalCharacterUnit_nsmul 𝕜]
  have exponent : degree • residueFloorCharacter basis degree character +
      normalizedResidueCharacter basis degree character = character := by
    simp only [normalizedResidueCharacter]
    abel
  have product := congrArg Units.val
    (fan.rationalCharacterUnit_add 𝕜 regular nonempty
      (degree • residueFloorCharacter basis degree character)
      (normalizedResidueCharacter basis degree character))
  simpa only [Units.val_mul, exponent] using product.symm

omit [FiniteDimensional ℝ Ambient] in
theorem chartCoordinateGerm_mem_stalkRange (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (coordinate : affineCoordinateRing 𝕜 fan.lattice cone.val)
    (point : fan.algebraicRealization 𝕜 regular)
    (contains : point ∈ (fan.affineToricChartι 𝕜 regular cone).opensRange) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.chartCoordinateGerm 𝕜) regular nonempty cone coordinate ∈
      (algebraMap ((fan.algebraicRealization 𝕜 regular).presheaf.stalk point)
        (fan.algebraicRealization 𝕜 regular).functionField).range := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let : Nonempty (fan.affineToricChartι 𝕜 regular cone).opensRange := ⟨⟨point, contains⟩⟩
  refine ⟨(fan.algebraicRealization 𝕜 regular).presheaf.germ _ point contains
    (fan.chartCoordinateSectionsEquiv 𝕜 regular cone coordinate), ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField,
    ← fan.chartCoordinateGerm_sections 𝕜]

theorem residueFloorRational_mem_stalkRange (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (domain : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty domain]
    (regularSection : Γ((fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj, domain))
    (point : fan.algebraicRealization 𝕜 regular)
    (contains : point ∈ fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.toricMultiplicationFunctionField 𝕜) regular (fan.completeFan_nonemptyCones complete) positive
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
          (Scheme.Modules.Hom.app
            (fan.invariantDivisorCartier 𝕜 complete regular
              (fan.residueFloorDivisor degree character)).sheafι domain regularSection)) *
      (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) character :
        (fan.algebraicRealization 𝕜 regular).functionField) ∈
      (algebraMap ((fan.algebraicRealization 𝕜 regular).presheaf.stalk point)
        (fan.algebraicRealization 𝕜 regular).functionField).range := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let atlas := fan.residueFloorAtlas 𝕜 complete regular degree character
  obtain ⟨index, chart_contains⟩ := atlas.covers.exists_mem point
  have preserved := fan.toricMultiplication_preimage_chart_open 𝕜 regular positive (atlas.cone index)
  have image_contains : fan.toricMultiplication 𝕜 regular degree point ∈
      (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange := by
    change point ∈ fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ
      (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange
    rw [preserved]
    exact chart_contains
  let divisor := fan.invariantDivisorCartier 𝕜 complete regular
    (fan.residueFloorDivisor degree character)
  let equation := fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (-atlas.character index)
  have local_equation : divisor.IsLocalEquationAt
      (fan.toricMultiplication 𝕜 regular degree point) equation :=
    fan.invariantDivisorCartier_isLocalEquationAt 𝕜 complete regular
      (fan.residueFloorDivisor degree character) index _ image_contains
  have membership := divisor.sheafι_app_mem domain regularSection
  have local_regular := (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections.mp membership)
    (fan.toricMultiplication 𝕜 regular degree point) contains equation local_equation
  have pulled_regular := BondalThomsen.rationalPullback_mem_stalkRange
    (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive)
    point local_regular
  have generator_regular := fan.chartCoordinateGerm_mem_stalkRange 𝕜 regular
    (fan.completeFan_nonemptyCones complete) (atlas.cone index)
    (fan.normalizedResidueMonomial 𝕜
      (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2 positive character)
    point chart_contains
  have generator_germ := fan.normalizedResidueMonomial_germ 𝕜 regular
    (fan.completeFan_nonemptyCones complete)
    (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
    (fan.residueFloorChartBasis 𝕜 complete regular degree character index).property.1
    positive character
  have generator_germ' : fan.chartCoordinateGerm 𝕜 regular
      (fan.completeFan_nonemptyCones complete) (atlas.cone index)
      (fan.normalizedResidueMonomial 𝕜
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2 positive character) =
    (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
      (normalizedResidueCharacter
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2 degree character) :
        (fan.algebraicRealization 𝕜 regular).functionField) := generator_germ
  rw [generator_germ'] at generator_regular
  have product := (algebraMap ((fan.algebraicRealization 𝕜 regular).presheaf.stalk point)
    (fan.algebraicRealization 𝕜 regular).functionField).range.mul_mem pulled_regular generator_regular
  change fan.toricMultiplicationFunctionField 𝕜 regular
      (fan.completeFan_nonemptyCones complete) positive
      ((equation : (fan.algebraicRealization 𝕜 regular).functionField) *
        TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
          (Scheme.Modules.Hom.app divisor.sheafι domain regularSection)) *
    (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
      (normalizedResidueCharacter
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2 degree character) :
        (fan.algebraicRealization 𝕜 regular).functionField) ∈ _ at product
  have equation_eq : equation = fan.rationalCharacterUnit 𝕜 regular
      (fan.completeFan_nonemptyCones complete)
      (residueFloorCharacter
        (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2 degree character) := by
    dsimp only [equation, atlas]
    rw [fan.residueFloorAtlas_character 𝕜, neg_neg]
  rw [equation_eq, map_mul, mul_right_comm,
    fan.residueFloorEquation_normalized 𝕜] at product
  simpa only [mul_comm] using product

noncomputable def residueFloorRationalHom (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj ⟶
      (Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).obj
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions (fan.algebraicRealization 𝕜 regular)) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (fan.invariantDivisorCartier 𝕜 complete regular
      (fan.residueFloorDivisor degree character)).sheafι ≫
    BondalThomsen.rationalSheafToPushforward (fan.toricMultiplication 𝕜 regular degree)
      (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive) ≫
    (Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).map
      (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul (fan.algebraicRealization 𝕜 regular)
        (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) character :
          (fan.algebraicRealization 𝕜 regular).functionField))

theorem residueFloorRationalHom_value (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (domain : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty domain]
    (regularSection : Γ((fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj, domain)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    letI := BondalThomsen.rationalPullback_nonempty_preimage (fan.toricMultiplication 𝕜 regular degree)
      (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive) domain
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv
        (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain)
        (Scheme.Modules.Hom.app
          (fan.residueFloorRationalHom 𝕜 complete regular positive character) domain regularSection) =
      fan.toricMultiplicationFunctionField 𝕜 regular (fan.completeFan_nonemptyCones complete) positive
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
          (Scheme.Modules.Hom.app
            (fan.invariantDivisorCartier 𝕜 complete regular
              (fan.residueFloorDivisor degree character)).sheafι domain regularSection)) *
        (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) character :
          (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let := BondalThomsen.rationalPullback_nonempty_preimage (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive) domain
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _
    (Scheme.Modules.Hom.app
      (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul (fan.algebraicRealization 𝕜 regular)
        (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) character :
          (fan.algebraicRealization 𝕜 regular).functionField)) _
      (BondalThomsen.rationalSectionsPullback (fan.toricMultiplication 𝕜 regular degree)
        (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive)
        domain (Scheme.Modules.Hom.app
          (fan.invariantDivisorCartier 𝕜 complete regular
            (fan.residueFloorDivisor degree character)).sheafι domain regularSection))) = _
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
    BondalThomsen.rationalSectionsPullback_equiv]
  exact mul_comm _ _

theorem residueFloorRationalHom_in_range (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (domain : (fan.algebraicRealization 𝕜 regular).Opens)
    (regularSection : Γ((fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj, domain)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.residueFloorRationalHom 𝕜 complete regular positive character).val.app
      (op domain) regularSection ∈
      (((Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).map
          (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions
            (fan.algebraicRealization 𝕜 regular))).val.app (op domain)).hom.range := by
  classical
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  by_cases nonempty : Nonempty domain
  · let := nonempty
    let := BondalThomsen.rationalPullback_nonempty_preimage (fan.toricMultiplication 𝕜 regular degree)
      (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive) domain
    obtain ⟨coefficient, coefficient_eq⟩ :=
      TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range
        (fun point contains => fan.residueFloorRational_mem_stalkRange 𝕜
          complete regular positive character domain regularSection point contains)
    refine ⟨coefficient, ?_⟩
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _).injective
    change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _
      (Scheme.Modules.Hom.app
        (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions (fan.algebraicRealization 𝕜 regular))
        _ coefficient) = _
    rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app]
    change (fan.algebraicRealization 𝕜 regular).germToFunctionField _ coefficient =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv
        (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain)
        (Scheme.Modules.Hom.app
          (fan.residueFloorRationalHom 𝕜 complete regular positive character) domain regularSection)
    rw [fan.residueFloorRationalHom_value 𝕜]
    exact coefficient_eq
  · have empty : domain = ⊥ := by
      apply bot_unique
      intro point contains
      exact False.elim (nonempty ⟨⟨point, contains⟩⟩)
    have pulled_empty : fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain = ⊥ := by simp [empty]
    let := TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctions
      (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain) pulled_empty
    refine ⟨0, ?_⟩
    change (Scheme.Modules.Hom.app
      (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions (fan.algebraicRealization 𝕜 regular))
      (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain) 0) =
      (Scheme.Modules.Hom.app
        (fan.residueFloorRationalHom 𝕜 complete regular positive character) domain regularSection)
    exact Subsingleton.elim _ _

noncomputable def residueFloorGlobalInclusion (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ) :
    (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj ⟶
      fan.toricMultiplicationPushforward 𝕜 regular degree := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact BondalThomsen.residueFactorSheafHom
    (fan.residueFloorRationalHom 𝕜 complete regular positive character)
    ((Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).map
      (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions (fan.algebraicRealization 𝕜 regular)))
    (fun domain => TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions_app_injective
      (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain))
    (fan.residueFloorRationalHom_in_range 𝕜 complete regular positive character)

theorem residueFloorGlobalInclusion_rational (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.residueFloorGlobalInclusion 𝕜) complete regular positive character ≫
      (Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).map
        (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions (fan.algebraicRealization 𝕜 regular)) =
      fan.residueFloorRationalHom 𝕜 complete regular positive character := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact BondalThomsen.residueFactorSheafHom_inclusion _ _ _ _

theorem residueFloorGlobalInclusion_value (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (domain : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty domain]
    (regularSection : Γ((fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)).obj, domain)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    letI := BondalThomsen.rationalPullback_nonempty_preimage (fan.toricMultiplication 𝕜 regular degree)
      (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive) domain
    (fan.algebraicRealization 𝕜 regular).germToFunctionField
        (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain)
        (Scheme.Modules.Hom.app
          (fan.residueFloorGlobalInclusion 𝕜 complete regular positive character) domain regularSection) =
      fan.toricMultiplicationFunctionField 𝕜 regular (fan.completeFan_nonemptyCones complete) positive
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
          (Scheme.Modules.Hom.app
            (fan.invariantDivisorCartier 𝕜 complete regular
              (fan.residueFloorDivisor degree character)).sheafι domain regularSection)) *
        (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) character :
          (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let := BondalThomsen.rationalPullback_nonempty_preimage (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive) domain
  have factor := congrArg (fun comparison => Scheme.Modules.Hom.app comparison domain regularSection)
    (fan.residueFloorGlobalInclusion_rational 𝕜 complete regular positive character)
  change Scheme.Modules.Hom.app
      (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions (fan.algebraicRealization 𝕜 regular))
      (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ domain)
      (Scheme.Modules.Hom.app
        (fan.residueFloorGlobalInclusion 𝕜 complete regular positive character) domain regularSection) =
    Scheme.Modules.Hom.app
      (fan.residueFloorRationalHom 𝕜 complete regular positive character) domain regularSection at factor
  rw [← TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app,
    factor, fan.residueFloorRationalHom_value 𝕜]

theorem residueFloorFrame_section_rational (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ)
    (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index)
    (coefficient : Γ(fan.algebraicRealization 𝕜 regular,
      (fan.affineToricChartι 𝕜 regular
        ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)).opensRange)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let chart := (fan.affineToricChartι 𝕜 regular
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)).opensRange
    letI := fan.chartOpen_nonempty 𝕜 regular
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      (Scheme.Modules.Hom.app
        (fan.invariantDivisorCartier 𝕜 complete regular
          (fan.residueFloorDivisor degree character)).sheafι chart
        ((fan.residueFloorFrame 𝕜 complete regular degree character index).hom.val.app
          (op (Over.mk (𝟙 chart))) coefficient)) =
      (fan.algebraicRealization 𝕜 regular).germToFunctionField chart coefficient *
        (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-residueFloorCharacter
            (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
            degree character) : (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let chart := (fan.affineToricChartι 𝕜 regular
    ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular
    ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)
  dsimp only
  have frame := congrArg (fun comparison => comparison.val.app
    (op (Over.mk (𝟙 chart))) coefficient)
    (fan.residueFloorFrame_rational 𝕜 complete regular degree character index)
  change Scheme.Modules.Hom.app
      (fan.invariantDivisorCartier 𝕜 complete regular
        (fan.residueFloorDivisor degree character)).sheafι chart
      ((fan.residueFloorFrame 𝕜 complete regular degree character index).hom.val.app
        (op (Over.mk (𝟙 chart))) coefficient) = _ at frame
  rw [frame]
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      (Scheme.Modules.Hom.app
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul (fan.algebraicRealization 𝕜 regular)
          (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
            (-residueFloorCharacter
              (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
              degree character) : (fan.algebraicRealization 𝕜 regular).functionField)) chart
        (Scheme.Modules.Hom.app
          (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions (fan.algebraicRealization 𝕜 regular))
          chart coefficient)) = _
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app]
  exact mul_comm _ _

noncomputable def residueFloorChartMonomial (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index) :
    affineCoordinateRing 𝕜 fan.lattice
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index).val := by
  exact fan.normalizedResidueMonomial 𝕜
    (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2 positive character

theorem residueFloorGlobalInclusion_frame_sections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {degree : ℕ}
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (index : (fan.residueFloorAtlas 𝕜 complete regular degree character).Index)
    (coefficient : affineCoordinateRing 𝕜 fan.lattice
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index).val) :
    let chart := (fan.affineToricChartι 𝕜 regular
      ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)).opensRange
    Scheme.Modules.Hom.app
        (fan.residueFloorGlobalInclusion 𝕜 complete regular positive character) chart
        ((fan.residueFloorFrame 𝕜 complete regular degree character index).hom.val.app
          (op (Over.mk (𝟙 chart)))
          (fan.chartCoordinateSectionsEquiv 𝕜 regular
            ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index) coefficient)) =
      (fan.algebraicRealization 𝕜 regular).presheaf.map
        (homOfLE (fan.toricMultiplication_preimage_chart_open 𝕜 regular positive
          ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)).le).op
        (fan.chartCoordinateSectionsEquiv 𝕜 regular
          ((fan.residueFloorAtlas 𝕜 complete regular degree character).cone index)
          (fan.toricMultiplicationRing 𝕜 degree _ coefficient *
            fan.residueFloorChartMonomial 𝕜 complete regular positive character index)) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := (fan.residueFloorAtlas 𝕜 complete regular degree character).cone index
  let chart := (fan.affineToricChartι 𝕜 regular cone).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular cone
  let := BondalThomsen.rationalPullback_nonempty_preimage (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive) chart
  dsimp only
  apply (fan.algebraicRealization 𝕜 regular).germToFunctionField_injective
    (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ chart)
  rw [fan.residueFloorGlobalInclusion_value 𝕜, fan.residueFloorFrame_section_rational 𝕜]
  have restriction_germ := (fan.algebraicRealization 𝕜 regular).presheaf.germ_res_apply
    (homOfLE (fan.toricMultiplication_preimage_chart_open 𝕜 regular positive cone).le)
    (genericPoint (fan.algebraicRealization 𝕜 regular))
    (TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem
      (fan.toricMultiplication 𝕜 regular degree ⁻¹ᵁ chart))
    (fan.chartCoordinateSectionsEquiv 𝕜 regular cone
      (fan.toricMultiplicationRing 𝕜 degree _ coefficient *
        fan.residueFloorChartMonomial 𝕜 complete regular positive character index))
  change (fan.algebraicRealization 𝕜 regular).germToFunctionField _ _ =
    (fan.algebraicRealization 𝕜 regular).germToFunctionField _ _ at restriction_germ
  rw [restriction_germ]
  have normalized := fan.residueFloorChart_coordinate_rational 𝕜 regular
    (fan.completeFan_nonemptyCones complete)
    (fan.residueFloorChartBasis 𝕜 complete regular degree character index).val.2
    (fan.residueFloorChartBasis 𝕜 complete regular degree character index).property.1
    positive character coefficient
  have normalized' : fan.chartCoordinateGerm 𝕜 regular
      (fan.completeFan_nonemptyCones complete) cone
      (fan.toricMultiplicationRing 𝕜 degree _ coefficient *
        fan.residueFloorChartMonomial 𝕜 complete regular positive character index) = _ := normalized
  rw [fan.chartCoordinateGerm_sections 𝕜] at normalized'
  rw [← fan.chartCoordinateGerm_sections 𝕜 regular (fan.completeFan_nonemptyCones complete)
    cone coefficient]
  exact normalized'.symm

end TauCeti.Toric.Fan
