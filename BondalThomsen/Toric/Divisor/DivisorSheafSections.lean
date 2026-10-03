module

public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import BondalThomsen.Toric.Positivity.SupportGeneration
public import BondalThomsen.Toric.Positivity.GlobalSectionsFinite
public import BondalThomsen.Fan.CompleteFanGlobalFunctions

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.Toric Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def laurentRationalMap (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.LaurentCharacterAlgebra 𝕜) →+* (fan.algebraicRealization 𝕜 regular).functionField := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact (fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty)).comp
    (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm.toRingHom

theorem laurentRationalMap_injective (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) :
    Function.Injective (fan.laurentRationalMap 𝕜 regular nonempty) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.chartOpen_nonempty 𝕜 regular (fan.botCone nonempty)
  change Function.Injective (fun polynomial =>
    fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty)
      ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm polynomial))
  apply Function.Injective.comp _ (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm.injective
  change Function.Injective ((fan.algebraicRealization 𝕜 regular).germToFunctionField
    (fan.affineToricChartι 𝕜 regular (fan.botCone nonempty)).opensRange ∘
      fan.chartCoordinateSectionsEquiv 𝕜 regular (fan.botCone nonempty))
  exact ((fan.algebraicRealization 𝕜 regular).germToFunctionField_injective _).comp
    (fan.chartCoordinateSectionsEquiv 𝕜 regular (fan.botCone nonempty)).injective

theorem laurentRationalMap_coneLaurentMap (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (coordinate : affineCoordinateRing 𝕜 fan.lattice cone.val) :
    fan.laurentRationalMap 𝕜 regular nonempty (fan.coneLaurentMap 𝕜 cone.val coordinate) =
      fan.chartCoordinateGerm 𝕜 regular nonempty cone coordinate := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  rw [fan.chartCoordinateGerm_torus 𝕜 regular nonempty cone coordinate]
  have same := AlgHom.congr_fun (fan.denseTorusCoordinateRingEquiv_faceMap 𝕜 cone) coordinate
  change (denseTorusCoordinateRingEquiv 𝕜 fan.lattice)
    (faceAffineCoordinateRingMap 𝕜 fan.lattice
      ((fan.isToricCone cone.property).salient.bot_isFaceOf) coordinate) = _ at same
  change fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty)
    ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm (fan.coneLaurentMap 𝕜 cone.val coordinate)) = _
  rw [← same]
  exact congrArg (fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty))
    ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm_apply_apply _)

theorem laurentRationalMap_characterMonomial (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.laurentRationalMap 𝕜) regular nonempty (fan.characterLaurentMonomial 𝕜 character) =
      (fan.rationalCharacterUnit 𝕜 regular nonempty character :
        (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  have unit_same := fan.chartCoordinateGerm_monomialUnit 𝕜 regular nonempty
    (fan.botCone nonempty) character (by change character ∈ dualSemigroup fan.lattice ⊥; simp)
      (by change -character ∈ dualSemigroup fan.lattice ⊥; simp)
  have same := congrArg Units.val unit_same
  simp only [Units.coe_map] at same
  change fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty)
    (toricMonomialUnit 𝕜 fan.lattice (fan.botCone nonempty).val character _ _ :
      affineCoordinateRing 𝕜 fan.lattice (fan.botCone nonempty).val) = _ at same
  rw [← same]
  change fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty)
    ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm (fan.characterLaurentMonomial 𝕜 character)) = _
  apply congrArg (fan.chartCoordinateGerm 𝕜 regular nonempty (fan.botCone nonempty))
  apply (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).injective
  exact ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).apply_symm_apply _).trans
    (denseTorusCoordinateRingEquiv_single 𝕜 fan.lattice
      ⟨character, by simp⟩ 1).symm

theorem laurentRationalMap_coneCharacterSectionMap (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (character : Lattice →+ ℤ) (coordinate : affineCoordinateRing 𝕜 fan.lattice cone.val) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.laurentRationalMap 𝕜) regular nonempty
        (fan.coneCharacterSectionMap 𝕜 cone.val character coordinate) =
      fan.chartCoordinateGerm 𝕜 regular nonempty cone coordinate *
        (fan.rationalCharacterUnit 𝕜 regular nonempty character :
          (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  rw [coneCharacterSectionMap_eq_mul, map_mul, laurentRationalMap_coneLaurentMap,
    laurentRationalMap_characterMonomial]

noncomputable def laurentRationalSection (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (open_set : (fan.algebraicRealization 𝕜 regular).Opens)
    [Nonempty open_set] :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.LaurentCharacterAlgebra 𝕜) →+
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions (fan.algebraicRealization 𝕜 regular),
        open_set) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set).symm.toAddMonoidHom.comp
    (fan.laurentRationalMap 𝕜 regular nonempty).toAddMonoidHom

@[simp] theorem rationalFunctionsEquiv_laurentRationalSection (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    (open_set : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty open_set]
    (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set
        (fan.laurentRationalSection 𝕜 regular nonempty open_set polynomial) =
      fan.laurentRationalMap 𝕜 regular nonempty polynomial := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact LinearEquiv.apply_symm_apply _ _

variable [FiniteDimensional ℝ Ambient]

omit [FiniteDimensional ℝ Ambient] in

theorem chartCoordinateGerm_sections (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (coordinate : affineCoordinateRing 𝕜 fan.lattice cone.val) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    (fan.chartCoordinateGerm 𝕜) regular nonempty cone coordinate =
      (fan.algebraicRealization 𝕜 regular).germToFunctionField
        (fan.affineToricChartι 𝕜 regular cone).opensRange
        (fan.chartCoordinateSectionsEquiv 𝕜 regular cone coordinate) := by
  rfl

omit [FiniteDimensional ℝ Ambient] in

theorem laurentRationalSection_mem_cartierSections_iff (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) (character : Lattice →+ ℤ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    ∀ divisor : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor (fan.algebraicRealization 𝕜 regular),
      divisor |_ (fan.affineToricChartι 𝕜 regular cone).opensRange =
        TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
          (fan.affineToricChartι 𝕜 regular cone).opensRange
          (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular nonempty (-character))) →
      ∀ polynomial : fan.LaurentCharacterAlgebra 𝕜,
        fan.laurentRationalSection 𝕜 regular nonempty
            (fan.affineToricChartι 𝕜 regular cone).opensRange polynomial ∈
          divisor.sections (fan.affineToricChartι 𝕜 regular cone).opensRange ↔
        polynomial ∈ (fan.coneCharacterSectionMap 𝕜 cone.val character).range := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.chartOpen_nonempty 𝕜 regular cone
  intro divisor equation polynomial
  rw [TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq
    le_rfl equation.symm, rationalFunctionsEquiv_laurentRationalSection]
  constructor
  · rintro ⟨regular_section, same_germ⟩
    let coefficient := (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).symm regular_section
    refine ⟨coefficient, fan.laurentRationalMap_injective 𝕜 regular nonempty ?_⟩
    rw [fan.laurentRationalMap_coneCharacterSectionMap 𝕜 regular nonempty cone]
    have coefficient_germ : fan.chartCoordinateGerm 𝕜 regular nonempty cone coefficient =
        (fan.rationalCharacterUnit 𝕜 regular nonempty (-character) :
          (fan.algebraicRealization 𝕜 regular).functionField) *
            fan.laurentRationalMap 𝕜 regular nonempty polynomial := by
      rw [fan.chartCoordinateGerm_sections 𝕜 regular nonempty cone,
        show fan.chartCoordinateSectionsEquiv 𝕜 regular cone coefficient = regular_section from
          (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).apply_symm_apply _]
      exact same_germ
    rw [coefficient_germ, rationalCharacterUnit_neg]
    simp only [Units.val_inv_eq_inv_val]
    rw [mul_right_comm, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  · rintro ⟨coefficient, rfl⟩
    refine ⟨fan.chartCoordinateSectionsEquiv 𝕜 regular cone coefficient, ?_⟩
    rw [← fan.chartCoordinateGerm_sections 𝕜 regular nonempty cone,
      fan.laurentRationalMap_coneCharacterSectionMap 𝕜 regular nonempty cone,
      rationalCharacterUnit_neg]
    simp only [Units.val_inv_eq_inv_val]
    rw [mul_left_comm, inv_mul_cancel₀ (Units.ne_zero _), mul_one]

noncomputable def divisorSectionChartBasis (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (index : Fin (Nat.card fan.cones)) :=
  fan.divisorChartBasis complete regular ((Finite.equivFin fan.cones).symm index)

noncomputable def divisorChartLaurentSectionSpace (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) : Submodule 𝕜 (fan.LaurentCharacterAlgebra 𝕜) :=
  (fan.coneCharacterSectionMap 𝕜 (fan.divisorLocalCone 𝕜 complete regular index).val
    (fan.divisorLocalCharacter 𝕜 complete regular divisor index)).range

theorem invariantDivisorCartier_chartSections_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    letI := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
    (fan.laurentRationalSection 𝕜) regular (fan.completeFan_nonemptyCones complete)
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
        polynomial ∈ (fan.invariantDivisorCartier 𝕜 complete regular divisor).sections
          (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange ↔
      polynomial ∈ fan.divisorChartLaurentSectionSpace 𝕜 complete regular divisor index :=
  fan.laurentRationalSection_mem_cartierSections_iff 𝕜 regular
    (fan.completeFan_nonemptyCones complete) (fan.divisorLocalCone 𝕜 complete regular index)
    (fan.divisorLocalCharacter 𝕜 complete regular divisor index) _
    (fan.invariantDivisorCartier_localEquation 𝕜 complete regular divisor index) polynomial

theorem mem_divisorChartLaurentSectionSpace_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    polynomial ∈ fan.divisorChartLaurentSectionSpace 𝕜 complete regular divisor index ↔
      polynomial ∈ fan.divisorLaurentSectionSpace 𝕜
        (fan.divisorLocalCone 𝕜 complete regular index).val divisor := by
  let basis_data := fan.divisorSectionChartBasis complete regular index
  exact fan.mem_coneDivisorSectionModule_iff 𝕜 basis_data.val.2 basis_data.property.1
    divisor polynomial

theorem divisorLocalCone_covers_rays (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (ray : fan.Ray) :
    ∃ index : Fin (Nat.card fan.cones),
      embedding ray.val ∈ (fan.divisorLocalCone 𝕜 complete regular index).val := by
  let original : fan.cones := ⟨ℝ ∙₊ embedding ray.val, ray.property.2⟩
  let index := (Finite.equivFin fan.cones) original
  refine ⟨index, ?_⟩
  change embedding ray.val ∈ (fan.divisorChartCone complete regular
    ((Finite.equivFin fan.cones).symm index)).val
  rw [show (Finite.equivFin fan.cones).symm index = original from
    (Finite.equivFin fan.cones).symm_apply_apply original]
  exact (fan.divisorChartBasis complete regular original).property.2.le
    (PointedCone.subset_hull (Set.mem_singleton _))

theorem mem_globalDivisorLaurentSectionSpace_iff_divisorCharts (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    polynomial ∈ fan.globalDivisorLaurentSectionSpace 𝕜 divisor ↔
      ∀ index : Fin (Nat.card fan.cones),
        polynomial ∈ fan.divisorChartLaurentSectionSpace 𝕜 complete regular divisor index := by
  constructor
  · intro member index
    exact (fan.mem_divisorChartLaurentSectionSpace_iff 𝕜 complete regular divisor index polynomial).mpr
      (fan.globalDivisorLaurentSectionSpace_le_cone 𝕜 _ divisor member)
  · intro local_members
    rw [mem_globalDivisorLaurentSectionSpace_iff]
    intro exponent contains ray
    obtain ⟨index, ray_contains⟩ := fan.divisorLocalCone_covers_rays 𝕜 complete regular ray
    exact (fan.mem_divisorLaurentSectionSpace_iff 𝕜 _ divisor polynomial).mp
      ((fan.mem_divisorChartLaurentSectionSpace_iff 𝕜 complete regular divisor index polynomial).mp
        (local_members index)) exponent contains ray ray_contains

omit [FiniteDimensional ℝ Ambient] in

theorem laurentRationalSection_restrict (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    ∀ (open_set : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty open_set]
      (polynomial : fan.LaurentCharacterAlgebra 𝕜),
      (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions (fan.algebraicRealization 𝕜 regular)).presheaf.map
          (homOfLE (show open_set ≤ ⊤ from le_top)).op
          (fan.laurentRationalSection 𝕜 regular nonempty ⊤ polynomial) =
        fan.laurentRationalSection 𝕜 regular nonempty open_set polynomial := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  intro open_set nonempty_open polynomial
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set).injective
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map,
    rationalFunctionsEquiv_laurentRationalSection, rationalFunctionsEquiv_laurentRationalSection]

theorem laurentRationalSection_mem_invariantDivisorSections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (polynomial : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.laurentRationalSection 𝕜) regular (fan.completeFan_nonemptyCones complete) ⊤ polynomial.val ∈
      (fan.invariantDivisorCartier 𝕜 complete regular divisor).sections ⊤ := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  apply TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections_iff_exists.mpr
  intro point _
  have covered : point ∈ ⨆ index,
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange := by
    change point ∈ ⨆ index,
      (fan.affineToricChartι 𝕜 regular
        ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).cone index)).opensRange
    rw [(fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).covers.iSup_eq_top]
    trivial
  obtain ⟨index, contains⟩ := Opens.mem_iSup.mp covered
  let chart := (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  have local_member := (fan.invariantDivisorCartier_chartSections_iff 𝕜 complete regular
    divisor index polynomial.val).mpr
      ((fan.mem_globalDivisorLaurentSectionSpace_iff_divisorCharts 𝕜 complete regular
        divisor polynomial.val).mp polynomial.property index)
  let equation := fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (-fan.divisorLocalCharacter 𝕜 complete regular divisor index)
  have local_equation : (fan.invariantDivisorCartier 𝕜 complete regular divisor).IsLocalEquationAt
      point equation :=
    fan.invariantDivisorCartier_isLocalEquationAt 𝕜 complete regular divisor index point contains
  refine ⟨equation, local_equation, ?_⟩
  have member_value := local_member point contains equation local_equation
  rw [rationalFunctionsEquiv_laurentRationalSection] at member_value ⊢
  exact member_value

theorem invariantDivisorSections_existsUnique_laurent (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    ∀ rational_section : Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions
        (fan.algebraicRealization 𝕜 regular), ⊤),
      rational_section ∈ (fan.invariantDivisorCartier 𝕜 complete regular divisor).sections ⊤ →
      ∃! polynomial : fan.globalDivisorLaurentSectionSpace 𝕜 divisor,
        fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤ polynomial.val =
          rational_section := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  intro rational_section member
  let original : fan.cones := Classical.choice (fan.completeFan_nonemptyCones complete)
  let index := (Finite.equivFin fan.cones) original
  let cone := fan.divisorLocalCone 𝕜 complete regular index
  let chart := (fan.affineToricChartι 𝕜 regular cone).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular cone
  let restricted := (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions
    (fan.algebraicRealization 𝕜 regular)).presheaf.map (homOfLE (show chart ≤ ⊤ from le_top)).op
      rational_section
  have local_member : restricted ∈ (fan.invariantDivisorCartier 𝕜 complete regular divisor).sections chart :=
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sections_map (homOfLE le_top) member
  obtain ⟨regular_section, coefficient_equation⟩ :=
    (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq
      le_rfl (fan.invariantDivisorCartier_localEquation 𝕜 complete regular divisor index).symm).mp
        local_member
  let coefficient := (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).symm regular_section
  let polynomial := fan.coneCharacterSectionMap 𝕜 cone.val
    (fan.divisorLocalCharacter 𝕜 complete regular divisor index) coefficient
  have polynomial_value : fan.laurentRationalMap 𝕜 regular (fan.completeFan_nonemptyCones complete)
      polynomial = TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤ rational_section := by
    rw [fan.laurentRationalMap_coneCharacterSectionMap 𝕜 regular _ cone]
    have coefficient_germ : fan.chartCoordinateGerm 𝕜 regular (fan.completeFan_nonemptyCones complete)
        cone coefficient = _ := (fan.chartCoordinateGerm_sections 𝕜 regular _ cone coefficient).trans
      (congrArg ((fan.algebraicRealization 𝕜 regular).germToFunctionField chart)
        ((fan.chartCoordinateSectionsEquiv 𝕜 regular cone).apply_symm_apply regular_section))
    rw [coefficient_germ, coefficient_equation,
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map,
      rationalCharacterUnit_neg]
    simp only [Units.val_inv_eq_inv_val]
    rw [mul_right_comm, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  have polynomial_section : fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete)
      ⊤ polynomial = rational_section := by
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤).injective
    rw [rationalFunctionsEquiv_laurentRationalSection]
    exact polynomial_value
  have global_member : polynomial ∈ fan.globalDivisorLaurentSectionSpace 𝕜 divisor := by
    rw [fan.mem_globalDivisorLaurentSectionSpace_iff_divisorCharts 𝕜 complete regular divisor polynomial]
    intro other_index
    let other_cone := fan.divisorLocalCone 𝕜 complete regular other_index
    let other_chart := (fan.affineToricChartι 𝕜 regular other_cone).opensRange
    let := fan.chartOpen_nonempty 𝕜 regular other_cone
    apply (fan.invariantDivisorCartier_chartSections_iff 𝕜 complete regular divisor other_index polynomial).mp
    have restricted_member := TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sections_map
      (homOfLE (show other_chart ≤ ⊤ from le_top)) member
    rw [← polynomial_section, fan.laurentRationalSection_restrict 𝕜] at restricted_member
    exact restricted_member
  refine ⟨⟨polynomial, global_member⟩, polynomial_section, ?_⟩
  intro other same_section
  apply Subtype.ext
  apply fan.laurentRationalMap_injective 𝕜 regular (fan.completeFan_nonemptyCones complete)
  have same_value := congrArg (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤)
    (same_section.trans polynomial_section.symm)
  simpa only [rationalFunctionsEquiv_laurentRationalSection] using same_value

noncomputable def globalDivisorLaurentToSheafSections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    fan.globalDivisorLaurentSectionSpace 𝕜 divisor →+
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, ⊤) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact {
    toFun := fun polynomial => TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sectionMk
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤ polynomial.val)
      (fan.laurentRationalSection_mem_invariantDivisorSections 𝕜 complete regular divisor polynomial)
    map_zero' := by apply Subtype.ext; exact map_zero _
    map_add' := fun first second => by apply Subtype.ext; exact map_add _ _ _ }

theorem globalDivisorLaurentToSheafSections_bijective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    Function.Bijective (fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  constructor
  · intro first second same
    apply Subtype.ext
    apply fan.laurentRationalMap_injective 𝕜 regular (fan.completeFan_nonemptyCones complete)
    have rational_same := congrArg (fun section_value =>
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤
        (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι ⊤
          section_value)) same
    change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤
        (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤ first.val) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤
        (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤ second.val)
      at rational_same
    simpa only [rationalFunctionsEquiv_laurentRationalSection] using rational_same
  · intro section_value
    let rational_section := Scheme.Modules.Hom.app
      (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι ⊤ section_value
    have member := (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_mem ⊤ section_value
    obtain ⟨polynomial, same, _⟩ :=
      fan.invariantDivisorSections_existsUnique_laurent 𝕜 complete regular divisor rational_section member
    refine ⟨polynomial, ?_⟩
    apply (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_injective ⊤
    exact same

variable {𝕜} in
noncomputable instance invariantDivisorGlobalSectionsScalarModule (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    Module 𝕜 Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, ⊤) :=
  Module.compHom _ (fan.scalarGlobalSections 𝕜 regular)

omit [FiniteDimensional ℝ Ambient] in

theorem chartCoordinateGerm_chartGlobalSections (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (regular_section : Γ(fan.algebraicRealization 𝕜 regular, ⊤)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.chartCoordinateGerm 𝕜) regular nonempty cone
        (fan.chartGlobalSections 𝕜 regular cone regular_section) =
      (fan.algebraicRealization 𝕜 regular).germToFunctionField ⊤ regular_section := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.chartOpen_nonempty 𝕜 regular cone
  have restriction := BondalThomsen.openImmersion_sectionsIso_appLE
    (fan.affineToricChartι 𝕜 regular cone) ⊤ (by simp)
  have same_sections : fan.chartCoordinateSectionsEquiv 𝕜 regular cone
      (fan.chartGlobalSections 𝕜 regular cone regular_section) =
        (fan.algebraicRealization 𝕜 regular).presheaf.map (homOfLE le_top).op regular_section := by
    have same := ConcreteCategory.congr_hom restriction regular_section
    have top_app : (fan.affineToricChartι 𝕜 regular cone).appLE ⊤ ⊤ (by simp) =
        (fan.affineToricChartι 𝕜 regular cone).appTop :=
      (fan.affineToricChartι 𝕜 regular cone).appLE_eq_app
    rw [top_app] at same
    change (IsOpenImmersion.ΓIsoTop (fan.affineToricChartι 𝕜 regular cone)).hom
      ((Scheme.ΓSpecIso _).inv ((Scheme.ΓSpecIso _).hom
        ((fan.affineToricChartι 𝕜 regular cone).appTop regular_section))) = _
    simpa only [Iso.hom_inv_id_apply, ConcreteCategory.comp_apply] using same
  rw [fan.chartCoordinateGerm_sections 𝕜 regular nonempty cone, same_sections]
  exact (fan.algebraicRealization 𝕜 regular).presheaf.Γgerm_res_apply _ _ _

omit [FiniteDimensional ℝ Ambient] in

theorem laurentRationalMap_smul (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (coefficient : 𝕜) (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.laurentRationalMap 𝕜) regular nonempty (coefficient • polynomial) =
      (fan.algebraicRealization 𝕜 regular).germToFunctionField ⊤
          (fan.scalarGlobalSections 𝕜 regular coefficient) *
        fan.laurentRationalMap 𝕜 regular nonempty polynomial := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  rw [Algebra.smul_def, map_mul]
  congr 1
  have scalar_chart := fan.chartGlobalSections_scalarGlobalSections 𝕜 regular
    (fan.botCone nonempty) coefficient
  have scalar_laurent : fan.coneLaurentMap 𝕜 (fan.botCone nonempty).val
      (fan.chartGlobalSections 𝕜 regular (fan.botCone nonempty)
        (fan.scalarGlobalSections 𝕜 regular coefficient)) =
          algebraMap 𝕜 (fan.LaurentCharacterAlgebra 𝕜) coefficient := by
    rw [scalar_chart]
    exact (fan.coneLaurentMap 𝕜 _).commutes coefficient
  rw [← scalar_laurent, fan.laurentRationalMap_coneLaurentMap 𝕜 regular nonempty,
    fan.chartCoordinateGerm_chartGlobalSections 𝕜 regular nonempty]

theorem globalDivisorLaurentToSheafSections_smul (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (coefficient : 𝕜) (polynomial : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor (coefficient • polynomial) =
      coefficient • fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor polynomial := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  apply (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_injective ⊤
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤).injective
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤
        (coefficient • polynomial.val)) =
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤
      (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι ⊤
        ((fan.scalarGlobalSections 𝕜 regular coefficient) •
          fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor polynomial))
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤
        (coefficient • polynomial.val)) =
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤
      ((fan.scalarGlobalSections 𝕜 regular coefficient) •
        fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤ polynomial.val)
  rw [(TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv ⊤).map_smul
      (fan.scalarGlobalSections 𝕜 regular coefficient),
    rationalFunctionsEquiv_laurentRationalSection,
    rationalFunctionsEquiv_laurentRationalSection, fan.laurentRationalMap_smul 𝕜 regular _]
  rfl

noncomputable def invariantDivisorSheafGlobalSectionsEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    fan.globalDivisorLaurentSectionSpace 𝕜 divisor ≃ₗ[𝕜]
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, ⊤) :=
  LinearEquiv.ofBijective
    { fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor with
      map_smul' := fan.globalDivisorLaurentToSheafSections_smul 𝕜 complete regular divisor }
    (fan.globalDivisorLaurentToSheafSections_bijective 𝕜 complete regular divisor)

noncomputable def invariantDivisorSheafRestrictGlobal (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (open_set : (fan.algebraicRealization 𝕜 regular).Opens) :
    Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, ⊤) →+
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, open_set) :=
  ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map
    (homOfLE (show open_set ≤ ⊤ from le_top)).op).hom

theorem invariantDivisorSheafRestrictGlobal_rationalValue (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (open_set : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty open_set]
    (polynomial : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set
        (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι open_set
          (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
            (fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor polynomial))) =
      fan.laurentRationalMap 𝕜 regular (fan.completeFan_nonemptyCones complete) polynomial.val := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set
    ((TauCeti.AlgebraicGeometry.Scheme.rationalFunctions (fan.algebraicRealization 𝕜 regular)).presheaf.map
      (homOfLE (show open_set ≤ ⊤ from le_top)).op
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤ polynomial.val)) = _
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map,
    rationalFunctionsEquiv_laurentRationalSection]

theorem invariantDivisorSheaf_chartRegularCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let cone := fan.divisorLocalCone 𝕜 complete regular index
    let chart := (fan.affineToricChartι 𝕜 regular cone).opensRange
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    ∀ section_value : Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, chart),
      ∃ coefficient : Γ(fan.algebraicRealization 𝕜 regular, chart),
        (fan.algebraicRealization 𝕜 regular).germToFunctionField chart coefficient =
          (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
              (-fan.divisorLocalCharacter 𝕜 complete regular divisor index) :
            (fan.algebraicRealization 𝕜 regular).functionField) *
            TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
              (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι
                chart section_value) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  dsimp only
  intro section_value
  exact (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq
    le_rfl (fan.invariantDivisorCartier_localEquation 𝕜 complete regular divisor index).symm).mp
      ((fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_mem _ section_value)

theorem divisorLocalCharacter_monomial_mem_global (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (index : Fin (Nat.card fan.cones)) :
    fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor index) ∈
      fan.globalDivisorLaurentSectionSpace 𝕜 divisor := by
  rw [fan.characterLaurentMonomial_mem_global_iff 𝕜]
  let basis_data := fan.divisorSectionChartBasis complete regular index
  exact support basis_data.val.1 basis_data.val.2 basis_data.property.1

noncomputable def invariantDivisorSheafGlobalChartGenerator (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (index : Fin (Nat.card fan.cones)) :
    Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, ⊤) :=
  fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor
    ⟨fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor index),
      fan.divisorLocalCharacter_monomial_mem_global 𝕜 complete regular divisor support index⟩

theorem invariantDivisorSheaf_subchart_generated_by_global (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (index : Fin (Nat.card fan.cones))
    (open_set : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty open_set]
    (contained : open_set ≤
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange)
    (section_value : Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, open_set)) :
    ∃ coefficient : Γ(fan.algebraicRealization 𝕜 regular, open_set),
      coefficient • fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support index) =
          section_value := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  have member := (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_mem open_set section_value
  obtain ⟨coefficient, equation⟩ :=
    (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq
      contained (fan.invariantDivisorCartier_localEquation 𝕜 complete regular divisor index).symm).mp member
  refine ⟨coefficient, ?_⟩
  apply (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_injective open_set
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set).injective
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set
      (coefficient • Scheme.Modules.Hom.app
        (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι open_set
        (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
          (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support index))) = _
  rw [(TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set).map_smul coefficient]
  change (fan.algebraicRealization 𝕜 regular).germToFunctionField open_set coefficient * _ = _
  have generator_value := fan.invariantDivisorSheafRestrictGlobal_rationalValue 𝕜 complete regular
    divisor open_set
    ⟨fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor index),
      fan.divisorLocalCharacter_monomial_mem_global 𝕜 complete regular divisor support index⟩
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set
      (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι open_set
        (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
          (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support index))) =
    fan.laurentRationalMap 𝕜 regular (fan.completeFan_nonemptyCones complete)
      (fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor index))
    at generator_value
  rw [fan.laurentRationalMap_characterMonomial 𝕜 regular _] at generator_value
  exact (congrArg (((fan.algebraicRealization 𝕜 regular).germToFunctionField open_set coefficient) * ·)
    generator_value).trans (by
    rw [equation, rationalCharacterUnit_neg]
    simp only [Units.val_inv_eq_inv_val]
    rw [mul_right_comm, inv_mul_cancel₀ (Units.ne_zero _), one_mul])

noncomputable def invariantDivisorSheafGeneratorFamily (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (index : Fin (Nat.card fan.cones)) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.sections :=
  PresheafOfModules.sectionsMk
    (fun open_set => (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.val.map
      (homOfLE (show open_set.unop ≤ ⊤ from le_top)).op
      (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support index))
    (by
      intro first second inclusion
      exact (PresheafOfModules.map_comp_apply
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.val
        (homOfLE (show first.unop ≤ ⊤ from le_top)).op inclusion
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support index)).symm.trans
          (by congr 1))

noncomputable def invariantDivisorSheafEvaluation (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) :
    SheafOfModules.free (R := (fan.algebraicRealization 𝕜 regular).ringCatSheaf)
      (Fin (Nat.card fan.cones)) ⟶ (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj :=
  (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.freeHomEquiv.symm
    (fan.invariantDivisorSheafGeneratorFamily 𝕜 complete regular divisor support)

theorem invariantDivisorSheafEvaluation_cancel_on_subchart (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor)
    (target : (fan.algebraicRealization 𝕜 regular).Modules)
    (first second : (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ⟶ target)
    (same_evaluation : fan.invariantDivisorSheafEvaluation 𝕜 complete regular divisor support ≫ first =
      fan.invariantDivisorSheafEvaluation 𝕜 complete regular divisor support ≫ second)
    (index : Fin (Nat.card fan.cones))
    (open_set : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty open_set]
    (contained : open_set ≤
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange)
    (section_value : Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, open_set)) :
    Scheme.Modules.Hom.app first open_set section_value =
      Scheme.Modules.Hom.app second open_set section_value := by
  have same_family := congrArg (fun morphism => target.freeHomEquiv morphism index) same_evaluation
  have first_family := SheafOfModules.freeHomEquiv_comp_apply
    (fan.invariantDivisorSheafEvaluation 𝕜 complete regular divisor support) first index
  have second_family := SheafOfModules.freeHomEquiv_comp_apply
    (fan.invariantDivisorSheafEvaluation 𝕜 complete regular divisor support) second index
  have same_generators := first_family.symm.trans (same_family.trans second_family)
  change SheafOfModules.sectionsMap first
      (((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.freeHomEquiv)
        (((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.freeHomEquiv).symm
          (fan.invariantDivisorSheafGeneratorFamily 𝕜 complete regular divisor support)) index) =
    SheafOfModules.sectionsMap second
      (((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.freeHomEquiv)
        (((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.freeHomEquiv).symm
          (fan.invariantDivisorSheafGeneratorFamily 𝕜 complete regular divisor support)) index)
    at same_generators
  simp only [Equiv.apply_symm_apply] at same_generators
  have generator_same := congrArg (fun family => family.val (op open_set)) same_generators
  change Scheme.Modules.Hom.app first open_set
      (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support index)) =
    Scheme.Modules.Hom.app second open_set
      (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support index))
    at generator_same
  obtain ⟨coefficient, same_section⟩ := fan.invariantDivisorSheaf_subchart_generated_by_global 𝕜
    complete regular divisor support index open_set contained section_value
  rw [← same_section, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, generator_same]

theorem invariantDivisorSheafEvaluation_epi (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) :
    Epi (fan.invariantDivisorSheafEvaluation 𝕜 complete regular divisor support) := by
  constructor
  intro target first second same_evaluation
  apply Scheme.Modules.hom_ext
  intro open_set
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro section_value
  let chart := fun index : Fin (Nat.card fan.cones) =>
    (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
  let Index := {index : Fin (Nat.card fan.cones) // Nonempty ↥(open_set ⊓ chart index)}
  let cover := fun index : Index => open_set ⊓ chart index.val
  have covers : open_set ≤ ⨆ index : Index, cover index := by
    intro point contains
    have on_charts : point ∈ ⨆ index, chart index := by
      change point ∈ ⨆ index,
        (fan.affineToricChartι 𝕜 regular
          ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).cone index)).opensRange
      rw [(fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).covers.iSup_eq_top]
      trivial
    obtain ⟨index, chart_contains⟩ := Opens.mem_iSup.mp on_charts
    exact Opens.mem_iSup.mpr ⟨⟨index, ⟨⟨point, contains, chart_contains⟩⟩⟩,
      ⟨contains, chart_contains⟩⟩
  let target_sheaf : TopCat.Sheaf AddCommGrpCat (fan.algebraicRealization 𝕜 regular) :=
    ⟨Scheme.Modules.presheaf target, Scheme.Modules.isSheaf target⟩
  apply target_sheaf.eq_of_locally_eq' cover open_set
    (fun _ => homOfLE inf_le_left) covers
  intro index
  let : Nonempty (cover index) := index.property
  have local_same := fan.invariantDivisorSheafEvaluation_cancel_on_subchart 𝕜 complete regular
    divisor support target first second same_evaluation index.val (cover index) inf_le_right
      ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map
        (homOfLE (show cover index ≤ open_set from inf_le_left)).op section_value)
  have first_natural := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf first).naturality
      (homOfLE (show cover index ≤ open_set from inf_le_left)).op)
      section_value
  have second_natural := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf second).naturality
      (homOfLE (show cover index ≤ open_set from inf_le_left)).op)
      section_value
  exact first_natural.symm.trans (local_same.trans second_natural)

noncomputable def invariantDivisorSheafGeneratingSections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.GeneratingSections where
  I := Fin (Nat.card fan.cones)
  s := fan.invariantDivisorSheafGeneratorFamily 𝕜 complete regular divisor support
  epi := fan.invariantDivisorSheafEvaluation_epi 𝕜 complete regular divisor support

variable {𝕜} in
instance invariantDivisorSheafGeneratingSections_isFiniteType (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) :
    (fan.invariantDivisorSheafGeneratingSections 𝕜 complete regular divisor support).IsFiniteType where
  finite := inferInstanceAs (Finite (Fin (Nat.card fan.cones)))

noncomputable def divisorChartLaurentToSheafSections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    fan.divisorChartLaurentSectionSpace 𝕜 complete regular divisor index →+
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  letI := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  exact {
    toFun := fun polynomial => TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sectionMk
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
        polynomial.val)
      ((fan.invariantDivisorCartier_chartSections_iff 𝕜 complete regular divisor index polynomial.val).mpr
        polynomial.property)
    map_zero' := by apply Subtype.ext; exact map_zero _
    map_add' := fun first second => by apply Subtype.ext; exact map_add _ _ _ }

theorem divisorChartLaurentToSheafSections_bijective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    Function.Bijective (fan.divisorChartLaurentToSheafSections 𝕜 complete regular divisor index) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := fan.divisorLocalCone 𝕜 complete regular index
  let chart := (fan.affineToricChartι 𝕜 regular cone).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular cone
  constructor
  · intro first second same
    apply Subtype.ext
    apply fan.laurentRationalMap_injective 𝕜 regular (fan.completeFan_nonemptyCones complete)
    have rational_same := congrArg (fun section_value =>
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
        (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι chart
          section_value)) same
    change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
        (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) chart first.val) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
        (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) chart second.val)
      at rational_same
    simpa only [rationalFunctionsEquiv_laurentRationalSection] using rational_same
  · intro section_value
    obtain ⟨regular_coefficient, coefficient_equation⟩ :=
      fan.invariantDivisorSheaf_chartRegularCoefficient 𝕜 complete regular divisor index section_value
    let coefficient := (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).symm regular_coefficient
    let polynomial := fan.coneCharacterSectionMap 𝕜 cone.val
      (fan.divisorLocalCharacter 𝕜 complete regular divisor index) coefficient
    have member : polynomial ∈ fan.divisorChartLaurentSectionSpace 𝕜 complete regular divisor index :=
      ⟨coefficient, rfl⟩
    refine ⟨⟨polynomial, member⟩, ?_⟩
    apply (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_injective chart
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart).injective
    change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
        (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) chart polynomial) = _
    rw [rationalFunctionsEquiv_laurentRationalSection,
      fan.laurentRationalMap_coneCharacterSectionMap 𝕜 regular _ cone]
    have coefficient_germ : fan.chartCoordinateGerm 𝕜 regular (fan.completeFan_nonemptyCones complete)
        cone coefficient = (fan.algebraicRealization 𝕜 regular).germToFunctionField chart
          regular_coefficient :=
      (fan.chartCoordinateGerm_sections 𝕜 regular _ cone coefficient).trans
        (congrArg ((fan.algebraicRealization 𝕜 regular).germToFunctionField chart)
          ((fan.chartCoordinateSectionsEquiv 𝕜 regular cone).apply_symm_apply regular_coefficient))
    rw [coefficient_germ, coefficient_equation, rationalCharacterUnit_neg]
    simp only [Units.val_inv_eq_inv_val]
    rw [mul_right_comm, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

noncomputable def invariantDivisorSheafChartSectionsEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    fan.divisorChartLaurentSectionSpace 𝕜 complete regular divisor index ≃+
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange) :=
  AddEquiv.ofBijective (fan.divisorChartLaurentToSheafSections 𝕜 complete regular divisor index)
    (fan.divisorChartLaurentToSheafSections_bijective 𝕜 complete regular divisor index)

theorem globalDivisorLaurentToSheafSections_on_chart (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) (polynomial : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
        (fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor polynomial) =
      fan.divisorChartLaurentToSheafSections 𝕜 complete regular divisor index
        ⟨polynomial.val,
          (fan.mem_globalDivisorLaurentSectionSpace_iff_divisorCharts 𝕜 complete regular divisor
            polynomial.val).mp polynomial.property index⟩ := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := fan.divisorLocalCone 𝕜 complete regular index
  let chart := (fan.affineToricChartι 𝕜 regular cone).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular cone
  apply (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_injective chart
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart).injective
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      ((TauCeti.AlgebraicGeometry.Scheme.rationalFunctions (fan.algebraicRealization 𝕜 regular)).presheaf.map
        (homOfLE le_top).op
        (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) ⊤ polynomial.val)) =
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) chart polynomial.val)
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map,
    rationalFunctionsEquiv_laurentRationalSection, rationalFunctionsEquiv_laurentRationalSection]

end TauCeti.Toric.Fan
