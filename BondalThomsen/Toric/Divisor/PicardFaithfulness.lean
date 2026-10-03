module

public import BondalThomsen.Toric.Divisor.CartierFaithfulness
public import BondalThomsen.Toric.Scheme.LaurentUnits
public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.LineBundle.CartierDivisorPrincipalKernel

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def rationalScalarUnit (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (scalar : 𝕜ˣ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.algebraicRealization 𝕜 regular).functionFieldˣ := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact Units.map ((fan.algebraicRealization 𝕜 regular).germToFunctionField ⊤).hom
    (Units.map (fan.scalarGlobalSections 𝕜 regular).toMonoidHom scalar)

theorem principalCartierDivisor_rationalScalarUnit (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) (scalar : 𝕜ˣ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor (fan.algebraicRealization 𝕜 regular)
      (fan.rationalScalarUnit 𝕜 regular nonempty scalar) = 0 := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  exact TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_regularUnitToFunctionField
    (fan.algebraicRealization 𝕜 regular) _

theorem laurentRationalMap_single (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (character : Lattice →+ ℤ) (coefficient : 𝕜) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (fan.laurentRationalMap 𝕜) regular nonempty (MonoidAlgebra.single (ofAdd character) coefficient) =
      (fan.algebraicRealization 𝕜 regular).germToFunctionField ⊤
          (fan.scalarGlobalSections 𝕜 regular coefficient) *
        (fan.rationalCharacterUnit 𝕜 regular nonempty character).val := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  have monomial : (MonoidAlgebra.single (ofAdd character) coefficient :
      fan.LaurentCharacterAlgebra 𝕜) = coefficient • fan.characterLaurentMonomial 𝕜 character := by
    simp [characterLaurentMonomial]
  rw [monomial, fan.laurentRationalMap_smul 𝕜 regular nonempty,
    fan.laurentRationalMap_characterMonomial 𝕜 regular nonempty]

theorem laurentRationalUnit_eq_scalar_character (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    (unit : (fan.LaurentCharacterAlgebra 𝕜)ˣ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    ∃ character : Lattice →+ ℤ, ∃ scalar : 𝕜ˣ,
      Units.map (fan.laurentRationalMap 𝕜 regular nonempty).toMonoidHom unit =
        fan.rationalScalarUnit 𝕜 regular nonempty scalar *
          fan.rationalCharacterUnit 𝕜 regular nonempty character := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  obtain ⟨character, coefficient, nonzero, same⟩ := fan.laurentUnit_eq_single 𝕜 unit
  refine ⟨character, Units.mk0 coefficient nonzero, Units.ext ?_⟩
  change fan.laurentRationalMap 𝕜 regular nonempty unit.val = _
  rw [same, fan.laurentRationalMap_single 𝕜 regular nonempty]
  rfl

theorem torusChartOpen_le_chartOpen (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) :
    (fan.affineToricChartι 𝕜 regular (fan.botCone nonempty)).opensRange ≤
      (fan.affineToricChartι 𝕜 regular cone).opensRange := by
  have intersection := fan.chart_opensRange_intersection 𝕜 regular (fan.botCone nonempty) cone
  have bottom : fan.botCone nonempty ⊓ cone = fan.botCone nonempty := by
    apply Subtype.ext
    change (⊥ : PointedCone ℝ Ambient) ⊓ cone.val = ⊥
    simp
  rw [bottom] at intersection
  exact (le_of_eq intersection).trans inf_le_right

variable [FiniteDimensional ℝ Ambient]

theorem invariantDivisorCartier_torus_restrict (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.invariantDivisorCartier 𝕜 complete regular divisor) |_
      (fan.affineToricChartι 𝕜 regular (fan.botCone (fan.completeFan_nonemptyCones complete))).opensRange =
        0 := by
  let nonempty := fan.completeFan_nonemptyCones complete
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let torus := fan.botCone nonempty
  let := fan.chartOpen_nonempty 𝕜 regular torus
  let index := (Finite.equivFin fan.cones) torus
  let cone := fan.divisorLocalCone 𝕜 complete regular index
  let := fan.chartOpen_nonempty 𝕜 regular cone
  have included := fan.torusChartOpen_le_chartOpen 𝕜 regular nonempty cone
  have equation := fan.invariantDivisorCartier_localEquation 𝕜 complete regular divisor index
  have restricted := congrArg (fun local_section => TopCat.Presheaf.restrictOpen local_section
    (fan.affineToricChartι 𝕜 regular torus).opensRange included) equation
  rw [TopCat.Presheaf.restrict_restrict,
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict] at restricted
  rw [restricted]
  let character := -fan.divisorLocalCharacter 𝕜 complete regular divisor index
  let unit := toricMonomialUnit 𝕜 fan.lattice torus.val character
    (by change character ∈ dualSemigroup fan.lattice ⊥; simp)
    (by change -character ∈ dualSemigroup fan.lattice ⊥; simp)
  have germ := fan.chartCoordinateGerm_monomialUnit 𝕜 regular nonempty torus character
    (by change character ∈ dualSemigroup fan.lattice ⊥; simp)
    (by change -character ∈ dualSemigroup fan.lattice ⊥; simp)
  rw [← germ, ← fan.chartCoordinateGerm_regularUnit 𝕜 regular nonempty torus unit]
  exact TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_germToFunctionField_eq_zero
    (fan.algebraicRealization 𝕜 regular) _ _

theorem invariantDivisorCartier_principal_has_laurentUnit (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    ∀ rational : (fan.algebraicRealization 𝕜 regular).functionFieldˣ,
      fan.invariantDivisorCartier 𝕜 complete regular divisor =
        TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor
          (fan.algebraicRealization 𝕜 regular) rational →
      ∃ unit : (fan.LaurentCharacterAlgebra 𝕜)ˣ,
        Units.map (fan.laurentRationalMap 𝕜 regular
          (fan.completeFan_nonemptyCones complete)).toMonoidHom unit = rational := by
  let nonempty := fan.completeFan_nonemptyCones complete
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let torus := fan.botCone nonempty
  let := fan.chartOpen_nonempty 𝕜 regular torus
  intro rational same
  have zero := fan.invariantDivisorCartier_torus_restrict 𝕜 complete regular divisor
  rw [same, TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_restrict] at zero
  have classes : TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass
      (fan.algebraicRealization 𝕜 regular) (fan.affineToricChartι 𝕜 regular torus).opensRange
      (Additive.ofMul rational) =
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass
      (fan.algebraicRealization 𝕜 regular) (fan.affineToricChartι 𝕜 regular torus).opensRange
      (Additive.ofMul 1) := by
    change _ = (_ : Additive (fan.algebraicRealization 𝕜 regular).functionFieldˣ →+ _) 0
    rw [map_zero]
    exact zero
  obtain ⟨section_unit, relation⟩ :=
    (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
      (fan.algebraicRealization 𝕜 regular) (fan.affineToricChartι 𝕜 regular torus).opensRange
      rational 1).mp classes
  let coordinate_unit := Units.map
    (fan.chartCoordinateSectionsEquiv 𝕜 regular torus).symm.toMonoidHom section_unit
  let unit := Units.map (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).toMonoidHom coordinate_unit
  refine ⟨unit, ?_⟩
  apply Units.ext
  change fan.chartCoordinateGerm 𝕜 regular nonempty torus
    ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm
      ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice) coordinate_unit.val)) = rational.val
  erw [(denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm_apply_apply]
  have transported := fan.chartCoordinateGerm_regularUnit 𝕜 regular nonempty torus coordinate_unit
  have section_same : Units.map (fan.chartCoordinateSectionsEquiv 𝕜 regular torus).toMonoidHom
      coordinate_unit = section_unit := by
    apply Units.ext
    exact (fan.chartCoordinateSectionsEquiv 𝕜 regular torus).apply_symm_apply _
  rw [section_same] at transported
  have rational_same := (mul_one _).symm.trans relation
  exact congrArg Units.val (transported.symm.trans rational_same)

theorem invariantDivisorCartier_principal_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (∃ rational : (fan.algebraicRealization 𝕜 regular).functionFieldˣ,
      fan.invariantDivisorCartier 𝕜 complete regular divisor =
        TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor
          (fan.algebraicRealization 𝕜 regular) rational) ↔
      ∃ character : Lattice →+ ℤ, divisor = fan.principalRayDivisor character := by
  let nonempty := fan.completeFan_nonemptyCones complete
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  constructor
  · rintro ⟨rational, same⟩
    obtain ⟨unit, unit_same⟩ :=
      fan.invariantDivisorCartier_principal_has_laurentUnit 𝕜 complete regular divisor rational same
    obtain ⟨character, scalar, decomposition⟩ :=
      fan.laurentRationalUnit_eq_scalar_character 𝕜 regular nonempty unit
    refine ⟨character, fan.invariantDivisorCartier_injective 𝕜 complete regular ?_⟩
    rw [fan.invariantDivisorCartier_principal 𝕜 complete regular character, same,
      ← unit_same, decomposition,
      TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_mul,
      fan.principalCartierDivisor_rationalScalarUnit 𝕜 regular nonempty, zero_add]
  · rintro ⟨character, rfl⟩
    exact ⟨fan.rationalCharacterUnit 𝕜 regular nonempty character,
      fan.invariantDivisorCartier_principal 𝕜 complete regular character⟩

theorem invariantDivisorLineBundle_class_eq_one_iff_principal (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    TauCeti.AlgebraicGeometry.LineBundleClass.mk
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) = 1 ↔
      ∃ character : Lattice →+ ℤ, divisor = fan.principalRayDivisor character := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  change (fan.invariantDivisorCartier 𝕜 complete regular divisor).toLineBundleClass = 1 ↔ _
  rw [BondalThomsen.CartierDivisorPrincipalKernel.toLineBundleClass_eq_one_iff,
    fan.invariantDivisorCartier_principal_iff 𝕜 complete regular divisor]

theorem invariantDivisorPicardRealization_eq_zero_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor_class : fan.InvariantRayDivisorClass) :
    fan.invariantDivisorPicardRealization 𝕜 complete regular divisor_class = 0 ↔
      divisor_class = 0 := by
  induction divisor_class using QuotientAddGroup.induction_on with
  | H divisor =>
    change fan.invariantDivisorPicardRealization 𝕜 complete regular
      (fan.invariantRayDivisorClass divisor) = 0 ↔ fan.invariantRayDivisorClass divisor = 0
    constructor
    · intro zero
      rw [fan.invariantDivisorPicardRealization_apply 𝕜] at zero
      have trivial : TauCeti.AlgebraicGeometry.LineBundleClass.mk
          (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) = 1 :=
        congrArg Additive.toMul zero
      obtain ⟨character, same⟩ :=
        (fan.invariantDivisorLineBundle_class_eq_one_iff_principal 𝕜 complete regular divisor).mp trivial
      rw [same, fan.invariantRayDivisorClass_principal]
    · intro zero
      rw [zero, map_zero]

theorem invariantDivisorPicardRealization_injective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    Function.Injective (fan.invariantDivisorPicardRealization 𝕜 complete regular) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  intro first second same
  apply sub_eq_zero.mp
  apply (fan.invariantDivisorPicardRealization_eq_zero_iff 𝕜 complete regular (first - second)).mp
  rw [map_sub, same, sub_self]

end TauCeti.Toric.Fan
