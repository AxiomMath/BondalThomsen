module

public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import BondalThomsen.Fan.CompleteFanCharacters
public import BondalThomsen.Toric.Scheme.BasisChart

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem chartCoordinateGerm_injective (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) :
    Function.Injective (fan.chartCoordinateGerm 𝕜 regular nonempty cone) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.chartOpen_nonempty 𝕜 regular cone
  change Function.Injective
    (((fan.algebraicRealization 𝕜 regular).germToFunctionField
      (fan.affineToricChartι 𝕜 regular cone).opensRange).hom.comp
      (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).toRingHom)
  exact ((fan.algebraicRealization 𝕜 regular).germToFunctionField_injective _).comp
    (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).injective

theorem denseTorusCharacterUnit_laurent (fan : Fan embedding) (character : Lattice →+ ℤ) :
    denseTorusCoordinateRingEquiv 𝕜 fan.lattice (fan.denseTorusCharacterUnit 𝕜 character).val =
      MonoidAlgebra.single (ofAdd character) (1 : 𝕜) := by
  change denseTorusCoordinateRingEquiv 𝕜 fan.lattice
    (MonoidAlgebra.single (ofAdd (⟨character, by rw [dualSemigroup_bot]; trivial⟩ :
      dualSemigroup fan.lattice ⊥)) 1) = _
  rw [denseTorusCoordinateRingEquiv_single]

theorem coneLaurentMap_eq_denseTorus_faceMap (fan : Fan embedding) (cone : fan.cones)
    (polynomial : affineCoordinateRing 𝕜 fan.lattice cone.val) :
    fan.coneLaurentMap 𝕜 cone.val polynomial = denseTorusCoordinateRingEquiv 𝕜 fan.lattice
      (faceAffineCoordinateRingMap 𝕜 fan.lattice
        ((fan.isToricCone cone.property).salient.bot_isFaceOf) polynomial) := by
  exact (DFunLike.congr_fun (fan.denseTorusCoordinateRingEquiv_faceMap 𝕜 cone) polynomial).symm

theorem character_mem_dualSemigroup_of_chart_germ (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (character : Lattice →+ ℤ) (polynomial : affineCoordinateRing 𝕜 fan.lattice cone.val)
    (same : fan.chartCoordinateGerm 𝕜 regular nonempty cone polynomial =
      (fan.rationalCharacterUnit 𝕜 regular nonempty character).val) :
    character ∈ dualSemigroup fan.lattice cone.val := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  have torus_same :
      faceAffineCoordinateRingMap 𝕜 fan.lattice
        ((fan.isToricCone cone.property).salient.bot_isFaceOf) polynomial =
      (fan.denseTorusCharacterUnit 𝕜 character).val := by
    apply fan.chartCoordinateGerm_injective 𝕜 regular nonempty (fan.botCone nonempty)
    rw [← fan.chartCoordinateGerm_torus 𝕜 regular nonempty cone polynomial]
    exact same
  have laurent_same : fan.coneLaurentMap 𝕜 cone.val polynomial =
      MonoidAlgebra.single (ofAdd character) (1 : 𝕜) := by
    rw [fan.coneLaurentMap_eq_denseTorus_faceMap 𝕜 cone polynomial, torus_same,
      fan.denseTorusCharacterUnit_laurent 𝕜 character]
  apply fan.character_regular_of_mem_coneLaurent_support 𝕜 cone.val polynomial (ofAdd character)
  rw [laurent_same]
  simp

theorem character_dualSemigroup_pair_of_chart_unit (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (character : Lattice →+ ℤ) (unit : (affineCoordinateRing 𝕜 fan.lattice cone.val)ˣ)
    (same : Units.map (fan.chartCoordinateGerm 𝕜 regular nonempty cone).toMonoidHom unit =
      fan.rationalCharacterUnit 𝕜 regular nonempty character) :
    character ∈ dualSemigroup fan.lattice cone.val ∧
      -character ∈ dualSemigroup fan.lattice cone.val := by
  constructor
  · apply fan.character_mem_dualSemigroup_of_chart_germ 𝕜 regular nonempty cone character unit.val
    exact congrArg Units.val same
  · apply fan.character_mem_dualSemigroup_of_chart_germ 𝕜 regular nonempty cone (-character) unit.inv
    have inverse_same := congrArg (fun value => value⁻¹) same
    rw [← map_inv, ← fan.rationalCharacterUnit_neg 𝕜 regular nonempty character] at inverse_same
    exact congrArg Units.val inverse_same

theorem character_pair_of_rationalUnitClass_eq (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (first second : Lattice →+ ℤ)
    (same : letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
      letI := fan.chartOpen_nonempty 𝕜 regular cone
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
          (fan.affineToricChartι 𝕜 regular cone).opensRange
          (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular nonempty first)) =
        TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
          (fan.affineToricChartι 𝕜 regular cone).opensRange
          (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular nonempty second))) :
    first - second ∈ dualSemigroup fan.lattice cone.val ∧
      -(first - second) ∈ dualSemigroup fan.lattice cone.val := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.chartOpen_nonempty 𝕜 regular cone
  obtain ⟨section_unit, relation⟩ :=
    (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
      (fan.algebraicRealization 𝕜 regular) (fan.affineToricChartι 𝕜 regular cone).opensRange
      (fan.rationalCharacterUnit 𝕜 regular nonempty first)
      (fan.rationalCharacterUnit 𝕜 regular nonempty second)).mp same
  let coordinate_unit := Units.map (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).symm.toMonoidHom
    section_unit
  have transported := fan.chartCoordinateGerm_regularUnit 𝕜 regular nonempty cone coordinate_unit
  have section_unit_same : Units.map (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).toMonoidHom
      coordinate_unit = section_unit := by
    apply Units.ext
    exact (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).apply_symm_apply section_unit.val
  rw [section_unit_same] at transported
  apply fan.character_dualSemigroup_pair_of_chart_unit 𝕜 regular nonempty cone (first - second)
    coordinate_unit
  rw [← transported]
  apply mul_right_cancel (b := fan.rationalCharacterUnit 𝕜 regular nonempty second)
  rw [relation, fan.rationalCharacterUnit_sub_mul 𝕜]

theorem rationalCharacterUnit_basisChart_class_injective (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    let cone : fan.cones := ⟨_, cone_basis⟩
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    Function.Injective (fun character : Lattice →+ ℤ =>
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular cone).opensRange
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular nonempty character))) := by
  dsimp only
  intro first second same
  have pair := fan.character_pair_of_rationalUnitClass_eq 𝕜 regular nonempty ⟨_, cone_basis⟩
    first second same
  have positive := (fan.mem_dualSemigroup_basisCone_iff basis (first - second)).mp pair.1
  have negative := (fan.mem_dualSemigroup_basisCone_iff basis (-(first - second))).mp pair.2
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  have lower := positive index
  have upper := negative index
  change first (basis index) - second (basis index) ≥ 0 at lower
  change -(first (basis index) - second (basis index)) ≥ 0 at upper
  change first (basis index) = second (basis index)
  omega

variable [FiniteDimensional ℝ Ambient]

theorem invariantDivisorCartier_eq_localCharacters (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : fan.invariantDivisorCartier 𝕜 complete regular first =
      fan.invariantDivisorCartier 𝕜 complete regular second)
    (index : Fin (Nat.card fan.cones)) :
    fan.divisorLocalCharacter 𝕜 complete regular first index =
      fan.divisorLocalCharacter 𝕜 complete regular second index := by
  let original := (Finite.equivFin fan.cones).symm index
  let basis_data := fan.divisorChartBasis complete regular original
  have local_same := congrArg (fun divisor => TopCat.Presheaf.restrictOpen divisor
    (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange le_top) same
  rw [fan.invariantDivisorCartier_localEquation 𝕜 complete regular first index,
    fan.invariantDivisorCartier_localEquation 𝕜 complete regular second index] at local_same
  have characters_same := fan.rationalCharacterUnit_basisChart_class_injective 𝕜 regular
    (fan.completeFan_nonemptyCones complete) basis_data.val.2 basis_data.property.1 local_same
  exact neg_injective characters_same

theorem invariantDivisorCartier_injective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    Function.Injective (fan.invariantDivisorCartier 𝕜 complete regular) := by
  intro first second same
  apply Finsupp.ext
  intro ray
  let ray_cone : fan.cones := ⟨PointedCone.hull ℝ {embedding ray.val}, ray.property.2⟩
  let index := (Finite.equivFin fan.cones) ray_cone
  let basis_data := fan.divisorChartBasis complete regular ray_cone
  have contains : embedding ray.val ∈ PointedCone.hull ℝ
      (Set.range (fun position => embedding (basis_data.val.2 position))) :=
    basis_data.property.2.le (PointedCone.subset_hull (Set.mem_singleton _))
  have local_same := fan.invariantDivisorCartier_eq_localCharacters 𝕜 complete regular first second
    same index
  have first_character : fan.divisorLocalCharacter 𝕜 complete regular first index =
      fan.coneDivisorCharacter basis_data.val.2 basis_data.property.1 first := by
    change fan.coneDivisorCharacter
      (fan.divisorChartBasis complete regular ((Finite.equivFin fan.cones).symm index)).val.2
      (fan.divisorChartBasis complete regular ((Finite.equivFin fan.cones).symm index)).property.1 first = _
    simp only [index]
    rw [Equiv.symm_apply_apply]
  have second_character : fan.divisorLocalCharacter 𝕜 complete regular second index =
      fan.coneDivisorCharacter basis_data.val.2 basis_data.property.1 second := by
    change fan.coneDivisorCharacter
      (fan.divisorChartBasis complete regular ((Finite.equivFin fan.cones).symm index)).val.2
      (fan.divisorChartBasis complete regular ((Finite.equivFin fan.cones).symm index)).property.1 second = _
    simp only [index]
    rw [Equiv.symm_apply_apply]
  rw [first_character, second_character] at local_same
  have values_same := congrArg (fun character : Lattice →+ ℤ => character ray.val) local_same
  rw [fan.coneDivisorCharacter_ray basis_data.val.2 basis_data.property.1 first ray contains,
    fan.coneDivisorCharacter_ray basis_data.val.2 basis_data.property.1 second ray contains] at values_same
  exact neg_injective values_same

end TauCeti.Toric.Fan
