module

public import BondalThomsen.Toric.Divisor.PicardSurjective

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def invertibleSheaf_chartCharacter (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] (cone : fan.cones) : Lattice →+ ℤ :=
  (fan.invertibleSheaf_chartRationalUnit_eq_scalar_character 𝕜 complete regular sheaf cone).choose

theorem invertibleSheaf_chartCharacter_spec (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] (cone : fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    ∃ scalar : 𝕜ˣ,
      Scheme.Modules.trivializationGeneratorRationalUnit sheaf
        (fan.invertibleSheaf_torusOpenTrivialization 𝕜 complete regular sheaf)
        (fan.torusOpen_dense 𝕜 regular (fan.completeFan_nonemptyCones complete))
        (fan.invertibleSheaf_chartOpenTrivialization 𝕜 complete regular cone sheaf) =
      fan.rationalScalarUnit 𝕜 regular (fan.completeFan_nonemptyCones complete) scalar *
        fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf cone) :=
  (fan.invertibleSheaf_chartRationalUnit_eq_scalar_character 𝕜 complete regular sheaf cone).choose_spec

noncomputable def invertibleSheaf_torusCartierDivisor (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor (fan.algebraicRealization 𝕜 regular) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (sheaf.exists_cartierDivisor_restrict_eq
    (fan.invertibleSheaf_torusOpenTrivialization 𝕜 complete regular sheaf)
    (fan.torusOpen_dense 𝕜 regular (fan.completeFan_nonemptyCones complete))).choose

theorem invertibleSheaf_torusCartierDivisor_spec (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    ∀ (domain : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty domain]
      (basis : SheafOfModules.free
        (R := (fan.algebraicRealization 𝕜 regular).ringCatSheaf.over domain) PUnit ≅ sheaf.over domain),
      (fan.invertibleSheaf_torusCartierDivisor 𝕜 complete regular sheaf) |_ domain =
        TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular) domain
          (-Additive.ofMul (Scheme.Modules.trivializationGeneratorRationalUnit sheaf
            (fan.invertibleSheaf_torusOpenTrivialization 𝕜 complete regular sheaf)
            (fan.torusOpen_dense 𝕜 regular (fan.completeFan_nonemptyCones complete)) basis)) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (sheaf.exists_cartierDivisor_restrict_eq
    (fan.invertibleSheaf_torusOpenTrivialization 𝕜 complete regular sheaf)
    (fan.torusOpen_dense 𝕜 regular (fan.completeFan_nonemptyCones complete))).choose_spec

noncomputable def invertibleSheaf_torusCartierIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    sheaf ≅ (fan.invertibleSheaf_torusCartierDivisor 𝕜 complete regular sheaf).sheaf := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isoSheafOfRestrictEq
    (fan.invertibleSheaf_torusCartierDivisor_spec 𝕜 complete regular sheaf)

theorem invertibleSheaf_torusCartierDivisor_chart (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] (cone : fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    (fan.invertibleSheaf_torusCartierDivisor 𝕜 complete regular sheaf) |_
        (fan.affineToricChartι 𝕜 regular cone).opensRange =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular cone).opensRange
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf cone))) := by
  let nonempty := fan.completeFan_nonemptyCones complete
  letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  letI := fan.chartOpen_nonempty 𝕜 regular cone
  rw [fan.invertibleSheaf_torusCartierDivisor_spec 𝕜 complete regular sheaf _
    (fan.invertibleSheaf_chartOpenTrivialization 𝕜 complete regular cone sheaf)]
  obtain ⟨scalar, same⟩ := fan.invertibleSheaf_chartCharacter_spec 𝕜 complete regular sheaf cone
  rw [same, ofMul_mul, neg_add, map_add, map_neg, map_neg]
  have scalarZero := congrArg (fun divisor => TopCat.Presheaf.restrictOpen divisor
    (fan.affineToricChartι 𝕜 regular cone).opensRange le_top)
    (fan.principalCartierDivisor_rationalScalarUnit 𝕜 regular nonempty scalar)
  rw [TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_restrict] at scalarZero
  have restrictedZero : TopCat.Presheaf.restrictOpen
      (0 : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor (fan.algebraicRealization 𝕜 regular))
      (fan.affineToricChartι 𝕜 regular cone).opensRange le_top = 0 := by
    exact map_zero ((TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf
      (fan.algebraicRealization 𝕜 regular)).obj.map (homOfLE le_top).op).hom
  rw [restrictedZero] at scalarZero
  rw [scalarZero, neg_zero, zero_add, fan.rationalCharacterUnit_neg 𝕜 regular nonempty]
  exact (map_neg _ _).symm

theorem invertibleSheaf_chartCharacter_overlap (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] (first second : fan.cones) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    letI := fan.chartOpen_nonempty 𝕜 regular (first ⊓ second)
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular (first ⊓ second)).opensRange
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first))) =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular (first ⊓ second)).opensRange
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second))) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  letI := fan.chartOpen_nonempty 𝕜 regular first
  letI := fan.chartOpen_nonempty 𝕜 regular second
  letI := fan.chartOpen_nonempty 𝕜 regular (first ⊓ second)
  have includedFirst : (fan.affineToricChartι 𝕜 regular (first ⊓ second)).opensRange ≤
      (fan.affineToricChartι 𝕜 regular first).opensRange := by
    rw [fan.chart_opensRange_intersection 𝕜 regular first second]
    exact inf_le_left
  have includedSecond : (fan.affineToricChartι 𝕜 regular (first ⊓ second)).opensRange ≤
      (fan.affineToricChartι 𝕜 regular second).opensRange := by
    rw [fan.chart_opensRange_intersection 𝕜 regular first second]
    exact inf_le_right
  have firstEquation := congrArg (fun equation => TopCat.Presheaf.restrictOpen equation
    (fan.affineToricChartι 𝕜 regular (first ⊓ second)).opensRange includedFirst)
    (fan.invertibleSheaf_torusCartierDivisor_chart 𝕜 complete regular sheaf first)
  have secondEquation := congrArg (fun equation => TopCat.Presheaf.restrictOpen equation
    (fan.affineToricChartι 𝕜 regular (first ⊓ second)).opensRange includedSecond)
    (fan.invertibleSheaf_torusCartierDivisor_chart 𝕜 complete regular sheaf second)
  rw [TopCat.Presheaf.restrict_restrict,
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict] at firstEquation secondEquation
  exact firstEquation.symm.trans secondEquation

theorem invertibleSheaf_chartCharacter_sharedRay (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf]
    (first second : fan.cones) (ray : fan.Ray)
    (inFirst : embedding ray.val ∈ first.val) (inSecond : embedding ray.val ∈ second.val) :
    fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first ray.val =
      fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second ray.val := by
  have pair := fan.character_pair_of_rationalUnitClass_eq 𝕜 regular
    (fan.completeFan_nonemptyCones complete) (first ⊓ second)
    (-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first)
    (-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second)
    (fan.invertibleSheaf_chartCharacter_overlap 𝕜 complete regular sheaf first second)
  have positive := pair.1 (show embedding ray.val ∈ (first ⊓ second).val from ⟨inFirst, inSecond⟩)
  have negative := pair.2 (show embedding ray.val ∈ (first ⊓ second).val from ⟨inFirst, inSecond⟩)
  change 0 ≤ fan.lattice.realCharacter
    (-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first -
      -fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second) (embedding ray.val) at positive
  change 0 ≤ fan.lattice.realCharacter
    (-(-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first -
      -fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second)) (embedding ray.val) at negative
  rw [fan.lattice.realCharacter_apply] at positive negative
  have lower : 0 ≤ (-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first -
      -fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second) ray.val := by
    exact_mod_cast positive
  have upper : 0 ≤ -(-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first -
      -fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second) ray.val := by
    exact_mod_cast negative
  change 0 ≤ -fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first ray.val -
    -fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second ray.val at lower
  change 0 ≤ -(-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf first ray.val -
    -fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf second ray.val) at upper
  omega

noncomputable def invertibleSheaf_invariantRayDivisor (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] : fan.InvariantRayDivisor :=
  fan.invariantDivisorOfCoefficients (fun ray =>
    -fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf
      ⟨PointedCone.hull ℝ {embedding ray.val}, ray.property.2⟩ ray.val)

theorem invertibleSheaf_invariantRayDivisor_ray (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] (cone : fan.cones) (ray : fan.Ray)
    (contains : embedding ray.val ∈ cone.val) :
    fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf cone ray.val =
      -fan.invertibleSheaf_invariantRayDivisor 𝕜 complete regular sheaf ray := by
  change _ = -(-fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf
    ⟨PointedCone.hull ℝ {embedding ray.val}, ray.property.2⟩ ray.val)
  rw [neg_neg]
  exact fan.invertibleSheaf_chartCharacter_sharedRay 𝕜 complete regular sheaf cone _ ray
    contains (PointedCone.subset_hull (Set.mem_singleton _))

theorem invertibleSheaf_invariantRayDivisor_localCharacter (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] (index : Fin (Nat.card fan.cones)) :
    fan.divisorLocalCharacter 𝕜 complete regular
        (fan.invertibleSheaf_invariantRayDivisor 𝕜 complete regular sheaf) index =
      fan.invertibleSheaf_chartCharacter 𝕜 complete regular sheaf
        (fan.divisorLocalCone 𝕜 complete regular index) := by
  let original := (Finite.equivFin fan.cones).symm index
  let basisData := fan.divisorChartBasis complete regular original
  change fan.coneDivisorCharacter basisData.val.2 basisData.property.1
    (fan.invertibleSheaf_invariantRayDivisor 𝕜 complete regular sheaf) = _
  apply AddMonoidHom.toIntLinearMap_injective
  apply basisData.val.2.ext
  intro position
  change fan.coneDivisorCharacter basisData.val.2 basisData.property.1
    (fan.invertibleSheaf_invariantRayDivisor 𝕜 complete regular sheaf) (basisData.val.2 position) = _
  rw [fan.coneDivisorCharacter_basis]
  exact (fan.invertibleSheaf_invariantRayDivisor_ray 𝕜 complete regular sheaf
    (fan.divisorLocalCone 𝕜 complete regular index)
    (fan.basisRay basisData.val.2 basisData.property.1 position)
    (PointedCone.subset_hull (Set.mem_range_self position))).symm

theorem invertibleSheaf_invariantDivisorCartier_eq (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.invariantDivisorCartier 𝕜) complete regular
        (fan.invertibleSheaf_invariantRayDivisor 𝕜 complete regular sheaf) =
      fan.invertibleSheaf_torusCartierDivisor 𝕜 complete regular sheaf := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  apply fan.cartierDivisor_eq_of_divisorCharts 𝕜 complete regular
  intro index
  letI := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  rw [fan.invariantDivisorCartier_localEquation 𝕜 complete regular,
    fan.invertibleSheaf_invariantRayDivisor_localCharacter 𝕜 complete regular sheaf index]
  exact (fan.invertibleSheaf_torusCartierDivisor_chart 𝕜 complete regular sheaf
    (fan.divisorLocalCone 𝕜 complete regular index)).symm

noncomputable def invertibleSheaf_invariantDivisorIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (sheaf : (fan.algebraicRealization 𝕜 regular).Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) sheaf] :
    sheaf ≅ (fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.invertibleSheaf_invariantRayDivisor 𝕜 complete regular sheaf)).obj := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact fan.invertibleSheaf_torusCartierIso 𝕜 complete regular sheaf ≪≫
    (eqToIso (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf
      (fan.invertibleSheaf_invariantDivisorCartier_eq 𝕜 complete regular sheaf))).symm

theorem invariantDivisorPicardRealization_surjective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    Function.Surjective (fan.invariantDivisorPicardRealization 𝕜 complete regular) := by
  intro bundleClass
  obtain ⟨bundle, represented⟩ := TauCeti.AlgebraicGeometry.LineBundleClass.mk_surjective
    (Additive.toMul bundleClass)
  refine ⟨fan.invariantRayDivisorClass
    (fan.invertibleSheaf_invariantRayDivisor 𝕜 complete regular bundle.obj), ?_⟩
  rw [fan.invariantDivisorPicardRealization_apply 𝕜 complete regular]
  apply Additive.toMul.injective
  change TauCeti.AlgebraicGeometry.LineBundleClass.mk
    (fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.invertibleSheaf_invariantRayDivisor 𝕜 complete regular bundle.obj)) = Additive.toMul bundleClass
  rw [← represented]
  exact TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mpr
    ⟨(fan.invertibleSheaf_invariantDivisorIso 𝕜 complete regular bundle.obj).symm⟩

end TauCeti.Toric.Fan
