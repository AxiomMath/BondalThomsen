module

public import BondalThomsen.Toric.Divisor.DivisorMonomialAffineEmbedding

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Module Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)

noncomputable def allSectionProjectiveRatio (chart : Fin (Nat.card fan.cones))
    (exponent : fan.globalDivisorSectionExponents divisor) :
    affineCoordinateRing 𝕜 fan.lattice (fan.divisorLocalCone 𝕜 complete regular chart).val :=
  fan.allDivisorMonomialRatio 𝕜
    (fan.divisorSectionChartBasis complete regular chart).val.2
    (fan.divisorSectionChartBasis complete regular chart).property.1 divisor exponent

noncomputable def allSectionProjectiveDenominator (chart : Fin (Nat.card fan.cones)) :
    fan.globalDivisorSectionExponents divisor :=
  fan.basisDivisorDenominator
    (fan.divisorSectionChartBasis complete regular chart).val.2
    (fan.divisorSectionChartBasis complete regular chart).property.1 divisor (support _ _ _)

theorem allSectionProjectiveRatio_denominator (chart : Fin (Nat.card fan.cones)) :
    fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart
      (fan.allSectionProjectiveDenominator complete regular divisor support chart) = 1 :=
  fan.allDivisorMonomialRatio_denominator 𝕜 _ _ _ _

theorem allSectionProjectiveRatio_overlap (first second : Fin (Nat.card fan.cones))
    (exponent : fan.globalDivisorSectionExponents divisor) :
    faceAffineCoordinateRingMap 𝕜 fan.lattice
        (fan.inf_isFaceOf_right (fan.divisorLocalCone 𝕜 complete regular first).property
          (fan.divisorLocalCone 𝕜 complete regular second).property)
        (fan.allSectionProjectiveRatio 𝕜 complete regular divisor second exponent) =
      (fan.divisorProjectiveTransitionUnit 𝕜 complete regular divisor first second :
        affineCoordinateRing 𝕜 fan.lattice
          ((fan.divisorLocalCone 𝕜 complete regular first).val ⊓
            (fan.divisorLocalCone 𝕜 complete regular second).val)) *
        faceAffineCoordinateRingMap 𝕜 fan.lattice
          (fan.inf_isFaceOf_left (fan.divisorLocalCone 𝕜 complete regular first).property
            (fan.divisorLocalCone 𝕜 complete regular second).property)
          (fan.allSectionProjectiveRatio 𝕜 complete regular divisor first exponent) :=
  fan.globalDivisorChartCoefficient_overlap 𝕜
    (fan.divisorSectionChartBasis complete regular first).val.2
    (fan.divisorSectionChartBasis complete regular first).property.1
    (fan.divisorSectionChartBasis complete regular second).val.2
    (fan.divisorSectionChartBasis complete regular second).property.1 divisor
    (fan.globalDivisorLaurentSectionBasis 𝕜 divisor exponent)

noncomputable def allSectionProjectiveChartMap (chart : Fin (Nat.card fan.cones)) :
    fan.affineToricChart 𝕜 (fan.divisorLocalCone 𝕜 complete regular chart) ⟶
      fan.allDivisorMonomialProjectiveSpace 𝕜 divisor :=
  BondalThomsen.projectiveCoordinateMap 𝕜 (algebraMap 𝕜 _)
    (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart)
    (fan.allSectionProjectiveDenominator complete regular divisor support chart) 1
    (fan.allSectionProjectiveRatio_denominator 𝕜 complete regular divisor support chart)

theorem allSectionProjectiveChartMap_overlap (first second : Fin (Nat.card fan.cones)) :
    fan.affineToricOverlapLeft 𝕜 (fan.divisorLocalCone 𝕜 complete regular first)
        (fan.divisorLocalCone 𝕜 complete regular second) ≫
          fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support first =
      fan.affineToricOverlapRight 𝕜 (fan.divisorLocalCone 𝕜 complete regular first)
        (fan.divisorLocalCone 𝕜 complete regular second) ≫
          fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support second := by
  let left := faceAffineCoordinateRingMap 𝕜 fan.lattice
    (fan.inf_isFaceOf_left (fan.divisorLocalCone 𝕜 complete regular first).property
      (fan.divisorLocalCone 𝕜 complete regular second).property)
  let right := faceAffineCoordinateRingMap 𝕜 fan.lattice
    (fan.inf_isFaceOf_right (fan.divisorLocalCone 𝕜 complete regular first).property
      (fan.divisorLocalCone 𝕜 complete regular second).property)
  unfold allSectionProjectiveChartMap
  rw [affineToricOverlapLeft_def, affineToricOverlapRight_def,
    faceAffineToricSchemeMap_def, faceAffineToricSchemeMap_def,
    BondalThomsen.projectiveCoordinateMap_map, BondalThomsen.projectiveCoordinateMap_map]
  have left_constants : left.toRingHom.comp (algebraMap 𝕜 _) = algebraMap 𝕜 _ := by
    apply RingHom.ext
    intro scalar
    exact left.commutes scalar
  have right_constants : right.toRingHom.comp (algebraMap 𝕜 _) = algebraMap 𝕜 _ := by
    apply RingHom.ext
    intro scalar
    exact right.commutes scalar
  change BondalThomsen.projectiveCoordinateMap 𝕜 (left.toRingHom.comp (algebraMap 𝕜 _))
      (fun exponent => left (fan.allSectionProjectiveRatio 𝕜 complete regular divisor first exponent))
      (fan.allSectionProjectiveDenominator complete regular divisor support first)
      (Units.map left.toMonoidHom 1) _ =
    BondalThomsen.projectiveCoordinateMap 𝕜 (right.toRingHom.comp (algebraMap 𝕜 _))
      (fun exponent => right (fan.allSectionProjectiveRatio 𝕜 complete regular divisor second exponent))
      (fan.allSectionProjectiveDenominator complete regular divisor support second)
      (Units.map right.toMonoidHom 1) _
  rw [left_constants, right_constants]
  apply BondalThomsen.projectiveCoordinateMap_scale 𝕜 _ _ _
    (fan.divisorProjectiveTransitionUnit 𝕜 complete regular divisor first second)
  intro exponent
  exact fan.allSectionProjectiveRatio_overlap 𝕜 complete regular divisor first second exponent

theorem allSectionProjectiveChartMap_pullback (first second : Fin (Nat.card fan.cones)) :
    Limits.pullback.fst
        ((fan.divisorProjectiveChartCover 𝕜 complete regular).f first)
        ((fan.divisorProjectiveChartCover 𝕜 complete regular).f second) ≫
          fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support first =
      Limits.pullback.snd
        ((fan.divisorProjectiveChartCover 𝕜 complete regular).f first)
        ((fan.divisorProjectiveChartCover 𝕜 complete regular).f second) ≫
          fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support second := by
  let intersection := fan.affineToricOverlap_isPullback 𝕜 regular
    (fan.divisorLocalCone 𝕜 complete regular first) (fan.divisorLocalCone 𝕜 complete regular second)
  apply (cancel_epi intersection.isoPullback.hom).mp
  dsimp only [divisorProjectiveChartCover]
  rw [← Category.assoc, ← Category.assoc,
    intersection.isoPullback_hom_fst, intersection.isoPullback_hom_snd]
  exact fan.allSectionProjectiveChartMap_overlap 𝕜 complete regular divisor support first second

noncomputable def allSectionProjectiveMonomialMap :
    fan.algebraicRealization 𝕜 regular ⟶ fan.allDivisorMonomialProjectiveSpace 𝕜 divisor :=
  (fan.divisorProjectiveChartCover 𝕜 complete regular).glueMorphisms
    (fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support)
    (fan.allSectionProjectiveChartMap_pullback 𝕜 complete regular divisor support)

@[reassoc]
theorem allSectionProjectiveMonomialMap_chart (chart : Fin (Nat.card fan.cones)) :
    fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart) ≫
        fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support =
      fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support chart :=
  (fan.divisorProjectiveChartCover 𝕜 complete regular).ι_glueMorphisms _ _ chart

@[reassoc]
theorem allSectionProjectiveChartMap_structureMap (chart : Fin (Nat.card fan.cones)) :
    fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support chart ≫
        BondalThomsen.polynomialProjStructureMap 𝕜 (fan.globalDivisorSectionExponents divisor) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 _)) :=
  BondalThomsen.projectiveCoordinateMap_structureMap 𝕜 _ _ _ _

@[reassoc]
theorem allSectionProjectiveMonomialMap_structureMap :
    fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support ≫
        BondalThomsen.polynomialProjStructureMap 𝕜 (fan.globalDivisorSectionExponents divisor) =
      fan.structureMap 𝕜 regular := by
  apply (fan.divisorProjectiveChartCover 𝕜 complete regular).hom_ext
  intro chart
  dsimp only [divisorProjectiveChartCover]
  rw [← Category.assoc, allSectionProjectiveMonomialMap_chart,
    allSectionProjectiveChartMap_structureMap, chartι_comp_structureMap]

noncomputable def allSectionProjectiveMonomialMapOver :
    Over.mk (fan.structureMap 𝕜 regular) ⟶
      Over.mk (BondalThomsen.polynomialProjStructureMap 𝕜 (fan.globalDivisorSectionExponents divisor)) :=
  Over.homMk (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
    (fan.allSectionProjectiveMonomialMap_structureMap 𝕜 complete regular divisor support)

def AllSectionProjectiveStepsAdmissible : Prop :=
  ∀ chart : Fin (Nat.card fan.cones),
    fan.BasisDivisorStepsAdmissible
      (fan.divisorSectionChartBasis complete regular chart).val.2
      (fan.divisorSectionChartBasis complete regular chart).property.1 divisor

noncomputable def allSectionProjectiveAffineChartMap (chart : Fin (Nat.card fan.cones)) :=
  fan.allDivisorMonomialAffineChartMap 𝕜
    (fan.divisorSectionChartBasis complete regular chart).val.2
    (fan.divisorSectionChartBasis complete regular chart).property.1 divisor (support _ _ _)

noncomputable def allSectionProjectiveChartInclusion (chart : Fin (Nat.card fan.cones)) :=
  Proj.awayι (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
    (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart))
    (MvPolynomial.isHomogeneous_X 𝕜 _) (by omega)

variable {𝕜} in
instance allSectionProjectiveChartInclusion_isOpenImmersion (chart : Fin (Nat.card fan.cones)) :
    IsOpenImmersion (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support chart) := by
  unfold allSectionProjectiveChartInclusion
  infer_instance

noncomputable def allSectionVertexDifference (first second : Fin (Nat.card fan.cones)) :
    dualSemigroup fan.lattice (fan.divisorLocalCone 𝕜 complete regular second).val := by
  refine ⟨fan.divisorLocalCharacter 𝕜 complete regular divisor first -
    fan.divisorLocalCharacter 𝕜 complete regular divisor second, ?_⟩
  apply (fan.sub_coneDivisorCharacter_mem_dualSemigroup_iff
    (fan.divisorSectionChartBasis complete regular second).val.2
    (fan.divisorSectionChartBasis complete regular second).property.1 divisor _).mpr
  intro ray _
  exact support _ _ _ ray

theorem allSectionProjectiveRatio_vertex (first second : Fin (Nat.card fan.cones)) :
    fan.allSectionProjectiveRatio 𝕜 complete regular divisor second
        (fan.allSectionProjectiveDenominator complete regular divisor support first) =
      MonoidAlgebra.single
        (ofAdd (fan.allSectionVertexDifference 𝕜 complete regular divisor support first second)) (1 : 𝕜) := by
  apply fan.coneCharacterSectionMap_injective 𝕜 _
    (fan.divisorLocalCharacter 𝕜 complete regular divisor second)
  rw [coneCharacterSectionMap_single]
  have reconstruct := fan.allDivisorMonomialRatio_reconstruct 𝕜
    (fan.divisorSectionChartBasis complete regular second).val.2
    (fan.divisorSectionChartBasis complete regular second).property.1 divisor
    (fan.allSectionProjectiveDenominator complete regular divisor support first)
  change fan.coneCharacterSectionMap 𝕜 _ _
    (fan.allSectionProjectiveRatio 𝕜 complete regular divisor second
      (fan.allSectionProjectiveDenominator complete regular divisor support first)) =
      MonoidAlgebra.single (ofAdd (fan.divisorLocalCharacter 𝕜 complete regular divisor second +
        (fan.allSectionVertexDifference 𝕜 complete regular divisor support first second : Lattice →+ ℤ))) 1
  change fan.coneCharacterSectionMap 𝕜 _ _
    (fan.allSectionProjectiveRatio 𝕜 complete regular divisor second
      (fan.allSectionProjectiveDenominator complete regular divisor support first)) =
      MonoidAlgebra.single
        (ofAdd (fan.divisorLocalCharacter 𝕜 complete regular divisor first)) 1 at reconstruct
  apply reconstruct.trans
  congr 1
  apply congrArg ofAdd
  change fan.divisorLocalCharacter 𝕜 complete regular divisor first =
    fan.divisorLocalCharacter 𝕜 complete regular divisor second +
      (fan.divisorLocalCharacter 𝕜 complete regular divisor first -
        fan.divisorLocalCharacter 𝕜 complete regular divisor second)
  abel

theorem allSectionVertexDifference_face_of_strictSupport
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis),
        fan.BasisDivisorStrictSupport basis cone_basis divisor)
    (first second : Fin (Nat.card fan.cones)) :
    (fan.divisorLocalCone 𝕜 complete regular second).val ⊓
        PointedCone.ofSubmodule (LinearMap.ker (fan.lattice.realCharacter
          (fan.allSectionVertexDifference 𝕜 complete regular divisor support first second : Lattice →+ ℤ))) =
      (fan.divisorLocalCone 𝕜 complete regular first).val ⊓
        (fan.divisorLocalCone 𝕜 complete regular second).val := by
  let first_basis := (fan.divisorSectionChartBasis complete regular first).val.2
  let first_cone := (fan.divisorSectionChartBasis complete regular first).property.1
  let second_basis := (fan.divisorSectionChartBasis complete regular second).val.2
  let second_cone := (fan.divisorSectionChartBasis complete regular second).property.1
  apply PointedCone.inf_ker_eq_of_eq_hull rfl
    (fan.inf_isFaceOf_right (fan.divisorLocalCone 𝕜 complete regular first).property
      (fan.divisorLocalCone 𝕜 complete regular second).property)
  · rintro vector ⟨index, rfl⟩
    rw [fan.lattice.realCharacter_apply]
    have bound := support _ first_basis first_cone (fan.basisRay second_basis second_cone index)
    change -divisor (fan.basisRay second_basis second_cone index) ≤
      fan.coneDivisorCharacter first_basis first_cone divisor (second_basis index) at bound
    change (0 : ℝ) ≤ ((fan.coneDivisorCharacter first_basis first_cone divisor
      (second_basis index) - fan.coneDivisorCharacter second_basis second_cone divisor
        (second_basis index) : ℤ) : ℝ)
    rw [fan.coneDivisorCharacter_basis]
    exact_mod_cast (by omega : (0 : ℤ) ≤
      fan.coneDivisorCharacter first_basis first_cone divisor (second_basis index) -
        -divisor (fan.basisRay second_basis second_cone index))
  · rintro vector ⟨index, rfl⟩
    rw [fan.lattice.realCharacter_apply]
    change ((fan.coneDivisorCharacter first_basis first_cone divisor (second_basis index) -
      fan.coneDivisorCharacter second_basis second_cone divisor (second_basis index) : ℤ) : ℝ) = 0 ↔ _
    rw [fan.coneDivisorCharacter_basis, Int.cast_eq_zero]
    constructor
    · intro vanishes
      have first_generator : (second_basis index) ∈ Set.range first_basis := by
        by_contra outside
        have strict := strict_support _ first_basis first_cone
          (fan.basisRay second_basis second_cone index) outside
        change -divisor (fan.basisRay second_basis second_cone index) <
          fan.coneDivisorCharacter first_basis first_cone divisor (second_basis index) at strict
        omega
      obtain ⟨first_index, same⟩ := first_generator
      constructor
      · change embedding (second_basis index) ∈
          PointedCone.hull ℝ (Set.range (fun index => embedding (first_basis index)))
        rw [← same]
        exact PointedCone.subset_hull (Set.mem_range_self first_index)
      · exact PointedCone.subset_hull (Set.mem_range_self index)
    · intro contains
      have local_value := fan.coneDivisorCharacter_ray first_basis first_cone divisor
        (fan.basisRay second_basis second_cone index) contains.1
      change fan.coneDivisorCharacter first_basis first_cone divisor (second_basis index) =
        -divisor (fan.basisRay second_basis second_cone index) at local_value
      rw [local_value]
      omega

theorem allSectionProjectiveChartMap_preimage_coordinate
    (chart : Fin (Nat.card fan.cones)) (exponent : fan.globalDivisorSectionExponents divisor) :
    fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support chart ⁻¹ᵁ
        Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
          (MvPolynomial.X exponent) =
      PrimeSpectrum.basicOpen (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent) := by
  unfold allSectionProjectiveChartMap BondalThomsen.projectiveCoordinateMap
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen
      (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
      (MvPolynomial.isHomogeneous_X 𝕜
        (fan.allSectionProjectiveDenominator complete regular divisor support chart))
      (show 0 < (1 : ℕ) by omega) (MvPolynomial.isHomogeneous_X 𝕜 exponent)
      (show 0 < (1 : ℕ) by omega)]
  rw [show HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X 𝕜
        (fan.allSectionProjectiveDenominator complete regular divisor support chart))
      (MvPolynomial.isHomogeneous_X 𝕜 exponent) =
    HomogeneousLocalization.Away.mk _
      (MvPolynomial.isHomogeneous_X 𝕜
        (fan.allSectionProjectiveDenominator complete regular divisor support chart))
      1 (MvPolynomial.X exponent) (by simpa using MvPolynomial.isHomogeneous_X 𝕜 exponent) by
        simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one]]
  change PrimeSpectrum.basicOpen
    (BondalThomsen.projectiveAwayEvaluation 𝕜 (algebraMap 𝕜 _)
      (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart)
      (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart)) 1
      (by simpa using fan.allSectionProjectiveRatio_denominator 𝕜 complete regular divisor support chart)
      (HomogeneousLocalization.Away.mk _
        (MvPolynomial.isHomogeneous_X 𝕜
          (fan.allSectionProjectiveDenominator complete regular divisor support chart))
        1 (MvPolynomial.X exponent) (by simpa using MvPolynomial.isHomogeneous_X 𝕜 exponent))) = _
  rw [BondalThomsen.projectiveAwayEvaluation_mk]
  simp only [MvPolynomial.eval₂Hom_X', inv_one, Units.val_one, one_pow, mul_one]

variable {𝕜} in
local instance allSectionOverlapRight_isOpenImmersion (first second : Fin (Nat.card fan.cones)) :
    IsOpenImmersion (fan.affineToricOverlapRight 𝕜 (fan.divisorLocalCone 𝕜 complete regular first)
      (fan.divisorLocalCone 𝕜 complete regular second)) :=
  fan.isOpenImmersion_affineToricOverlapRight 𝕜 _ _
    (regular (fan.divisorLocalCone 𝕜 complete regular second).property)

theorem allSectionProjectiveChartMap_preimage_vertex_of_strictSupport
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis),
        fan.BasisDivisorStrictSupport basis cone_basis divisor)
    (first second : Fin (Nat.card fan.cones)) :
    fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support second ⁻¹ᵁ
        (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support first).opensRange =
      (fan.affineToricOverlapRight 𝕜 (fan.divisorLocalCone 𝕜 complete regular first)
        (fan.divisorLocalCone 𝕜 complete regular second)).opensRange := by
  unfold allSectionProjectiveChartInclusion
  rw [Proj.opensRange_awayι, allSectionProjectiveChartMap_preimage_coordinate,
    allSectionProjectiveRatio_vertex]
  apply TopologicalSpace.Opens.ext
  change _ = Set.range (fan.affineToricOverlapRight 𝕜 _ _)
  rw [affineToricOverlapRight_def]
  exact (TauCeti.Toric.range_faceAffineToricSchemeMap_of_eq 𝕜 fan.lattice
    (fan.isToricCone (fan.divisorLocalCone 𝕜 complete regular second).property).fg
    (fan.inf_isFaceOf_right (fan.divisorLocalCone 𝕜 complete regular first).property
      (fan.divisorLocalCone 𝕜 complete regular second).property)
    (fan.allSectionVertexDifference 𝕜 complete regular divisor support first second)
    (fan.allSectionVertexDifference_face_of_strictSupport 𝕜 complete regular divisor support
      strict_support first second)).symm

theorem allSectionProjectiveMonomialMap_preimage_vertex_of_strictSupport
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis),
        fan.BasisDivisorStrictSupport basis cone_basis divisor)
    (first : Fin (Nat.card fan.cones)) :
    fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support ⁻¹ᵁ
        (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support first).opensRange =
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular first)).opensRange := by
  ext source_point
  obtain ⟨second, chart_point, same⟩ :=
    (fan.divisorProjectiveChartCover 𝕜 complete regular).exists_eq source_point
  have source_same : fan.affineToricChartι 𝕜 regular
      (fan.divisorLocalCone 𝕜 complete regular second) chart_point = source_point := same
  rw [← source_same]
  change (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular second) chart_point) ∈
        (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support first).opensRange ↔
      fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular second) chart_point ∈
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular first)).opensRange
  have chart_equation := congrArg (fun morphism => morphism chart_point)
    (fan.allSectionProjectiveMonomialMap_chart 𝕜 complete regular divisor support second)
  change fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support
    (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular second) chart_point) =
      fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support second chart_point at chart_equation
  apply (congrArg (fun point => point ∈
    (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support first).opensRange)
      chart_equation).to_iff.trans
  change chart_point ∈ fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support second ⁻¹ᵁ
      (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support first).opensRange ↔ _
  rw [fan.allSectionProjectiveChartMap_preimage_vertex_of_strictSupport 𝕜
    complete regular divisor support strict_support first second]
  constructor
  · rintro ⟨overlap_point, rfl⟩
    refine ⟨fan.affineToricOverlapLeft 𝕜 (fan.divisorLocalCone 𝕜 complete regular first)
      (fan.divisorLocalCone 𝕜 complete regular second) overlap_point, ?_⟩
    exact congrArg (fun morphism => morphism overlap_point)
      (fan.affineToricOverlap_comp_affineToricChartι 𝕜 regular
        (fan.divisorLocalCone 𝕜 complete regular first) (fan.divisorLocalCone 𝕜 complete regular second))
  · rintro ⟨first_point, equality⟩
    obtain ⟨overlap_point, _, right_eq⟩ :=
      (fan.affineToricChartι_eq_affineToricChartι_iff 𝕜 regular first_point chart_point).mp equality
    exact ⟨overlap_point, right_eq⟩

@[reassoc]
theorem allSectionProjectiveAffineChartMap_chartInclusion (chart : Fin (Nat.card fan.cones)) :
    fan.allSectionProjectiveAffineChartMap 𝕜 complete regular divisor support chart ≫
        fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support chart =
      fan.allSectionProjectiveChartMap 𝕜 complete regular divisor support chart := rfl

def AllSectionProjectiveChartPullbacks : Prop :=
  ∀ chart : Fin (Nat.card fan.cones),
    IsPullback
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart))
      (fan.allSectionProjectiveAffineChartMap 𝕜 complete regular divisor support chart)
      (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
      (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support chart)

theorem allSectionProjectiveChartPullbacks_of_strictSupport
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis),
        fan.BasisDivisorStrictSupport basis cone_basis divisor) :
    fan.AllSectionProjectiveChartPullbacks 𝕜 complete regular divisor support := by
  intro chart
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact (fan.allSectionProjectiveMonomialMap_chart 𝕜 complete regular divisor support chart).trans
      (fan.allSectionProjectiveAffineChartMap_chartInclusion 𝕜 complete regular divisor support chart).symm
  · exact fan.allSectionProjectiveMonomialMap_preimage_vertex_of_strictSupport 𝕜
      complete regular divisor support strict_support chart

theorem allSectionProjectiveMonomialMap_isImmersion_of_chartPullbacks
    (steps : fan.AllSectionProjectiveStepsAdmissible complete regular divisor)
    (chart_pullbacks : fan.AllSectionProjectiveChartPullbacks 𝕜 complete regular divisor support) :
    IsImmersion (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support) := by
  classical
  let : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) := {
    postcomp := fun inclusion open_immersion morphism immersion => by
      let := open_immersion
      let := immersion
      infer_instance }
  let target_opens := fun chart : Fin (Nat.card fan.cones) =>
    (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support chart).opensRange
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) target_opens
  · rintro point ⟨source_point, rfl⟩
    obtain ⟨chart, chart_point, same⟩ :=
      (fan.divisorProjectiveChartCover 𝕜 complete regular).exists_eq source_point
    have chart_equation := congrArg (fun morphism => morphism chart_point)
      (fan.allSectionProjectiveMonomialMap_chart 𝕜 complete regular divisor support chart)
    have inclusion_equation := congrArg (fun morphism => morphism chart_point)
      (fan.allSectionProjectiveAffineChartMap_chartInclusion 𝕜 complete regular divisor support chart)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨chart, ?_⟩
    change fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support source_point ∈
      Set.range (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support chart)
    refine ⟨fan.allSectionProjectiveAffineChartMap 𝕜 complete regular divisor support chart chart_point, ?_⟩
    have source_same : fan.affineToricChartι 𝕜 regular
        (fan.divisorLocalCone 𝕜 complete regular chart) chart_point = source_point := same
    exact inclusion_equation.trans
      (chart_equation.symm.trans
        (congrArg (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support) source_same))
  · intro chart
    let square := chart_pullbacks chart
    let := fan.allDivisorMonomialAffineChartMap_isClosedImmersion_of_steps 𝕜
      (fan.divisorSectionChartBasis complete regular chart).val.2
      (fan.divisorSectionChartBasis complete regular chart).property.1 divisor
      (support _ _ _) (steps chart)
    have affine_immersion : IsImmersion
        (fan.allSectionProjectiveAffineChartMap 𝕜 complete regular divisor support chart) := by
      dsimp [allSectionProjectiveAffineChartMap]
      infer_instance
    have pullback_immersion : IsImmersion
        (Limits.pullback.snd
          (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
          (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support chart)) := by
      apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsImmersion)
        square.isoPullback.hom _).mp
      rw [square.isoPullback_hom_snd]
      exact affine_immersion
    exact (MorphismProperty.arrow_mk_iso_iff (P := @IsImmersion)
      (morphismRestrictOpensRange
        (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
        (fan.allSectionProjectiveChartInclusion 𝕜 complete regular divisor support chart))).mpr
      pullback_immersion

theorem allSectionProjectiveMonomialMap_isImmersion_of_strictSupport
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis),
        fan.BasisDivisorStrictSupport basis cone_basis divisor)
    (steps : fan.AllSectionProjectiveStepsAdmissible complete regular divisor) :
    IsImmersion (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support) :=
  fan.allSectionProjectiveMonomialMap_isImmersion_of_chartPullbacks 𝕜 complete regular divisor support
    steps (fan.allSectionProjectiveChartPullbacks_of_strictSupport 𝕜
      complete regular divisor support strict_support)

omit support in
theorem strictSupport_allSectionProjectiveMonomialMap_large_multiples_isImmersion
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis),
        fan.BasisDivisorStrictSupport basis cone_basis divisor) :
    ∃ threshold : ℕ, 0 < threshold ∧ ∀ multiple : ℕ, threshold ≤ multiple →
      ∃ multiple_support : fan.HasRaySupportInequalities (multiple • divisor),
        IsImmersion
          (fan.allSectionProjectiveMonomialMap 𝕜 complete regular (multiple • divisor) multiple_support) := by
  classical
  have local_thresholds : ∀ chart : Fin (Nat.card fan.cones),
      ∃ threshold : ℕ, 0 < threshold ∧ ∀ multiple : ℕ, threshold ≤ multiple →
        fan.BasisDivisorStepsAdmissible
          (fan.divisorSectionChartBasis complete regular chart).val.2
          (fan.divisorSectionChartBasis complete regular chart).property.1
          (multiple • divisor) := by
    intro chart
    exact fan.basisDivisorStepsAdmissible_large_multiples _ _ divisor (strict_support _ _ _)
  choose thresholds positives steps using local_thresholds
  obtain ⟨bound, bounds⟩ := Finite.exists_le thresholds
  refine ⟨bound + 1, by omega, ?_⟩
  intro multiple large
  have positive_multiple : (0 : ℤ) < multiple := by exact_mod_cast (by omega : 0 < multiple)
  have multiple_support : fan.HasRaySupportInequalities (multiple • divisor) := by
    intro dimension basis cone_basis
    exact fan.basisDivisor_multiple_admissible_of_strictSupport basis cone_basis divisor
      (strict_support _ _ _) multiple
  have multiple_strict : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis),
        fan.BasisDivisorStrictSupport basis cone_basis (multiple • divisor) := by
    intro dimension basis cone_basis ray outside
    rw [fan.coneDivisorCharacter_nsmul basis cone_basis divisor multiple]
    simp only [Finsupp.smul_apply, AddMonoidHom.nsmul_apply, Int.nsmul_eq_mul]
    have bound := mul_lt_mul_of_pos_left (strict_support _ basis cone_basis ray outside) positive_multiple
    simpa only [mul_neg] using bound
  have multiple_steps : fan.AllSectionProjectiveStepsAdmissible complete regular (multiple • divisor) :=
    fun chart => steps chart multiple ((bounds chart).trans (by omega))
  exact ⟨multiple_support, fan.allSectionProjectiveMonomialMap_isImmersion_of_strictSupport 𝕜
    complete regular (multiple • divisor) multiple_support multiple_strict multiple_steps⟩

end TauCeti.Toric.Fan
