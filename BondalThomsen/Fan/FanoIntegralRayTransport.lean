module

public import BondalThomsen.Fan.FanoFanDetermination
public import BondalThomsen.Fan.SmoothFanoCoordinateBounds
public import BondalThomsen.Rarity.FanClassTransport
public import BondalThomsen.Toric.Scheme.ConeEquivalenceRays

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Set BondalThomsen
open scoped Classical

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem isConeBasis_of_supporting_ray_simplex_of_strictSupport
    (fan : Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (strict : fan.HasStrictAnticanonicalConeSupport)
    (basis : Basis (Fin dimension) ℤ Lattice)
    (generators : Set.range (fun index => embedding (basis index)) ⊆ fan.rayGenerators)
    (functional : Ambient →ₗ[ℝ] ℝ)
    (values : ∀ index, functional (embedding (basis index)) = 1)
    (support : ∀ ray : fan.Ray, functional (embedding ray.val) ≤ 1) :
    fan.IsConeBasis basis := by
  classical
  let point := ∑ index, embedding (basis index)
  obtain ⟨size, adapted, adaptedCone, contains⟩ :=
    fan.exists_coneBasis_containing complete regular point
  have sizeEquality : size = dimension := by
    have basisRank := finrank_eq_card_basis basis
    have adaptedRank := finrank_eq_card_basis adapted
    simp only [Fintype.card_fin] at basisRank adaptedRank
    omega
  subst size
  let realAdapted := fan.lattice.isBaseChange.basis adapted
  have nonnegative : ∀ index, 0 ≤ realAdapted.repr point index := by
    apply (mem_basisCone_iff realAdapted point).mp
    convert contains using 1
    congr 1
    ext vector
    simp only [Set.mem_range]
    constructor <;> rintro ⟨index, rfl⟩ <;> refine ⟨index, ?_⟩
    · exact (fan.lattice.isBaseChange.basis_apply adapted index).symm
    · exact fan.lattice.isBaseChange.basis_apply adapted index
  have functionalOnAdapted : ∀ index, functional (realAdapted index) ≤ 1 := by
    intro index
    rw [show realAdapted index = embedding (adapted index) from
      fan.lattice.isBaseChange.basis_apply adapted index]
    exact support (fan.basisRay adapted adaptedCone index)
  have functionalValue : functional point = (dimension : ℝ) := by
    simp [point, map_sum, values]
  have functionalLeAdapted : functional point ≤ fan.supportingFunctional adapted point := by
    rw [fan.supportingFunctional_eq_sum_realCoordinates adapted]
    conv_lhs => rw [← realAdapted.sum_repr point]
    rw [map_sum]
    apply Finset.sum_le_sum
    intro index _
    rw [map_smul, smul_eq_mul]
    exact mul_le_of_le_one_right (nonnegative index) (functionalOnAdapted index)
  have adaptedOnBasis : ∀ index, fan.supportingFunctional adapted (embedding (basis index)) ≤ 1 := by
    intro index
    obtain ⟨ray, equality⟩ := generators ⟨index, rfl⟩
    change embedding ray.val = embedding (basis index) at equality
    exact equality ▸ fan.supportingFunctional_ray_le_one_of_strictSupport strict adapted adaptedCone ray
  have adaptedValue : fan.supportingFunctional adapted point = (dimension : ℝ) := by
    apply le_antisymm
    · simpa [point, map_sum] using Finset.sum_le_sum
        (fun index (_ : index ∈ Finset.univ) => adaptedOnBasis index)
    · rw [← functionalValue]
      exact functionalLeAdapted
  have allEqual : ∀ index, fan.supportingFunctional adapted (embedding (basis index)) = 1 := by
    have sumsEqual : ∑ index, fan.supportingFunctional adapted (embedding (basis index)) =
        ∑ _ : Fin dimension, (1 : ℝ) := by
      simpa [point, map_sum] using adaptedValue
    exact fun index => (Finset.sum_eq_sum_iff_of_le
      (fun index _ => adaptedOnBasis index)).mp sumsEqual index (Finset.mem_univ _)
  have generatorMatch : ∀ index, ∃ row, basis index = adapted row := by
    intro index
    obtain ⟨ray, rayEquality⟩ := generators ⟨index, rfl⟩
    change embedding ray.val = embedding (basis index) at rayEquality
    have equality := allEqual index
    rw [← rayEquality] at equality
    obtain ⟨row, vectorEquality⟩ :=
      (fan.supportingFunctional_ray_eq_one_iff_of_strictSupport strict adapted adaptedCone ray).mp equality
    exact ⟨row, fan.lattice.injective
      (rayEquality.symm.trans (congrArg embedding vectorEquality.symm))⟩
  choose matching matched using generatorMatch
  have matchingInjective : Function.Injective matching := by
    intro first second equality
    apply basis.injective
    rw [matched, matched, equality]
  have matchingSurjective := Finite.surjective_of_injective matchingInjective
  have generatingSetsEquality : Set.range (fun index => embedding (basis index)) =
      Set.range (fun index => embedding (adapted index)) := by
    ext vector
    constructor
    · rintro ⟨index, rfl⟩
      exact ⟨matching index, congrArg embedding (matched index).symm⟩
    · rintro ⟨row, rfl⟩
      obtain ⟨index, rfl⟩ := matchingSurjective row
      exact ⟨index, congrArg embedding (matched index)⟩
  change PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones
  rw [generatingSetsEquality]
  exact adaptedCone

end TauCeti.Toric.Fan

namespace BondalThomsen.ToricTransport

variable {SourceLattice TargetLattice SourceAmbient TargetAmbient : Type}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    [FiniteDimensional ℝ SourceAmbient] [FiniteDimensional ℝ TargetAmbient]
    {sourceEmbedding : SourceLattice →+ SourceAmbient}
    {targetEmbedding : TargetLattice →+ TargetAmbient}

omit [FiniteDimensional ℝ SourceAmbient] in
theorem map_cone_basis_of_rayGenerators_image_of_strictSupport
    (source : TauCeti.Toric.Fan sourceEmbedding) (target : TauCeti.Toric.Fan targetEmbedding)
    (sourceStrict : source.HasStrictAnticanonicalConeSupport)
    (targetComplete : target.IsComplete) (targetRegular : target.IsRegular)
    (targetStrict : target.HasStrictAnticanonicalConeSupport)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (sourceEmbedding vector) = targetEmbedding (lattice vector))
    (raySets : ambient '' source.rayGenerators = target.rayGenerators)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ SourceLattice)
    (coneBasis : source.IsConeBasis basis) : target.IsConeBasis (basis.map lattice) := by
  refine target.isConeBasis_of_supporting_ray_simplex_of_strictSupport targetComplete targetRegular
    targetStrict (basis.map lattice) ?_
    ((source.supportingFunctional basis).comp ambient.symm.toLinearMap) ?_ ?_
  · rintro vector ⟨index, rfl⟩
    change targetEmbedding ((basis.map lattice) index) ∈ target.rayGenerators
    rw [Basis.map_apply, ← embeddings, ← raySets]
    exact ⟨sourceEmbedding (basis index),
      source.basisGenerators_subset_rayGenerators basis coneBasis ⟨index, rfl⟩, rfl⟩
  · intro index
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.map_apply, ← embeddings,
      LinearEquiv.symm_apply_apply]
    exact source.supportingFunctional_basis basis index
  · intro ray
    have member : targetEmbedding ray.val ∈ ambient '' source.rayGenerators := by
      rw [raySets]
      exact ⟨ray, rfl⟩
    obtain ⟨_, ⟨sourceRay, rfl⟩, equality⟩ := member
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← equality, LinearEquiv.symm_apply_apply]
    exact source.supportingFunctional_ray_le_one_of_strictSupport sourceStrict basis coneBasis sourceRay

theorem map_cone_of_rayGenerators_image_of_strictSupport
    (source : TauCeti.Toric.Fan sourceEmbedding) (target : TauCeti.Toric.Fan targetEmbedding)
    (sourceComplete : source.IsComplete) (sourceRegular : source.IsRegular)
    (sourceStrict : source.HasStrictAnticanonicalConeSupport)
    (targetComplete : target.IsComplete) (targetRegular : target.IsRegular)
    (targetStrict : target.HasStrictAnticanonicalConeSupport)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (sourceEmbedding vector) = targetEmbedding (lattice vector))
    (raySets : ambient '' source.rayGenerators = target.rayGenerators)
    (cone : PointedCone ℝ SourceAmbient) (member : cone ∈ source.cones) :
    PointedCone.map ambient.toLinearMap cone ∈ target.cones := by
  obtain ⟨size, basis, coneBasis, face⟩ :=
    source.exists_coneBasis_above sourceComplete sourceRegular cone member
  have targetBasis := map_cone_basis_of_rayGenerators_image_of_strictSupport source target sourceStrict
    targetComplete targetRegular targetStrict lattice ambient embeddings raySets basis coneBasis
  have mappedFace := face.map ambient.toLinearMap ambient.injective
  rw [map_hull_eq] at mappedFace
  simp only [LinearEquiv.coe_coe] at mappedFace
  have generators : ambient '' Set.range (fun index => sourceEmbedding (basis index)) =
      Set.range (fun index => targetEmbedding ((basis.map lattice) index)) := by
    ext vector
    constructor
    · rintro ⟨_, ⟨index, rfl⟩, rfl⟩
      refine ⟨index, ?_⟩
      change targetEmbedding ((basis.map lattice) index) = ambient (sourceEmbedding (basis index))
      rw [Basis.map_apply, ← embeddings]
    · rintro ⟨index, rfl⟩
      refine ⟨sourceEmbedding (basis index), ⟨index, rfl⟩, ?_⟩
      change ambient (sourceEmbedding (basis index)) = targetEmbedding ((basis.map lattice) index)
      rw [Basis.map_apply, ← embeddings]
  rw [generators] at mappedFace
  exact target.mem_of_isFaceOf targetBasis mappedFace

theorem cones_iff_of_rayGenerators_image_of_strictSupport
    (source : TauCeti.Toric.Fan sourceEmbedding) (target : TauCeti.Toric.Fan targetEmbedding)
    (sourceComplete : source.IsComplete) (sourceRegular : source.IsRegular)
    (sourceStrict : source.HasStrictAnticanonicalConeSupport)
    (targetComplete : target.IsComplete) (targetRegular : target.IsRegular)
    (targetStrict : target.HasStrictAnticanonicalConeSupport)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (sourceEmbedding vector) = targetEmbedding (lattice vector))
    (raySets : ambient '' source.rayGenerators = target.rayGenerators)
    (cone : PointedCone ℝ SourceAmbient) :
    cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones := by
  constructor
  · exact map_cone_of_rayGenerators_image_of_strictSupport source target sourceComplete sourceRegular
      sourceStrict targetComplete targetRegular targetStrict lattice ambient embeddings raySets cone
  · intro member
    have inverseEmbeddings : ∀ vector, ambient.symm (targetEmbedding vector) =
        sourceEmbedding (lattice.symm vector) := by
      intro vector
      apply ambient.injective
      simp only [LinearEquiv.apply_symm_apply, embeddings]
    have inverseRays : ambient.symm '' target.rayGenerators = source.rayGenerators := by
      rw [← raySets, Set.image_image]
      simp
    have inverseMember := map_cone_of_rayGenerators_image_of_strictSupport target source targetComplete
      targetRegular targetStrict sourceComplete sourceRegular sourceStrict lattice.symm ambient.symm
      inverseEmbeddings inverseRays (PointedCone.map ambient.toLinearMap cone) member
    rwa [map_symm_map] at inverseMember

def integralRayFanEquivOfRayGeneratorsImageOfStrictSupport
    (source : TauCeti.Toric.Fan sourceEmbedding) (target : TauCeti.Toric.Fan targetEmbedding)
    (sourceComplete : source.IsComplete) (sourceRegular : source.IsRegular)
    (sourceStrict : source.HasStrictAnticanonicalConeSupport)
    (targetComplete : target.IsComplete) (targetRegular : target.IsRegular)
    (targetStrict : target.HasStrictAnticanonicalConeSupport)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (sourceEmbedding vector) = targetEmbedding (lattice vector))
    (raySets : ambient '' source.rayGenerators = target.rayGenerators) : IntegralRayFanEquiv source target :=
  IntegralRayFanEquiv.ofConeTransport lattice ambient embeddings
    (cones_iff_of_rayGenerators_image_of_strictSupport source target sourceComplete sourceRegular
      sourceStrict targetComplete targetRegular targetStrict lattice ambient embeddings raySets)

end BondalThomsen.ToricTransport

namespace BondalThomsen.ToricTransport

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def integralRayFanEquivOfNormalizedRayCoordinatesEq
    (source target : TauCeti.Toric.Fan embedding)
    (sourceComplete : source.IsComplete) (sourceRegular : source.IsRegular)
    (sourceStrict : source.HasStrictAnticanonicalConeSupport)
    (targetComplete : target.IsComplete) (targetRegular : target.IsRegular)
    (targetStrict : target.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (sourceBasis targetBasis : Basis (Fin dimension) ℤ Lattice)
    (sameCoordinates : source.normalizedRayCoordinates sourceBasis =
      target.normalizedRayCoordinates targetBasis) : IntegralRayFanEquiv source target := by
  let lattice := sourceBasis.equivFun.trans targetBasis.equivFun.symm
  let ambient := latticeEquivReal source target lattice
  have coordinateEquality {sourceRay : source.Ray} {targetRay : target.Ray}
      (equality : (fun index => sourceBasis.repr sourceRay.val index) =
        (fun index => targetBasis.repr targetRay.val index)) :
      lattice sourceRay.val = targetRay.val := by
    apply targetBasis.equivFun.injective
    ext index
    simpa only [lattice, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      Basis.equivFun_apply] using congrFun equality index
  have raySets : ambient '' source.rayGenerators = target.rayGenerators := by
    ext vector
    constructor
    · rintro ⟨_, ⟨sourceRay, rfl⟩, rfl⟩
      have member : (fun index => sourceBasis.repr sourceRay.val index) ∈
          target.normalizedRayCoordinates targetBasis := by
        rw [← sameCoordinates]
        exact ⟨sourceRay, rfl⟩
      obtain ⟨targetRay, equality⟩ := member
      refine ⟨targetRay, ?_⟩
      change embedding targetRay.val = latticeEquivReal source target lattice (embedding sourceRay.val)
      rw [latticeEquivReal_embedding, coordinateEquality equality.symm]
    · rintro ⟨targetRay, rfl⟩
      have member : (fun index => targetBasis.repr targetRay.val index) ∈
          source.normalizedRayCoordinates sourceBasis := by
        rw [sameCoordinates]
        exact ⟨targetRay, rfl⟩
      obtain ⟨sourceRay, equality⟩ := member
      refine ⟨embedding sourceRay.val, ⟨sourceRay, rfl⟩, ?_⟩
      change latticeEquivReal source target lattice (embedding sourceRay.val) = embedding targetRay.val
      rw [latticeEquivReal_embedding, coordinateEquality equality]
  exact integralRayFanEquivOfRayGeneratorsImageOfStrictSupport source target sourceComplete sourceRegular
    sourceStrict targetComplete targetRegular targetStrict lattice ambient
    (latticeEquivReal_embedding source target lattice) raySets

theorem integralFanClass_eq_of_normalizedRayCoordinates_eq
    (source target : TauCeti.Toric.Fan embedding)
    (sourceComplete : source.IsComplete) (sourceRegular : source.IsRegular)
    (sourceStrict : source.HasStrictAnticanonicalConeSupport)
    (targetComplete : target.IsComplete) (targetRegular : target.IsRegular)
    (targetStrict : target.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (sourceBasis targetBasis : Basis (Fin dimension) ℤ Lattice)
    (sameCoordinates : source.normalizedRayCoordinates sourceBasis =
      target.normalizedRayCoordinates targetBasis) : integralFanClass source = integralFanClass target := by
  exact integralFanClass_eq_of_equiv (integralRayFanEquivOfNormalizedRayCoordinatesEq source target
    sourceComplete sourceRegular sourceStrict targetComplete targetRegular targetStrict
    sourceBasis targetBasis sameCoordinates)

end BondalThomsen.ToricTransport
