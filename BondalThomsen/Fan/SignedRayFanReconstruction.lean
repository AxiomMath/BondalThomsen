module

public import BondalThomsen.DeepFan.Theorems
public import BondalThomsen.DeepFan.UnconditionalRigidity
public import BondalThomsen.Toric.Scheme.RayEquivalenceRigidity

@[expose] public section

namespace TauCeti.Toric.Fan

open Module Set BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem isConeBasis_of_supporting_ray_simplex (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (basis : Basis (Fin dimension) ℤ Lattice)
    (generators : Set.range (fun index => embedding (basis index)) ⊆ fan.rayGenerators)
    (functional : Ambient →ₗ[ℝ] ℝ)
    (values : ∀ index, functional (embedding (basis index)) = 1)
    (support : ∀ ray : fan.Ray, functional (embedding ray.val) ≤ 1) :
    fan.IsConeBasis basis := by
  classical
  let point := ∑ index, embedding (basis index)
  obtain ⟨size, adapted, adapted_cone, contains⟩ :=
    fan.exists_coneBasis_containing complete regular point
  have size_eq : size = dimension := by
    have basis_rank := finrank_eq_card_basis basis
    have adapted_rank := finrank_eq_card_basis adapted
    simp only [Fintype.card_fin] at basis_rank adapted_rank
    omega
  subst size
  let real_adapted := fan.lattice.isBaseChange.basis adapted
  have nonnegative : ∀ index, 0 ≤ real_adapted.repr point index := by
    apply (mem_basisCone_iff real_adapted point).mp
    convert contains using 1
    congr 1
    ext vector
    simp only [Set.mem_range]
    constructor <;> rintro ⟨index, rfl⟩ <;> refine ⟨index, ?_⟩
    · exact (fan.lattice.isBaseChange.basis_apply adapted index).symm
    · exact fan.lattice.isBaseChange.basis_apply adapted index
  have functional_on_adapted : ∀ index, functional (real_adapted index) ≤ 1 := by
    intro index
    rw [show real_adapted index = embedding (adapted index) from
      fan.lattice.isBaseChange.basis_apply adapted index]
    exact support (fan.basisRay adapted adapted_cone index)
  have functional_value : functional point = (dimension : ℝ) := by
    simp [point, map_sum, values]
  have functional_le_adapted : functional point ≤ fan.supportingFunctional adapted point := by
    rw [fan.supportingFunctional_eq_sum_realCoordinates adapted]
    conv_lhs => rw [← real_adapted.sum_repr point]
    rw [map_sum]
    apply Finset.sum_le_sum
    intro index _
    rw [map_smul, smul_eq_mul]
    exact mul_le_of_le_one_right (nonnegative index) (functional_on_adapted index)
  have adapted_on_basis : ∀ index,
      fan.supportingFunctional adapted (embedding (basis index)) ≤ 1 := by
    intro index
    obtain ⟨ray, equality⟩ := generators ⟨index, rfl⟩
    change embedding ray.val = embedding (basis index) at equality
    exact equality ▸ fan.supportingFunctional_ray_le_one deep adapted adapted_cone ray
  have adapted_value : fan.supportingFunctional adapted point = (dimension : ℝ) := by
    apply le_antisymm
    · simpa [point, map_sum] using Finset.sum_le_sum
        (fun index (_ : index ∈ Finset.univ) => adapted_on_basis index)
    · rw [← functional_value]
      exact functional_le_adapted
  have all_equal : ∀ index, fan.supportingFunctional adapted (embedding (basis index)) = 1 := by
    have sums_equal :
        ∑ index, fan.supportingFunctional adapted (embedding (basis index)) =
          ∑ _ : Fin dimension, (1 : ℝ) := by
      simpa [point, map_sum] using adapted_value
    exact fun index => (Finset.sum_eq_sum_iff_of_le
      (fun index _ => adapted_on_basis index)).mp sums_equal index (Finset.mem_univ _)
  have generator_match : ∀ index, ∃ row, basis index = adapted row := by
    intro index
    obtain ⟨ray, ray_eq⟩ := generators ⟨index, rfl⟩
    change embedding ray.val = embedding (basis index) at ray_eq
    have equality := all_equal index
    rw [← ray_eq] at equality
    obtain ⟨row, same_vector⟩ :=
      (fan.supportingFunctional_ray_eq_one_iff deep adapted adapted_cone ray).mp equality
    exact ⟨row, fan.lattice.injective
      (ray_eq.symm.trans (congrArg embedding same_vector))⟩
  choose matching matched using generator_match
  have matching_injective : Function.Injective matching := by
    intro first_index second_index equality
    apply basis.injective
    rw [matched, matched, equality]
  have matching_surjective := Finite.surjective_of_injective matching_injective
  have generating_sets_eq : Set.range (fun index => embedding (basis index)) =
      Set.range (fun index => embedding (adapted index)) := by
    ext vector
    constructor
    · rintro ⟨index, rfl⟩
      exact ⟨matching index, congrArg embedding (matched index).symm⟩
    · rintro ⟨row, rfl⟩
      obtain ⟨index, rfl⟩ := matching_surjective row
      exact ⟨index, congrArg embedding (matched index)⟩
  change PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones
  rw [generating_sets_eq]
  exact adapted_cone

end TauCeti.Toric.Fan

namespace BondalThomsen.ToricTransport

open Module Set

variable {SourceLattice TargetLattice SourceAmbient TargetAmbient : Type*}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    [FiniteDimensional ℝ SourceAmbient] [FiniteDimensional ℝ TargetAmbient]
    {source_embedding : SourceLattice →+ SourceAmbient}
    {target_embedding : TargetLattice →+ TargetAmbient}

omit [FiniteDimensional ℝ SourceAmbient] in

theorem map_cone_basis_of_rayGenerators_image
    (source : TauCeti.Toric.Fan source_embedding) (target : TauCeti.Toric.Fan target_embedding)
    {dimension : ℕ} (source_deep : source.IsDeep dimension)
    (target_complete : target.IsComplete) (target_regular : target.IsRegular)
    (target_deep : target.IsDeep dimension)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (ray_sets : ambient '' source.rayGenerators = target.rayGenerators)
    (basis : Basis (Fin dimension) ℤ SourceLattice) (cone_basis : source.IsConeBasis basis) :
    target.IsConeBasis (basis.map lattice) := by
  refine target.isConeBasis_of_supporting_ray_simplex target_complete target_regular target_deep
    (basis.map lattice) ?_ ((source.supportingFunctional basis).comp ambient.symm.toLinearMap)
    ?_ ?_
  · rintro vector ⟨index, rfl⟩
    change target_embedding ((basis.map lattice) index) ∈ target.rayGenerators
    rw [Basis.map_apply, ← embeddings, ← ray_sets]
    exact ⟨source_embedding (basis index),
      source.basisGenerators_subset_rayGenerators basis cone_basis ⟨index, rfl⟩, rfl⟩
  · intro index
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.map_apply, ← embeddings,
      LinearEquiv.symm_apply_apply]
    exact source.supportingFunctional_basis basis index
  · intro ray
    have member : target_embedding ray.val ∈ ambient '' source.rayGenerators := by
      rw [ray_sets]
      exact ⟨ray, rfl⟩
    obtain ⟨_, ⟨source_ray, rfl⟩, equality⟩ := member
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← equality,
      LinearEquiv.symm_apply_apply]
    exact source.supportingFunctional_ray_le_one source_deep basis cone_basis source_ray

theorem cones_iff_of_rayGenerators_image
    (source : TauCeti.Toric.Fan source_embedding) (target : TauCeti.Toric.Fan target_embedding)
    {dimension : ℕ} (source_complete : source.IsComplete) (source_regular : source.IsRegular)
    (source_deep : source.IsDeep dimension) (target_complete : target.IsComplete)
    (target_regular : target.IsRegular) (target_deep : target.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ SourceLattice)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (ray_sets : ambient '' source.rayGenerators = target.rayGenerators)
    (cone : PointedCone ℝ SourceAmbient) :
    cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones := by
  have forward : ∀ cone : PointedCone ℝ SourceAmbient, cone ∈ source.cones →
      PointedCone.map ambient.toLinearMap cone ∈ target.cones := by
    intro cone member
    obtain ⟨size, basis, cone_basis, face⟩ :=
      source.exists_coneBasis_above source_complete source_regular cone member
    have size_eq : size = dimension := by
      have basis_rank := finrank_eq_card_basis basis
      have reference_rank := finrank_eq_card_basis reference
      simp only [Fintype.card_fin] at basis_rank reference_rank
      omega
    subst size
    have target_basis := map_cone_basis_of_rayGenerators_image source target source_deep
      target_complete target_regular target_deep lattice ambient embeddings ray_sets basis cone_basis
    have mapped_face := face.map ambient.toLinearMap ambient.injective
    rw [map_hull_eq] at mapped_face
    simp only [LinearEquiv.coe_coe] at mapped_face
    have generators : ambient '' Set.range (fun index => source_embedding (basis index)) =
        Set.range (fun index => target_embedding ((basis.map lattice) index)) := by
      ext vector
      constructor
      · rintro ⟨_, ⟨index, rfl⟩, rfl⟩
        refine ⟨index, ?_⟩
        change target_embedding ((basis.map lattice) index) = ambient (source_embedding (basis index))
        rw [Basis.map_apply, ← embeddings]
      · rintro ⟨index, rfl⟩
        refine ⟨source_embedding (basis index), ⟨index, rfl⟩, ?_⟩
        change ambient (source_embedding (basis index)) = target_embedding ((basis.map lattice) index)
        rw [Basis.map_apply, ← embeddings]
    rw [generators] at mapped_face
    exact target.mem_of_isFaceOf target_basis mapped_face
  constructor
  · exact forward cone
  · intro member
    have inverse_embeddings : ∀ vector,
        ambient.symm (target_embedding vector) = source_embedding (lattice.symm vector) := by
      intro vector
      apply ambient.injective
      simp only [LinearEquiv.apply_symm_apply, embeddings, LinearEquiv.apply_symm_apply]
    have inverse_rays : ambient.symm '' target.rayGenerators = source.rayGenerators := by
      rw [← ray_sets, Set.image_image]
      simp
    obtain ⟨size, basis, cone_basis, face⟩ :=
      target.exists_coneBasis_above target_complete target_regular
        (PointedCone.map ambient.toLinearMap cone) member
    have size_eq : size = dimension := by
      have basis_rank := finrank_eq_card_basis basis
      have reference_rank := finrank_eq_card_basis (reference.map lattice)
      simp only [Fintype.card_fin] at basis_rank reference_rank
      omega
    subst size
    have source_basis := map_cone_basis_of_rayGenerators_image target source target_deep
      source_complete source_regular source_deep lattice.symm ambient.symm inverse_embeddings
      inverse_rays basis cone_basis
    have mapped_face := face.map ambient.symm.toLinearMap ambient.symm.injective
    rw [map_symm_map, map_hull_eq] at mapped_face
    simp only [LinearEquiv.coe_coe] at mapped_face
    have generators : ambient.symm '' Set.range (fun index => target_embedding (basis index)) =
        Set.range (fun index => source_embedding ((basis.map lattice.symm) index)) := by
      ext vector
      constructor
      · rintro ⟨_, ⟨index, rfl⟩, rfl⟩
        refine ⟨index, ?_⟩
        change source_embedding ((basis.map lattice.symm) index) =
          ambient.symm (target_embedding (basis index))
        rw [Basis.map_apply, ← inverse_embeddings]
      · rintro ⟨index, rfl⟩
        refine ⟨target_embedding (basis index), ⟨index, rfl⟩, ?_⟩
        change ambient.symm (target_embedding (basis index)) =
          source_embedding ((basis.map lattice.symm) index)
        rw [Basis.map_apply, ← inverse_embeddings]
    rw [generators] at mapped_face
    exact source.mem_of_isFaceOf source_basis mapped_face

theorem exists_integralRayFanEquiv_of_rayGenerators_image
    (source : TauCeti.Toric.Fan source_embedding) (target : TauCeti.Toric.Fan target_embedding)
    {dimension : ℕ} (source_complete : source.IsComplete) (source_regular : source.IsRegular)
    (source_deep : source.IsDeep dimension) (target_complete : target.IsComplete)
    (target_regular : target.IsRegular) (target_deep : target.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ SourceLattice)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (ray_sets : ambient '' source.rayGenerators = target.rayGenerators) :
    ∃ equivalence : IntegralRayFanEquiv source target,
      equivalence.lattice = lattice ∧ equivalence.ambient = ambient := by
  classical
  have ray_image : ∀ ray : source.Ray, ∃ target_ray : target.Ray,
      lattice ray.val = target_ray.val := by
    intro ray
    have member : ambient (source_embedding ray.val) ∈ target.rayGenerators := by
      rw [← ray_sets]
      exact ⟨source_embedding ray.val, ⟨ray, rfl⟩, rfl⟩
    obtain ⟨target_ray, equality⟩ := member
    change target_embedding target_ray.val = ambient (source_embedding ray.val) at equality
    exact ⟨target_ray, target.lattice.injective ((embeddings ray.val).symm.trans equality.symm)⟩
  choose ray_map ray_vectors using ray_image
  have injective : Function.Injective ray_map := by
    intro first_ray second_ray equality
    apply Subtype.ext
    apply lattice.injective
    rw [ray_vectors, ray_vectors, equality]
  have surjective : Function.Surjective ray_map := by
    intro target_ray
    have member : target_embedding target_ray.val ∈ ambient '' source.rayGenerators := by
      rw [ray_sets]
      exact ⟨target_ray, rfl⟩
    obtain ⟨_, ⟨source_ray, rfl⟩, equality⟩ := member
    refine ⟨source_ray, Subtype.ext ?_⟩
    apply target.lattice.injective
    rw [← ray_vectors, ← embeddings]
    exact equality
  let rays := Equiv.ofBijective ray_map ⟨injective, surjective⟩
  refine ⟨{ lattice := lattice
            ambient := ambient
            embeddings := embeddings
            rays := rays
            ray_vectors := ray_vectors
            cones := ?_ }, rfl, rfl⟩
  exact cones_iff_of_rayGenerators_image source target source_complete source_regular
    source_deep target_complete target_regular target_deep reference lattice ambient embeddings ray_sets

end BondalThomsen.ToricTransport
