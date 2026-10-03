module

public import BondalThomsen.Fan.FaceReconstruction
public import BondalThomsen.Matroid.RootConnectivity
public import BondalThomsen.Fan.ConeRayQuotient

@[expose] public section

namespace TauCeti.Toric.Fan

open Module Set BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] [Nontrivial Ambient]
    {embedding : Lattice →+ Ambient}

theorem supporting_rayGenerators_affineIndependent (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (functional : Ambient →ₗ[ℝ] ℝ)
    (bounded : ∀ vector ∈ fan.rayGenerators, functional vector ≤ 1) :
    AffineIndependent ℝ (fun vector :
      ↥(fan.rayGenerators ∩ {vector | functional vector = 1}) => vector.val) := by
  let face := fan.rayPolytope ∩ {vector | functional vector = 1}
  have polytope_bounded : ∀ vector ∈ fan.rayPolytope, functional vector ≤ 1 :=
    convexHull_min bounded (convex_halfSpace_le functional.isLinear 1)
  have exposed : IsExposed ℝ fan.rayPolytope face := by
    intro nonempty
    obtain ⟨point, point_member, point_value⟩ := nonempty
    refine ⟨functional.toContinuousLinearMap, ?_⟩
    ext vector
    constructor
    · rintro ⟨member, value⟩
      refine ⟨member, ?_⟩
      intro other other_member
      change functional other ≤ functional vector
      rw [value]
      exact polytope_bounded other other_member
    · rintro ⟨member, maximal⟩
      refine ⟨member, (polytope_bounded vector member).antisymm ?_⟩
      have lower := maximal point point_member
      change functional point ≤ functional vector at lower
      rwa [point_value] at lower
  have proper : face ≠ fan.rayPolytope := by
    intro equality
    have zero_member : (0 : Ambient) ∈ fan.rayPolytope :=
      interior_subset (fan.zero_mem_interior_rayPolytope_of_complete complete)
    rw [← equality] at zero_member
    have impossible := zero_member.2
    simp at impossible
  obtain ⟨basis, _, contained⟩ := fan.properFace_generators_subset_basis complete regular deep
    reference face exposed proper
  apply (fan.basisGenerators_affineIndependent basis).range.mono
  intro vector member
  exact contained ⟨member.1, subset_convexHull ℝ fan.rayGenerators member.1, member.2⟩

theorem no_supporting_ray_parallelogram (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (functional : Ambient →ₗ[ℝ] ℝ)
    (bounded : ∀ vector ∈ fan.rayGenerators, functional vector ≤ 1)
    (vertices : Fin 4 → Ambient) (distinct : Function.Injective vertices)
    (opposite_sums : vertices 0 + vertices 1 = vertices 2 + vertices 3)
    (on_face : ∀ index, vertices index ∈ fan.rayGenerators ∧ functional (vertices index) = 1) :
    False := by
  apply parallelogram_not_subset_affineIndependent _
    (fan.supporting_rayGenerators_affineIndependent complete regular deep reference functional
      bounded) vertices distinct opposite_sums
  rintro _ ⟨index, rfl⟩
  exact ⟨⟨vertices index, on_face index⟩, rfl⟩

theorem not_semicomplete_rootConfiguration (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (graph : Digraph (Fin 4)) (semicomplete : DigraphSemicomplete graph)
    (coordinates : Ambient →ₗ[ℝ] (Fin 4 → ℝ)) (injective : Function.Injective coordinates)
    (configuration : coordinates '' fan.rayGenerators = digraphRoots graph) : False := by
  have roots_generated : ∀ source destination,
      directedRoot source destination ∈ PointedCone.hull ℝ (digraphRoots graph) := by
    intro source destination
    by_cases same : source = destination
    · subst destination
      simp [directedRoot]
    · rcases semicomplete source destination same with forward | backward
      · exact PointedCone.subset_hull ⟨source, destination, forward, rfl⟩
      · have reverse_member : directedRoot destination source ∈ coordinates.range := by
          obtain ⟨vector, _, equality⟩ := Set.ext_iff.mp configuration
            (directedRoot destination source) |>.mpr ⟨destination, source, backward, rfl⟩
          exact ⟨vector, equality⟩
        have member : directedRoot source destination ∈ coordinates.range := by
          have negative := coordinates.range.neg_mem reverse_member
          simpa [directedRoot] using negative
        obtain ⟨vector, equality⟩ := member
        rw [← configuration, ← BondalThomsen.pointedCone_map_hull]
        refine ⟨vector, ?_, equality⟩
        rw [fan.hull_rayGenerators_eq_top complete]
        trivial
  obtain ⟨functional, roots, distinct_roots, sums, bounded_roots, roots_face⟩ :=
    stronglyConnected_semicomplete_four_root_obstruction graph
      (digraphStronglyConnected_of_root_hull graph roots_generated) semicomplete
  have preimages : ∀ index, ∃ vector,
      vector ∈ fan.rayGenerators ∧ coordinates vector = roots index := by
    intro index
    exact Set.ext_iff.mp configuration (roots index) |>.mpr (roots_face index).1
  choose vertices vertices_member vertices_coordinates using preimages
  have distinct : Function.Injective vertices := by
    intro first second equality
    apply distinct_roots
    rw [← vertices_coordinates first, ← vertices_coordinates second, equality]
  have opposite_sums : vertices 0 + vertices 1 = vertices 2 + vertices 3 := by
    apply injective
    simpa only [map_add, vertices_coordinates] using sums
  apply fan.no_supporting_ray_parallelogram complete regular deep reference
    (functional.comp coordinates) ?_ vertices distinct opposite_sums ?_
  · intro vector member
    exact bounded_roots _ (configuration ▸ Set.mem_image_of_mem coordinates member)
  · intro index
    exact ⟨vertices_member index, by
      change functional (coordinates (vertices index)) = 1
      rw [vertices_coordinates]
      exact (roots_face index).2⟩

end TauCeti.Toric.Fan
