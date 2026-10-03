module

public import BondalThomsen.Fan.RootObstruction

@[expose] public section

namespace BondalThomsen

open Set

theorem four_normal_form_with_middle_arc (graph : Digraph (Fin 4))
    (normal : FourVertexNormalForm graph) :
    ∃ labeling : Equiv.Perm (Fin 4), graph.Adj (labeling 3) (labeling 0) ∧
      graph.Adj (labeling 0) (labeling 1) ∧ graph.Adj (labeling 0) (labeling 2) ∧
      graph.Adj (labeling 1) (labeling 3) ∧ graph.Adj (labeling 2) (labeling 3) ∧
      graph.Adj (labeling 1) (labeling 2) := by
  obtain ⟨labeling, edge30, edge01, edge02, edge13, edge23, middle⟩ := normal
  rcases middle with edge12 | edge21
  · exact ⟨labeling, edge30, edge01, edge02, edge13, edge23, edge12⟩
  · let exchange : Fin 4 → Fin 4 := ![0, 2, 1, 3]
    have bijective : Function.Bijective exchange := by decide
    exact ⟨(Equiv.ofBijective exchange bijective).trans labeling,
      edge30, edge02, edge01, edge23, edge13, edge21⟩

theorem normalized_four_root_obstruction (graph : Digraph (Fin 4))
    (edge01 : graph.Adj 0 1) (edge02 : graph.Adj 0 2)
    (edge13 : graph.Adj 1 3) (edge23 : graph.Adj 2 3) (edge12 : graph.Adj 1 2) :
    ∃ functional : (Fin 4 → ℝ) →ₗ[ℝ] ℝ, ∃ vertices : Fin 4 → (Fin 4 → ℝ),
      Function.Injective vertices ∧ vertices 0 + vertices 1 = vertices 2 + vertices 3 ∧
      (∀ vector ∈ digraphRoots graph, functional vector ≤ 1) ∧
      (∀ index, vertices index ∈ digraphRoots graph ∧ functional (vertices index) = 1) := by
  by_cases edge03 : graph.Adj 0 3
  · refine ⟨rootPotentialFunctional secondRootPotential, secondExposedRoots,
      secondExposedRoots_injective, secondExposedRoots_parallelogram,
      fun vector member => secondRootHull_supporting graph (subset_convexHull ℝ _ member), ?_⟩
    intro index
    have member : secondExposedRoots index ∈ Set.range secondExposedRoots := ⟨index, rfl⟩
    rw [← secondRootGenerators_supporting_eq graph edge02 edge03 edge12 edge13] at member
    exact member
  · refine ⟨rootPotentialFunctional firstRootPotential, firstExposedRoots,
      firstExposedRoots_injective, firstExposedRoots_parallelogram,
      fun vector member => firstRootHull_supporting graph edge03
        (subset_convexHull ℝ _ member), ?_⟩
    intro index
    have member : firstExposedRoots index ∈ Set.range firstExposedRoots := ⟨index, rfl⟩
    rw [← firstRootGenerators_supporting_eq graph edge01 edge02 edge13 edge23] at member
    exact member

theorem directedRoot_relabel (labeling : Equiv.Perm (Fin 4)) (source destination : Fin 4) :
    (LinearEquiv.funCongrLeft ℝ ℝ labeling.symm) (directedRoot source destination) =
      directedRoot (labeling source) (labeling destination) := by
  ext vertex
  change directedRoot source destination (labeling.symm vertex) =
    directedRoot (labeling source) (labeling destination) vertex
  simp only [directedRoot, Pi.sub_apply, Pi.single_apply]
  have destination_iff : labeling.symm vertex = destination ↔ vertex = labeling destination :=
    labeling.symm_apply_eq
  have source_iff : labeling.symm vertex = source ↔ vertex = labeling source :=
    labeling.symm_apply_eq
  simp only [destination_iff, source_iff]

theorem stronglyConnected_semicomplete_four_root_obstruction (graph : Digraph (Fin 4))
    (strong : DigraphStronglyConnected graph) (semicomplete : DigraphSemicomplete graph) :
    ∃ functional : (Fin 4 → ℝ) →ₗ[ℝ] ℝ, ∃ vertices : Fin 4 → (Fin 4 → ℝ),
      Function.Injective vertices ∧ vertices 0 + vertices 1 = vertices 2 + vertices 3 ∧
      (∀ vector ∈ digraphRoots graph, functional vector ≤ 1) ∧
      (∀ index, vertices index ∈ digraphRoots graph ∧ functional (vertices index) = 1) := by
  obtain ⟨labeling, _, edge01, edge02, edge13, edge23, edge12⟩ :=
    four_normal_form_with_middle_arc graph
      (stronglyConnected_semicomplete_four_normal_form graph strong semicomplete)
  let normalized : Digraph (Fin 4) := ⟨fun source destination =>
    graph.Adj (labeling source) (labeling destination)⟩
  obtain ⟨functional, vertices, distinct, opposite_sums, bounded, on_face⟩ :=
    normalized_four_root_obstruction normalized edge01 edge02 edge13 edge23 edge12
  let coordinates := LinearEquiv.funCongrLeft ℝ ℝ labeling.symm
  let transported_functional := functional.comp coordinates.symm.toLinearMap
  let transported_vertices := fun index => coordinates (vertices index)
  refine ⟨transported_functional, transported_vertices, coordinates.injective.comp distinct,
    ?_, ?_, ?_⟩
  · change coordinates (vertices 0) + coordinates (vertices 1) =
      coordinates (vertices 2) + coordinates (vertices 3)
    rw [← map_add, ← map_add, opposite_sums]
  · rintro vector ⟨source, destination, arrow, rfl⟩
    have root_member : directedRoot (labeling.symm source) (labeling.symm destination) ∈
        digraphRoots normalized := ⟨labeling.symm source, labeling.symm destination, by
      simpa only [normalized, labeling.apply_symm_apply] using arrow, rfl⟩
    have root_transport := directedRoot_relabel labeling (labeling.symm source)
      (labeling.symm destination)
    simp only [labeling.apply_symm_apply] at root_transport
    change functional (coordinates.symm (directedRoot source destination)) ≤ 1
    rw [← root_transport, LinearEquiv.symm_apply_apply]
    exact bounded _ root_member
  · intro index
    obtain ⟨⟨source, destination, arrow, equality⟩, value⟩ := on_face index
    refine ⟨⟨labeling source, labeling destination, arrow, ?_⟩, ?_⟩
    · change coordinates (vertices index) = directedRoot (labeling source) (labeling destination)
      rw [equality]
      exact directedRoot_relabel labeling source destination
    · change functional (coordinates.symm (coordinates (vertices index))) = 1
      simpa only [LinearEquiv.symm_apply_apply] using value

end BondalThomsen
