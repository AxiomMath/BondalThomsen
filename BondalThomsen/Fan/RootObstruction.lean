module

public import BondalThomsen.Matroid.FourVertexDigraph
public import BondalThomsen.Ports.SupportingHull
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

namespace BondalThomsen

open Set Module

def directedRoot (source destination : Fin 4) : Fin 4 → ℝ :=
  Pi.single destination 1 - Pi.single source 1

noncomputable def rootPotentialFunctional (potential : Fin 4 → ℤ) :
    (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  (Pi.basisFun ℝ (Fin 4)).constr ℝ (fun vertex => (potential vertex : ℝ))

@[simp] theorem rootPotentialFunctional_directedRoot (potential : Fin 4 → ℤ)
    (source destination : Fin 4) :
    rootPotentialFunctional potential (directedRoot source destination) =
      (potential destination : ℝ) - potential source := by
  unfold directedRoot
  rw [map_sub, ← Pi.basisFun_apply ℝ (Fin 4) destination,
    ← Pi.basisFun_apply ℝ (Fin 4) source]
  simp only [rootPotentialFunctional, Basis.constr_basis]

def digraphRoots (graph : Digraph (Fin 4)) : Set (Fin 4 → ℝ) :=
  {vector | ∃ source destination, graph.Adj source destination ∧
    vector = directedRoot source destination}

def firstExposedRoots : Fin 4 → (Fin 4 → ℝ) :=
  ![directedRoot 0 1, directedRoot 1 3, directedRoot 0 2, directedRoot 2 3]

def secondExposedRoots : Fin 4 → (Fin 4 → ℝ) :=
  ![directedRoot 0 2, directedRoot 1 3, directedRoot 0 3, directedRoot 1 2]

theorem firstExposedRoots_parallelogram :
    firstExposedRoots 0 + firstExposedRoots 1 = firstExposedRoots 2 + firstExposedRoots 3 := by
  ext vertex
  simp [firstExposedRoots, directedRoot]

theorem secondExposedRoots_parallelogram :
    secondExposedRoots 0 + secondExposedRoots 1 = secondExposedRoots 2 + secondExposedRoots 3 := by
  ext vertex
  simp [secondExposedRoots, directedRoot]
  ring

theorem parallelogram_not_affineIndependent {Ambient : Type*} [AddCommGroup Ambient]
    [Module ℝ Ambient] (vertices : Fin 4 → Ambient)
    (opposite_sums : vertices 0 + vertices 1 = vertices 2 + vertices 3) :
    ¬ AffineIndependent ℝ vertices := by
  intro independent
  let weights : Fin 4 → ℝ := ![1, 1, -1, -1]
  have weights_zero : ∑ index, weights index = 0 := by
    norm_num [weights, Fin.sum_univ_succ]
  have combination_zero : ∑ index, weights index • vertices index = 0 := by
    simp [weights, Fin.sum_univ_succ]
    rw [← sub_eq_zero] at opposite_sums
    convert opposite_sums using 1; abel
  have coefficient := independent.eq_zero_of_sum_eq_zero weights_zero combination_zero
    0 (Finset.mem_univ _)
  norm_num [weights] at coefficient

theorem firstExposedRoots_injective : Function.Injective firstExposedRoots := by
  intro first second equality
  have coordinates := fun vertex => congrFun equality vertex
  have coordinate0 := coordinates 0
  have coordinate1 := coordinates 1
  fin_cases first <;> fin_cases second
  all_goals first | rfl |
    (solve | norm_num [firstExposedRoots, directedRoot, Pi.single_apply] at coordinate0) |
    (solve | norm_num [firstExposedRoots, directedRoot, Pi.single_apply] at coordinate1)

theorem secondExposedRoots_injective : Function.Injective secondExposedRoots := by
  intro first second equality
  have coordinates := fun vertex => congrFun equality vertex
  have coordinate0 := coordinates 0
  have coordinate1 := coordinates 1
  have coordinate2 := coordinates 2
  fin_cases first <;> fin_cases second
  all_goals first | rfl |
    (solve | norm_num [secondExposedRoots, directedRoot, Pi.single_apply] at coordinate0) |
    (solve | norm_num [secondExposedRoots, directedRoot, Pi.single_apply] at coordinate1) |
    (solve | norm_num [secondExposedRoots, directedRoot, Pi.single_apply] at coordinate2)

theorem parallelogram_not_subset_affineIndependent {Ambient Index : Type*}
    [AddCommGroup Ambient] [Module ℝ Ambient] (simplex : Index → Ambient)
    (independent : AffineIndependent ℝ simplex) (vertices : Fin 4 → Ambient)
    (distinct : Function.Injective vertices)
    (opposite_sums : vertices 0 + vertices 1 = vertices 2 + vertices 3)
    (contained : Set.range vertices ⊆ Set.range simplex) : False := by
  classical
  have representatives : ∀ index, ∃ chosen, simplex chosen = vertices index :=
    fun index => contained ⟨index, rfl⟩
  choose inclusion inclusion_eq using representatives
  have inclusion_injective : Function.Injective inclusion := by
    intro first second equality
    apply distinct
    rw [← inclusion_eq first, ← inclusion_eq second, equality]
  have independent_vertices := independent.comp_embedding ⟨inclusion, inclusion_injective⟩
  change AffineIndependent ℝ (simplex ∘ inclusion) at independent_vertices
  have equality : simplex ∘ inclusion = vertices := funext inclusion_eq
  rw [equality] at independent_vertices
  exact parallelogram_not_affineIndependent vertices opposite_sums independent_vertices

theorem firstRootHull_supporting (graph : Digraph (Fin 4)) (missing : ¬ graph.Adj 0 3) :
    convexHull ℝ (digraphRoots graph) ⊆
      {vector | rootPotentialFunctional firstRootPotential vector ≤ 1} := by
  apply convexHull_min
  · rintro vector ⟨source, destination, arrow, rfl⟩
    change rootPotentialFunctional firstRootPotential (directedRoot source destination) ≤ 1
    rw [rootPotentialFunctional_directedRoot]
    exact_mod_cast firstRootPotential_bound graph missing source destination arrow
  · exact convex_halfSpace_le
      ⟨(rootPotentialFunctional firstRootPotential).map_add,
        (rootPotentialFunctional firstRootPotential).map_smul⟩ 1

theorem secondRootHull_supporting (graph : Digraph (Fin 4)) :
    convexHull ℝ (digraphRoots graph) ⊆
      {vector | rootPotentialFunctional secondRootPotential vector ≤ 1} := by
  apply convexHull_min
  · rintro vector ⟨source, destination, _, rfl⟩
    change rootPotentialFunctional secondRootPotential (directedRoot source destination) ≤ 1
    rw [rootPotentialFunctional_directedRoot]
    exact_mod_cast secondRootPotential_bound source destination
  · exact convex_halfSpace_le
      ⟨(rootPotentialFunctional secondRootPotential).map_add,
        (rootPotentialFunctional secondRootPotential).map_smul⟩ 1

theorem firstExposedRoots_mem (graph : Digraph (Fin 4))
    (edge01 : graph.Adj 0 1) (edge02 : graph.Adj 0 2)
    (edge13 : graph.Adj 1 3) (edge23 : graph.Adj 2 3) (index : Fin 4) :
    firstExposedRoots index ∈ digraphRoots graph := by
  fin_cases index
  · exact ⟨0, 1, edge01, rfl⟩
  · exact ⟨1, 3, edge13, rfl⟩
  · exact ⟨0, 2, edge02, rfl⟩
  · exact ⟨2, 3, edge23, rfl⟩

theorem secondExposedRoots_mem (graph : Digraph (Fin 4))
    (edge02 : graph.Adj 0 2) (edge03 : graph.Adj 0 3)
    (edge12 : graph.Adj 1 2) (edge13 : graph.Adj 1 3) (index : Fin 4) :
    secondExposedRoots index ∈ digraphRoots graph := by
  fin_cases index
  · exact ⟨0, 2, edge02, rfl⟩
  · exact ⟨1, 3, edge13, rfl⟩
  · exact ⟨0, 3, edge03, rfl⟩
  · exact ⟨1, 2, edge12, rfl⟩

theorem firstRootGenerators_supporting_eq (graph : Digraph (Fin 4))
    (edge01 : graph.Adj 0 1) (edge02 : graph.Adj 0 2)
    (edge13 : graph.Adj 1 3) (edge23 : graph.Adj 2 3) :
    digraphRoots graph ∩ {vector | rootPotentialFunctional firstRootPotential vector = 1} =
      Set.range firstExposedRoots := by
  ext vector
  constructor
  · rintro ⟨⟨source, destination, _, rfl⟩, equality⟩
    change rootPotentialFunctional firstRootPotential (directedRoot source destination) = 1 at equality
    rw [rootPotentialFunctional_directedRoot] at equality
    have integer_equality : firstRootPotential destination - firstRootPotential source = 1 := by
      exact_mod_cast equality
    rcases (firstRootPotential_eq_one_iff source destination).mp integer_equality with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨index, rfl⟩
    refine ⟨firstExposedRoots_mem graph edge01 edge02 edge13 edge23 index, ?_⟩
    fin_cases index <;> norm_num [firstExposedRoots, firstRootPotential]

theorem secondRootGenerators_supporting_eq (graph : Digraph (Fin 4))
    (edge02 : graph.Adj 0 2) (edge03 : graph.Adj 0 3)
    (edge12 : graph.Adj 1 2) (edge13 : graph.Adj 1 3) :
    digraphRoots graph ∩ {vector | rootPotentialFunctional secondRootPotential vector = 1} =
      Set.range secondExposedRoots := by
  ext vector
  constructor
  · rintro ⟨⟨source, destination, _, rfl⟩, equality⟩
    change rootPotentialFunctional secondRootPotential (directedRoot source destination) = 1 at equality
    rw [rootPotentialFunctional_directedRoot] at equality
    have integer_equality : secondRootPotential destination - secondRootPotential source = 1 := by
      exact_mod_cast equality
    rcases (secondRootPotential_eq_one_iff source destination).mp integer_equality with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨index, rfl⟩
    refine ⟨secondExposedRoots_mem graph edge02 edge03 edge12 edge13 index, ?_⟩
    fin_cases index <;> norm_num [secondExposedRoots, secondRootPotential]

end BondalThomsen
