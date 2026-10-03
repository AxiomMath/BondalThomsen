module

public import BondalThomsen.Fan.FourRootObstruction
public import Mathlib.Geometry.Convex.Cone.Pointed

@[expose] public section

namespace BondalThomsen

theorem linearFunctional_nonpositive_on_hull (points : Set (Fin 4 → ℝ))
    (functional : (Fin 4 → ℝ) →ₗ[ℝ] ℝ)
    (nonpositive : ∀ point ∈ points, functional point ≤ 0)
    (vector : Fin 4 → ℝ) (member : vector ∈ PointedCone.hull ℝ points) :
    functional vector ≤ 0 := by
  induction member using Submodule.span_induction with
  | mem vector member => exact nonpositive vector member
  | zero => simp
  | add first second _ _ first_nonpositive second_nonpositive =>
    rw [map_add]
    exact add_nonpos first_nonpositive second_nonpositive
  | smul coefficient vector _ vector_nonpositive =>
    change functional ((coefficient : ℝ) • vector) ≤ 0
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos coefficient.property vector_nonpositive

theorem digraphStronglyConnected_of_root_hull (graph : Digraph (Fin 4))
    (spanning : ∀ source destination,
      directedRoot source destination ∈ PointedCone.hull ℝ (digraphRoots graph)) :
    DigraphStronglyConnected graph := by
  classical
  let := digraphQuiver graph
  change ∀ source destination, Nonempty (Quiver.Path source destination)
  intro source destination
  by_contra unreachable
  let reachable : Set (Fin 4) := {vertex | Nonempty (Quiver.Path source vertex)}
  have source_reachable : source ∈ reachable := ⟨Quiver.Path.nil⟩
  have destination_outside : destination ∉ reachable := unreachable
  have closed : ∀ first ∈ reachable, ∀ second,
      graph.Adj first second → second ∈ reachable := by
    rintro first ⟨path⟩ second arrow
    exact ⟨path.cons ⟨arrow⟩⟩
  let potential : Fin 4 → ℤ := fun vertex => if vertex ∈ reachable then 0 else 1
  let functional := rootPotentialFunctional potential
  have bounded : ∀ vector ∈ digraphRoots graph, functional vector ≤ 0 := by
    rintro vector ⟨first, second, arrow, rfl⟩
    change rootPotentialFunctional potential (directedRoot first second) ≤ 0
    rw [rootPotentialFunctional_directedRoot]
    by_cases first_mem : first ∈ reachable
    · have second_mem := closed first first_mem second arrow
      simp [potential, first_mem, second_mem]
    · by_cases second_mem : second ∈ reachable <;> simp [potential, first_mem, second_mem]
  have impossible := linearFunctional_nonpositive_on_hull _ functional bounded
    (directedRoot source destination) (spanning source destination)
  change rootPotentialFunctional potential (directedRoot source destination) ≤ 0 at impossible
  rw [rootPotentialFunctional_directedRoot] at impossible
  norm_num [potential, source_reachable, destination_outside] at impossible

end BondalThomsen
