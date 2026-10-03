module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Tactic

@[expose] public section

namespace BondalThomsen

variable {Vertex : Type*}

@[instance_reducible] def digraphQuiver (graph : Digraph Vertex) : Quiver Vertex where
  Hom first second := PLift (graph.Adj first second)

def DigraphStronglyConnected (graph : Digraph Vertex) : Prop :=
  letI := digraphQuiver graph
  Quiver.IsStronglyConnected Vertex

def DigraphSemicomplete (graph : Digraph Vertex) : Prop :=
  ∀ first second, first ≠ second → graph.Adj first second ∨ graph.Adj second first

theorem digraph_path_stays_in_set (graph : Digraph Vertex) (vertices : Set Vertex)
    (closed : ∀ first ∈ vertices, ∀ second, graph.Adj first second → second ∈ vertices)
    {first second : Vertex} (first_mem : first ∈ vertices)
    (path : @Quiver.Path Vertex (digraphQuiver graph) first second) : second ∈ vertices := by
  induction path with
  | nil => exact first_mem
  | cons initial arrow induction => exact closed _ induction _ arrow.down

theorem stronglyConnected_exists_exit (graph : Digraph Vertex)
    (strong : DigraphStronglyConnected graph) (vertices : Set Vertex)
    (nonempty : vertices.Nonempty) (outside : ∃ vertex, vertex ∉ vertices) :
    ∃ first ∈ vertices, ∃ second, second ∉ vertices ∧ graph.Adj first second := by
  classical
  by_contra no_exit
  have closed : ∀ first ∈ vertices, ∀ second, graph.Adj first second → second ∈ vertices := by
    intro first first_mem second arrow
    by_contra second_outside
    exact no_exit ⟨first, first_mem, second, second_outside, arrow⟩
  obtain ⟨first, first_mem⟩ := nonempty
  obtain ⟨second, second_outside⟩ := outside
  let := digraphQuiver graph
  obtain ⟨path⟩ := Quiver.IsStronglyConnected.nonempty_path Vertex strong first second
  exact second_outside (digraph_path_stays_in_set graph vertices closed first_mem path)

def FourVertexHamiltonianCycle (graph : Digraph (Fin 4)) : Prop :=
  ∃ labeling : Equiv.Perm (Fin 4), graph.Adj (labeling 0) (labeling 1) ∧
    graph.Adj (labeling 1) (labeling 2) ∧ graph.Adj (labeling 2) (labeling 3) ∧
    graph.Adj (labeling 3) (labeling 0)

def FourVertexCycleOrders (graph : Digraph (Fin 4)) : Prop :=
  (graph.Adj 0 1 ∧ graph.Adj 1 2 ∧ graph.Adj 2 3 ∧ graph.Adj 3 0) ∨
  (graph.Adj 0 1 ∧ graph.Adj 1 3 ∧ graph.Adj 3 2 ∧ graph.Adj 2 0) ∨
  (graph.Adj 0 2 ∧ graph.Adj 2 1 ∧ graph.Adj 1 3 ∧ graph.Adj 3 0) ∨
  (graph.Adj 0 2 ∧ graph.Adj 2 3 ∧ graph.Adj 3 1 ∧ graph.Adj 1 0) ∨
  (graph.Adj 0 3 ∧ graph.Adj 3 1 ∧ graph.Adj 1 2 ∧ graph.Adj 2 0) ∨
  (graph.Adj 0 3 ∧ graph.Adj 3 2 ∧ graph.Adj 2 1 ∧ graph.Adj 1 0)

set_option maxHeartbeats 4000000 in

theorem stronglyConnected_semicomplete_four_cycle_orders (graph : Digraph (Fin 4))
    (strong : DigraphStronglyConnected graph) (semicomplete : DigraphSemicomplete graph) :
    FourVertexCycleOrders graph := by
  classical
  have exits : ∀ vertices : Finset (Fin 4), vertices.Nonempty → vertices ≠ Finset.univ →
      ∃ first ∈ vertices, ∃ second, second ∉ vertices ∧ graph.Adj first second := by
    intro vertices nonempty proper
    apply stronglyConnected_exists_exit graph strong vertices nonempty
    by_contra none
    apply proper
    ext vertex
    simp only [Finset.mem_univ, iff_true]
    by_contra outside
    exact none ⟨vertex, outside⟩
  have exit0 := exits {0} (by simp) (by decide)
  have exit1 := exits {1} (by simp) (by decide)
  have exit2 := exits {2} (by simp) (by decide)
  have exit3 := exits {3} (by simp) (by decide)
  have exit01 := exits {0, 1} (by simp) (by decide)
  have exit02 := exits {0, 2} (by simp) (by decide)
  have exit03 := exits {0, 3} (by simp) (by decide)
  have exit12 := exits {1, 2} (by simp) (by decide)
  have exit13 := exits {1, 3} (by simp) (by decide)
  have exit23 := exits {2, 3} (by simp) (by decide)
  have exit012 := exits {0, 1, 2} (by simp) (by decide)
  have exit013 := exits {0, 1, 3} (by simp) (by decide)
  have exit023 := exits {0, 2, 3} (by simp) (by decide)
  have exit123 := exits {1, 2, 3} (by simp) (by decide)
  have pair01 := semicomplete 0 1 (by decide)
  have pair02 := semicomplete 0 2 (by decide)
  have pair03 := semicomplete 0 3 (by decide)
  have pair12 := semicomplete 1 2 (by decide)
  have pair13 := semicomplete 1 3 (by decide)
  have pair23 := semicomplete 2 3 (by decide)
  simp [Fin.exists_fin_succ] at exit0 exit1 exit2 exit3 exit01 exit02 exit03 exit12 exit13 exit23 exit012 exit013 exit023 exit123
  clear exits strong semicomplete
  unfold FourVertexCycleOrders
  grind only

theorem four_cycle_orders_hamiltonian (graph : Digraph (Fin 4))
    (orders : FourVertexCycleOrders graph) : FourVertexHamiltonianCycle graph := by
  rcases orders with first | second | third | fourth | fifth | sixth
  · exact ⟨Equiv.refl _, first⟩
  · let labeling : Fin 4 → Fin 4 := ![0, 1, 3, 2]
    have bijective : Function.Bijective labeling := by decide
    exact ⟨Equiv.ofBijective labeling bijective, second⟩
  · let labeling : Fin 4 → Fin 4 := ![0, 2, 1, 3]
    have bijective : Function.Bijective labeling := by decide
    exact ⟨Equiv.ofBijective labeling bijective, third⟩
  · let labeling : Fin 4 → Fin 4 := ![0, 2, 3, 1]
    have bijective : Function.Bijective labeling := by decide
    exact ⟨Equiv.ofBijective labeling bijective, fourth⟩
  · let labeling : Fin 4 → Fin 4 := ![0, 3, 1, 2]
    have bijective : Function.Bijective labeling := by decide
    exact ⟨Equiv.ofBijective labeling bijective, fifth⟩
  · let labeling : Fin 4 → Fin 4 := ![0, 3, 2, 1]
    have bijective : Function.Bijective labeling := by decide
    exact ⟨Equiv.ofBijective labeling bijective, sixth⟩

theorem stronglyConnected_semicomplete_four_hamiltonian (graph : Digraph (Fin 4))
    (strong : DigraphStronglyConnected graph) (semicomplete : DigraphSemicomplete graph) :
    FourVertexHamiltonianCycle graph :=
  four_cycle_orders_hamiltonian graph
    (stronglyConnected_semicomplete_four_cycle_orders graph strong semicomplete)

def FourVertexNormalForm (graph : Digraph (Fin 4)) : Prop :=
  ∃ labeling : Equiv.Perm (Fin 4), graph.Adj (labeling 3) (labeling 0) ∧
    graph.Adj (labeling 0) (labeling 1) ∧ graph.Adj (labeling 0) (labeling 2) ∧
    graph.Adj (labeling 1) (labeling 3) ∧ graph.Adj (labeling 2) (labeling 3) ∧
    (graph.Adj (labeling 1) (labeling 2) ∨ graph.Adj (labeling 2) (labeling 1))

theorem four_hamiltonian_normal_form (graph : Digraph (Fin 4))
    (semicomplete : DigraphSemicomplete graph) (cycle : FourVertexHamiltonianCycle graph) :
    FourVertexNormalForm graph := by
  obtain ⟨labeling, cycle01, cycle12, cycle23, cycle30⟩ := cycle
  have pair02 := semicomplete (labeling 0) (labeling 2)
    (labeling.injective.ne (by decide))
  have pair13 := semicomplete (labeling 1) (labeling 3)
    (labeling.injective.ne (by decide))
  have finish : ∀ order : Equiv.Perm (Fin 4),
      graph.Adj (order 3) (order 0) → graph.Adj (order 0) (order 1) →
      graph.Adj (order 0) (order 2) → graph.Adj (order 1) (order 3) →
      graph.Adj (order 2) (order 3) → FourVertexNormalForm graph := by
    intro order edge30 edge01 edge02 edge13 edge23
    exact ⟨order, edge30, edge01, edge02, edge13, edge23,
      semicomplete (order 1) (order 2) (order.injective.ne (by decide))⟩
  rcases pair02 with diagonal02 | diagonal20 <;>
    rcases pair13 with diagonal13 | diagonal31
  · exact finish labeling cycle30 cycle01 diagonal02 diagonal13 cycle23
  · let rotation : Fin 4 → Fin 4 := ![3, 0, 1, 2]
    have bijective : Function.Bijective rotation := by decide
    exact finish ((Equiv.ofBijective rotation bijective).trans labeling)
      cycle23 cycle30 diagonal31 diagonal02 cycle12
  · let rotation : Fin 4 → Fin 4 := ![1, 2, 3, 0]
    have bijective : Function.Bijective rotation := by decide
    exact finish ((Equiv.ofBijective rotation bijective).trans labeling)
      cycle01 cycle12 diagonal13 diagonal20 cycle30
  · let rotation : Fin 4 → Fin 4 := ![2, 0, 3, 1]
    have bijective : Function.Bijective rotation := by decide
    exact finish ((Equiv.ofBijective rotation bijective).trans labeling)
      cycle12 diagonal20 cycle23 cycle01 diagonal31

theorem stronglyConnected_semicomplete_four_normal_form (graph : Digraph (Fin 4))
    (strong : DigraphStronglyConnected graph) (semicomplete : DigraphSemicomplete graph) :
    FourVertexNormalForm graph :=
  four_hamiltonian_normal_form graph semicomplete
    (stronglyConnected_semicomplete_four_hamiltonian graph strong semicomplete)

def firstRootPotential : Fin 4 → ℤ := ![-1, 0, 0, 1]

def secondRootPotential : Fin 4 → ℤ := ![0, 0, 1, 1]

theorem firstRootPotential_bound (graph : Digraph (Fin 4)) (missing : ¬ graph.Adj 0 3)
    (first second : Fin 4) (arrow : graph.Adj first second) :
    firstRootPotential second - firstRootPotential first ≤ 1 := by
  fin_cases first <;> fin_cases second <;> norm_num [firstRootPotential] at *
  exact missing arrow

theorem firstRootPotential_eq_one_iff (first second : Fin 4) :
    firstRootPotential second - firstRootPotential first = 1 ↔
      (first = 0 ∧ second = 1) ∨ (first = 0 ∧ second = 2) ∨
      (first = 1 ∧ second = 3) ∨ (first = 2 ∧ second = 3) := by
  fin_cases first <;> fin_cases second <;> norm_num [firstRootPotential]

theorem secondRootPotential_bound (first second : Fin 4) :
    secondRootPotential second - secondRootPotential first ≤ 1 := by
  fin_cases first <;> fin_cases second <;> norm_num [secondRootPotential]

theorem secondRootPotential_eq_one_iff (first second : Fin 4) :
    secondRootPotential second - secondRootPotential first = 1 ↔
      (first = 0 ∧ second = 2) ∨ (first = 0 ∧ second = 3) ∨
      (first = 1 ∧ second = 2) ∨ (first = 1 ∧ second = 3) := by
  fin_cases first <;> fin_cases second <;> norm_num [secondRootPotential]

end BondalThomsen
