module

public import BondalThomsen.Matroid.TUSigningCycles
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

@[expose] public section

namespace BondalThomsen

open SimpleGraph

def signingWalkProduct {Vertex : Type*} {graph : SimpleGraph Vertex}
    (sign : Vertex → Vertex → ℤ) {start finish : Vertex}
    (walk : graph.Walk start finish) : ℤ :=
  match walk with
  | .nil => 1
  | @SimpleGraph.Walk.cons _ _ source target _ _ tail =>
      sign source target * signingWalkProduct sign tail

theorem signingWalkProduct_append {Vertex : Type*} {graph : SimpleGraph Vertex}
    (sign : Vertex → Vertex → ℤ) {start middle finish : Vertex}
    (first : graph.Walk start middle) (second : graph.Walk middle finish) :
    signingWalkProduct sign (first.append second) =
      signingWalkProduct sign first * signingWalkProduct sign second := by
  induction first with
  | nil => simp [signingWalkProduct]
  | cons adjacent tail induction =>
      simp [signingWalkProduct, induction, mul_assoc]

theorem signingWalkProduct_reverse {Vertex : Type*} {graph : SimpleGraph Vertex}
    (sign : Vertex → Vertex → ℤ)
    (symmetric : ∀ source target, sign source target = sign target source)
    {start finish : Vertex} (walk : graph.Walk start finish) :
    signingWalkProduct sign walk.reverse = signingWalkProduct sign walk := by
  induction walk with
  | nil => rfl
  | @cons source target finish adjacent tail induction =>
      simp [SimpleGraph.Walk.reverse_cons, signingWalkProduct_append,
        signingWalkProduct, induction, symmetric target source, mul_comm]

theorem signingWalkProduct_isUnit {Vertex : Type*} {graph : SimpleGraph Vertex}
    (sign : Vertex → Vertex → ℤ)
    (units : ∀ source target, graph.Adj source target → IsUnit (sign source target))
    {start finish : Vertex} (walk : graph.Walk start finish) :
    IsUnit (signingWalkProduct sign walk) := by
  induction walk with
  | nil => exact isUnit_one
  | cons adjacent tail induction => exact (units _ _ adjacent).mul induction

theorem signingWalkProduct_square {Vertex : Type*} {graph : SimpleGraph Vertex}
    (sign : Vertex → Vertex → ℤ)
    (units : ∀ source target, graph.Adj source target → IsUnit (sign source target))
    {start finish : Vertex} (walk : graph.Walk start finish) :
    signingWalkProduct sign walk * signingWalkProduct sign walk = 1 := by
  rcases Int.isUnit_iff.mp (signingWalkProduct_isUnit sign units walk) with
    positive | negative
  · simp [positive]
  · simp [negative]

theorem signingWalkProduct_copy {Vertex : Type*} {graph : SimpleGraph Vertex}
    (sign : Vertex → Vertex → ℤ) {start finish new_start new_finish : Vertex}
    (walk : graph.Walk start finish) (first_eq : start = new_start)
    (second_eq : finish = new_finish) :
    signingWalkProduct sign (walk.copy first_eq second_eq) =
      signingWalkProduct sign walk := by
  subst new_start new_finish
  rfl

theorem closedWalk_vertex_index {Vertex : Type*} {graph : SimpleGraph Vertex}
    {start vertex : Vertex} (walk : graph.Walk start start)
    (positive_length : 0 < walk.length) (member : vertex ∈ walk.support) :
    ∃ index < walk.length, walk.getVert index = vertex := by
  obtain ⟨index, equality, bound⟩ := walk.mem_support_iff_exists_getVert.mp member
  by_cases strict : index < walk.length
  · exact ⟨index, strict, equality⟩
  · have last : index = walk.length := by omega
    refine ⟨0, positive_length, ?_⟩
    simpa only [last, SimpleGraph.Walk.getVert_length,
      SimpleGraph.Walk.getVert_zero] using equality

theorem cycle_chord_indices {Vertex : Type*} {graph : SimpleGraph Vertex}
    {start : Vertex} (walk : graph.Walk start start) (cycle : walk.IsCycle)
    (not_chordless : ¬walk.IsChordless) :
    ∃ first second : ℕ, first < second ∧ second < walk.length ∧
      2 ≤ second - first ∧ second - first + 2 ≤ walk.length ∧
      graph.Adj (walk.getVert first) (walk.getVert second) := by
  classical
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges] at not_chordless
  push Not at not_chordless
  obtain ⟨source, target, source_mem, target_mem, adjacent, not_edge⟩ := not_chordless
  have positive_length : 0 < walk.length := by have := cycle.three_le_length; omega
  obtain ⟨first, first_lt, first_eq⟩ := closedWalk_vertex_index walk positive_length source_mem
  obtain ⟨second, second_lt, second_eq⟩ := closedWalk_vertex_index walk positive_length target_mem
  have distinct : first ≠ second := by
    intro equality
    apply adjacent.ne
    rw [← first_eq, ← second_eq, equality]
  have ordered (first second : ℕ) (first_lt : first < walk.length)
      (second_lt : second < walk.length) (order : first < second)
      (adjacent : graph.Adj (walk.getVert first) (walk.getVert second))
      (not_edge : s(walk.getVert first, walk.getVert second) ∉ walk.edges) :
      2 ≤ second - first ∧ second - first + 2 ≤ walk.length := by
    have not_successive : second ≠ first + 1 := by
      intro equality
      apply not_edge
      apply walk.mk_mem_edges_iff_exists.mpr
      exact ⟨first, first_lt, by rw [equality]⟩
    have not_wrap : ¬(first = 0 ∧ second + 1 = walk.length) := by
      rintro ⟨rfl, last⟩
      apply not_edge
      apply walk.mk_mem_edges_iff_exists.mpr
      refine ⟨second, second_lt, ?_⟩
      rw [last, SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
      exact Sym2.eq_swap
    constructor <;> omega
  rcases lt_or_gt_of_ne distinct with order | order
  · have adjacent' : graph.Adj (walk.getVert first) (walk.getVert second) := by
      rwa [first_eq, second_eq]
    have not_edge' : s(walk.getVert first, walk.getVert second) ∉ walk.edges := by
      rwa [first_eq, second_eq]
    obtain ⟨distance, complement⟩ := ordered first second first_lt second_lt order
      adjacent' not_edge'
    exact ⟨first, second, order, second_lt, distance, complement, adjacent'⟩
  · have adjacent' : graph.Adj (walk.getVert second) (walk.getVert first) := by
      rw [first_eq, second_eq]
      exact adjacent.symm
    have not_edge' : s(walk.getVert second, walk.getVert first) ∉ walk.edges := by
      simpa only [first_eq, second_eq, Sym2.eq_swap] using not_edge
    obtain ⟨distance, complement⟩ := ordered second first second_lt first_lt order
      adjacent' not_edge'
    exact ⟨second, first, order, first_lt, distance, complement, adjacent'⟩

theorem closed_walk_products_of_chordless_cycle_products {Vertex : Type*}
    (graph : SimpleGraph Vertex) (sign : Vertex → Vertex → ℤ)
    (symmetric : ∀ source target, sign source target = sign target source)
    (units : ∀ source target, graph.Adj source target → IsUnit (sign source target))
    (chordless : ∀ start (walk : graph.Walk start start),
      walk.IsCycle → walk.IsChordless → signingWalkProduct sign walk = 1) :
    ∀ start (walk : graph.Walk start start), signingWalkProduct sign walk = 1 := by
  classical
  have by_length : ∀ length : ℕ, ∀ start (walk : graph.Walk start start),
      walk.length = length → signingWalkProduct sign walk = 1 := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length induction =>
      intro start walk length_eq
      cases walk with
      | nil => rfl
      | @cons source target finish adjacent tail =>
        by_cases path : tail.IsPath
        · by_cases long : 3 ≤ (SimpleGraph.Walk.cons adjacent tail).length
          · have cycle : (SimpleGraph.Walk.cons adjacent tail).IsCycle :=
              SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
                ⟨by simpa using path, long⟩
            by_cases no_chord : (SimpleGraph.Walk.cons adjacent tail).IsChordless
            · exact chordless _ _ cycle no_chord
            · obtain ⟨first, second, order, second_lt, distance, complement, chord⟩ :=
                cycle_chord_indices _ cycle no_chord
              let walk := SimpleGraph.Walk.cons adjacent tail
              let initial_walk := walk.take first
              let remaining := walk.drop first
              let middle := remaining.take (second - first)
              let suffix := remaining.drop (second - first)
              have middle_end : remaining.getVert (second - first) = walk.getVert second := by
                simp only [remaining, SimpleGraph.Walk.drop_getVert,
                  Nat.add_sub_of_le (Nat.le_of_lt order)]
              have edge : graph.Adj (walk.getVert first)
                  (remaining.getVert (second - first)) := by rwa [middle_end]
              have inside_length : (middle.append edge.symm.toWalk).length < length := by
                simp only [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk,
                  middle, remaining, SimpleGraph.Walk.take_length,
                  SimpleGraph.Walk.drop_length]
                change (SimpleGraph.Walk.cons adjacent tail).length = length at length_eq
                change second < (SimpleGraph.Walk.cons adjacent tail).length at second_lt
                omega
              have outside_length : (initial_walk.append (edge.toWalk.append suffix)).length <
                  length := by
                have walk_length : walk.length = length := length_eq
                simp only [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk,
                  initial_walk, suffix, remaining, SimpleGraph.Walk.take_length,
                  SimpleGraph.Walk.drop_length]
                change (SimpleGraph.Walk.cons adjacent tail).length = length at length_eq
                change second - first + 2 ≤ (SimpleGraph.Walk.cons adjacent tail).length
                  at complement
                change second < (SimpleGraph.Walk.cons adjacent tail).length at second_lt
                omega
              have inside := induction _ inside_length _ (middle.append edge.symm.toWalk) rfl
              have outside := induction _ outside_length _
                (initial_walk.append (edge.toWalk.append suffix)) rfl
              have reconstruction : initial_walk.append (middle.append suffix) = walk := by
                rw [show middle.append suffix = remaining from
                  SimpleGraph.Walk.append_take_drop_eq remaining (second - first)]
                exact SimpleGraph.Walk.append_take_drop_eq walk first
              have edge_square : sign (walk.getVert first)
                    (remaining.getVert (second - first)) *
                  sign (walk.getVert first) (remaining.getVert (second - first)) = 1 := by
                rcases Int.isUnit_iff.mp (units _ _ edge) with positive | negative
                · simp [positive]
                · simp [negative]
              simp only [signingWalkProduct_append, signingWalkProduct, mul_one,
                ← symmetric (walk.getVert first) (remaining.getVert (second - first))]
                at inside outside
              have middle_product : signingWalkProduct sign middle =
                  sign (walk.getVert first) (remaining.getVert (second - first)) := by
                calc
                  _ = signingWalkProduct sign middle *
                      (sign (walk.getVert first) (remaining.getVert (second - first)) *
                        sign (walk.getVert first) (remaining.getVert (second - first))) := by
                          rw [edge_square, mul_one]
                  _ = _ := by rw [← mul_assoc, inside, one_mul]
              change signingWalkProduct sign walk = 1
              rw [← reconstruction, signingWalkProduct_append, signingWalkProduct_append,
                middle_product]
              exact outside
          · cases tail with
            | nil => exact (adjacent.ne rfl).elim
            | @cons target middle source back rest =>
              have rest_zero : rest.length = 0 := by
                simp only [SimpleGraph.Walk.length_cons] at long
                omega
              have endpoint : middle = start := rest.eq_of_length_eq_zero rest_zero
              subst middle
              have rest_nil : rest = .nil := (rest.length_eq_zero_iff.mp rest_zero).eq_nil
              subst rest
              change sign start target * (sign target start * 1) = 1
              rw [← symmetric start target, mul_one]
              rcases Int.isUnit_iff.mp (units _ _ adjacent) with positive | negative
              · simp [positive]
              · simp [negative]
        · have repeated := (SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil (p := tail)).not.mp path
          push Not at repeated
          obtain ⟨vertex, loop, subwalk, not_nil⟩ := repeated
          obtain ⟨initial_walk, suffix, decomposition⟩ := subwalk
          have loop_positive : 0 < loop.length := by
            exact SimpleGraph.Walk.not_nil_iff_lt_length.mp not_nil
          have tail_decomposition : tail.length = initial_walk.length + loop.length + suffix.length := by
            rw [decomposition, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append]
          have loop_shorter : loop.length < length := by
            simp only [SimpleGraph.Walk.length_cons] at length_eq
            omega
          have reduced_shorter : (SimpleGraph.Walk.cons adjacent
              (initial_walk.append suffix)).length < length := by
            simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append] at *
            omega
          have loop_product := induction _ loop_shorter vertex loop rfl
          have reduced_product := induction _ reduced_shorter start
            (SimpleGraph.Walk.cons adjacent (initial_walk.append suffix)) rfl
          rw [decomposition]
          simpa only [signingWalkProduct, signingWalkProduct_append, loop_product,
            mul_one, mul_assoc] using reduced_product
  intro start walk
  exact by_length walk.length start walk rfl

theorem vertex_signs_of_closed_walk_products {Vertex : Type*}
    (graph : SimpleGraph Vertex) (sign : Vertex → Vertex → ℤ)
    (symmetric : ∀ source target, sign source target = sign target source)
    (units : ∀ source target, graph.Adj source target → IsUnit (sign source target))
    (closed : ∀ start (walk : graph.Walk start start), signingWalkProduct sign walk = 1) :
    ∃ vertex_sign : Vertex → ℤ,
      (∀ vertex, vertex_sign vertex = 1 ∨ vertex_sign vertex = -1) ∧
      ∀ source target, graph.Adj source target →
        sign source target = vertex_sign source * vertex_sign target := by
  classical
  let root : Vertex → Vertex := fun vertex => (graph.connectedComponentMk vertex).out
  have root_reachable (vertex : Vertex) : graph.Reachable (root vertex) vertex := by
    apply SimpleGraph.ConnectedComponent.exact
    exact Quot.out_eq (graph.connectedComponentMk vertex)
  let path : ∀ vertex, graph.Walk (root vertex) vertex :=
    fun vertex => Classical.choice (root_reachable vertex)
  let vertex_sign : Vertex → ℤ := fun vertex => signingWalkProduct sign (path vertex)
  refine ⟨vertex_sign, ?_, ?_⟩
  · intro vertex
    exact Int.isUnit_iff.mp (signingWalkProduct_isUnit sign units (path vertex))
  · intro source target adjacent
    have same_root : root source = root target := by
      unfold root
      rw [SimpleGraph.ConnectedComponent.sound adjacent.reachable]
    let target_path : graph.Walk (root source) target :=
      (path target).copy same_root.symm rfl
    have target_product : signingWalkProduct sign target_path = vertex_sign target := by
      exact signingWalkProduct_copy sign (path target) same_root.symm rfl
    have compatibility := closed (root source)
      (((path source).append adjacent.toWalk).append target_path.reverse)
    rw [signingWalkProduct_append, signingWalkProduct_append,
      signingWalkProduct_reverse sign symmetric, target_product] at compatibility
    change vertex_sign source * (sign source target * 1) * vertex_sign target = 1
      at compatibility
    have source_square := signingWalkProduct_square sign units (path source)
    have target_square := signingWalkProduct_square sign units (path target)
    change vertex_sign source * vertex_sign source = 1 at source_square
    change vertex_sign target * vertex_sign target = 1 at target_square
    calc
      sign source target = sign source target *
          (vertex_sign source * vertex_sign source) *
          (vertex_sign target * vertex_sign target) := by
            rw [source_square, target_square, mul_one, mul_one]
      _ = (vertex_sign source * sign source target * vertex_sign target) *
          (vertex_sign source * vertex_sign target) := by ring
      _ = vertex_sign source * vertex_sign target := by
        simpa only [mul_one, one_mul] using congrArg (fun value =>
          value * (vertex_sign source * vertex_sign target)) compatibility

theorem vertex_signs_of_chordless_cycle_products {Vertex : Type*}
    (graph : SimpleGraph Vertex) (sign : Vertex → Vertex → ℤ)
    (symmetric : ∀ source target, sign source target = sign target source)
    (units : ∀ source target, graph.Adj source target → IsUnit (sign source target))
    (chordless : ∀ start (walk : graph.Walk start start),
      walk.IsCycle → walk.IsChordless → signingWalkProduct sign walk = 1) :
    ∃ vertex_sign : Vertex → ℤ,
      (∀ vertex, vertex_sign vertex = 1 ∨ vertex_sign vertex = -1) ∧
      ∀ source target, graph.Adj source target →
        sign source target = vertex_sign source * vertex_sign target :=
  vertex_signs_of_closed_walk_products graph sign symmetric units
    (closed_walk_products_of_chordless_cycle_products graph sign symmetric units chordless)

def matrixSigningGraph {Row Column : Type*} (matrix : Matrix Row Column ℤ) :
    SimpleGraph (Row ⊕ Column) where
  Adj source target := match source, target with
    | .inl row, .inr column => matrix row column ≠ 0
    | .inr column, .inl row => matrix row column ≠ 0
    | _, _ => False
  symm := ⟨by intro source target adjacent; cases source <;> cases target <;> exact adjacent⟩
  loopless := ⟨by intro vertex; cases vertex <;> simp⟩

def matrixRelativeSigning {Row Column : Type*} (first second : Matrix Row Column ℤ)
    (source target : Row ⊕ Column) : ℤ :=
  match source, target with
  | .inl row, .inr column => tuRelativeSign first second row column
  | .inr column, .inl row => tuRelativeSign first second row column
  | _, _ => 1

theorem matrixRelativeSigning_symmetric {Row Column : Type*}
    (first second : Matrix Row Column ℤ) (source target : Row ⊕ Column) :
    matrixRelativeSigning first second source target =
      matrixRelativeSigning first second target source := by
  cases source <;> cases target <;> rfl

theorem row_column_signs_of_chordless_cycle_products {Row Column : Type*}
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (support : ∀ row column, first row column = 0 ↔ second row column = 0)
    (chordless : ∀ start (walk : (matrixSigningGraph first).Walk start start),
      walk.IsCycle → walk.IsChordless →
        signingWalkProduct (matrixRelativeSigning first second) walk = 1) :
    ∃ row_sign : Row → ℤ, ∃ column_sign : Column → ℤ,
      (∀ row, row_sign row = 1 ∨ row_sign row = -1) ∧
      (∀ column, column_sign column = 1 ∨ column_sign column = -1) ∧
      ∀ row column, second row column = row_sign row * first row column * column_sign column := by
  have units : ∀ source target, (matrixSigningGraph first).Adj source target →
      IsUnit (matrixRelativeSigning first second source target) := by
    intro source target adjacent
    cases source <;> cases target
    · exact adjacent.elim
    · exact tuRelativeSign_isUnit first_tu second_tu support adjacent
    · exact tuRelativeSign_isUnit first_tu second_tu support adjacent
    · exact adjacent.elim
  obtain ⟨vertex_sign, signs, switching⟩ := vertex_signs_of_chordless_cycle_products
    (matrixSigningGraph first) (matrixRelativeSigning first second)
    (matrixRelativeSigning_symmetric first second) units chordless
  refine ⟨fun row => vertex_sign (.inl row), fun column => vertex_sign (.inr column),
    fun row => signs (.inl row), fun column => signs (.inr column), ?_⟩
  intro row column
  by_cases zero : first row column = 0
  · simp [zero, (support row column).mp zero]
  · have edge := switching (.inl row) (.inr column) zero
    change tuRelativeSign first second row column =
      vertex_sign (.inl row) * vertex_sign (.inr column) at edge
    rw [← tuRelativeSign_recover first_tu support row column, edge]
    ring

theorem integral_equivalence_of_chordless_cycle_products {Row Column : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Column] [DecidableEq Column]
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (support : ∀ row column, first row column = 0 ↔ second row column = 0)
    (chordless : ∀ start (walk : (matrixSigningGraph first).Walk start start),
      walk.IsCycle → walk.IsChordless →
        signingWalkProduct (matrixRelativeSigning first second) walk = 1) :
    ∃ operation : (Matrix Row Row ℤ)ˣ,
      ∃ column_sign : Column → ℤ,
        (∀ column, column_sign column = 1 ∨ column_sign column = -1) ∧
        second = (operation : Matrix Row Row ℤ) * first * Matrix.diagonal column_sign := by
  obtain ⟨row_sign, column_sign, row_units, column_units, equality⟩ :=
    row_column_signs_of_chordless_cycle_products first second first_tu second_tu support chordless
  obtain ⟨operation, operation_eq⟩ :=
    integral_row_operation_of_signs first second row_sign column_sign row_units equality
  exact ⟨operation, column_sign, column_units, operation_eq⟩

end BondalThomsen
