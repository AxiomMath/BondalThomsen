module

public import BondalThomsen.Matroid.TUSigningSwitching

@[expose] public section

namespace BondalThomsen

open SimpleGraph Finset

theorem matrixSigningGraph_adj_isLeft {Row Column : Type*}
    (matrix : Matrix Row Column ℤ) {source target : Row ⊕ Column}
    (adjacent : (matrixSigningGraph matrix).Adj source target) :
    source.isLeft = !target.isLeft := by
  cases source <;> cases target <;> simp_all [matrixSigningGraph]

theorem matrixSigningGraph_walk_alternates {Row Column : Type*}
    (matrix : Matrix Row Column ℤ) {start finish : Row ⊕ Column}
    (walk : (matrixSigningGraph matrix).Walk start finish) {index : ℕ}
    (bound : index ≤ walk.length) :
    (walk.getVert index).isLeft = if Even index then start.isLeft else !start.isLeft := by
  induction index with
  | zero => simp
  | succ index induction =>
      have previous := induction (by omega)
      have adjacent := matrixSigningGraph_adj_isLeft matrix
        (walk.adj_getVert_succ (i := index) (by omega))
      have next : (walk.getVert (index + 1)).isLeft = !(walk.getVert index).isLeft := by
        rw [adjacent]
        simp
      rw [next, previous]
      by_cases parity : Even index <;> simp [Nat.even_add_one, parity]

theorem matrixSigningGraph_closedWalk_even {Row Column : Type*}
    (matrix : Matrix Row Column ℤ) {start : Row ⊕ Column}
    (walk : (matrixSigningGraph matrix).Walk start start) : Even walk.length := by
  have alternation := matrixSigningGraph_walk_alternates matrix walk (le_refl walk.length)
  rw [SimpleGraph.Walk.getVert_length] at alternation
  by_contra odd
  cases start <;> simp [odd] at alternation

theorem signingWalkProduct_eq_prod_range {Vertex : Type*} {graph : SimpleGraph Vertex}
    (sign : Vertex → Vertex → ℤ) {start finish : Vertex} (walk : graph.Walk start finish) :
    signingWalkProduct sign walk =
      ∏ index ∈ range walk.length, sign (walk.getVert index) (walk.getVert (index + 1)) := by
  induction walk with
  | nil => simp [signingWalkProduct]
  | cons adjacent tail induction =>
      rw [SimpleGraph.Walk.length_cons, Finset.prod_range_succ']
      simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero,
        signingWalkProduct, induction]
      exact mul_comm _ _

theorem prod_range_two_mul (function : ℕ → ℤ) (length : ℕ) :
    (∏ index ∈ range (2 * length), function index) =
      ∏ index ∈ range length, function (2 * index) * function (2 * index + 1) := by
  induction length with
  | zero => simp
  | succ length induction =>
      rw [show 2 * (length + 1) = (2 * length + 1) + 1 by omega]
      rw [Finset.prod_range_succ, Finset.prod_range_succ, induction,
        Finset.prod_range_succ]
      exact mul_assoc _ _ _

theorem closedWalk_getVert_finRotate_two {Vertex : Type*} {graph : SimpleGraph Vertex}
    {start : Vertex} (walk : graph.Walk start start) {length : ℕ}
    (length_eq : walk.length = 2 * length) (index : Fin length) :
    walk.getVert (2 * (finRotate length index).val) = walk.getVert (2 * index.val + 2) := by
  cases length with
  | zero => exact Fin.elim0 index
  | succ length =>
      rw [coe_finRotate]
      split_ifs with last
      · have last_val : index.val = length := congrArg Fin.val last
        rw [last_val, show 2 * length + 2 = walk.length by omega]
        simp
      · congr 1

theorem matrixSigningGraph_cycle_indexing {Row Column : Type*}
    (matrix : Matrix Row Column ℤ) {start : Row}
    (walk : (matrixSigningGraph matrix).Walk (.inl start) (.inl start))
    (cycle : walk.IsCycle) :
    ∃ length : ℕ, 2 ≤ length ∧ walk.length = 2 * length ∧
      ∃ rows : Fin length → Row, ∃ columns : Fin length → Column,
        (∀ index, walk.getVert (2 * index.val) = .inl (rows index)) ∧
        (∀ index, walk.getVert (2 * index.val + 1) = .inr (columns index)) := by
  classical
  obtain ⟨length, length_eq⟩ := even_iff_exists_two_mul.mp
    (matrixSigningGraph_closedWalk_even matrix walk)
  have lower : 2 ≤ length := by have := cycle.three_le_length; omega
  have even_vertices : ∀ index : Fin length,
      ∃ row : Row, walk.getVert (2 * index.val) = .inl row := by
    intro index
    apply Sum.isLeft_iff.mp
    have alternation := matrixSigningGraph_walk_alternates matrix walk
      (index := 2 * index.val) (by omega)
    simpa using alternation
  have odd_vertices : ∀ index : Fin length,
      ∃ column : Column, walk.getVert (2 * index.val + 1) = .inr column := by
    intro index
    have alternation := matrixSigningGraph_walk_alternates matrix walk
      (index := 2 * index.val + 1) (by omega)
    cases vertex_eq : walk.getVert (2 * index.val + 1) with
    | inl row => simp [vertex_eq] at alternation
    | inr column => exact ⟨column, rfl⟩
  choose rows rows_eq using even_vertices
  choose columns columns_eq using odd_vertices
  exact ⟨length, lower, length_eq, rows, columns, rows_eq, columns_eq⟩

theorem matrixSigningGraph_chordless_submatrix_support {Row Column : Type*}
    (matrix : Matrix Row Column ℤ) {start : Row} {length : ℕ}
    (walk : (matrixSigningGraph matrix).Walk (.inl start) (.inl start))
    (cycle : walk.IsCycle) (chordless : walk.IsChordless)
    (length_eq : walk.length = 2 * length)
    (rows : Fin length → Row) (columns : Fin length → Column)
    (rows_eq : ∀ index, walk.getVert (2 * index.val) = .inl (rows index))
    (columns_eq : ∀ index, walk.getVert (2 * index.val + 1) = .inr (columns index)) :
    HasCycleSupport (matrix.submatrix rows columns) (finRotate length) := by
  intro row column not_diagonal not_next
  by_contra nonzero
  have adjacent : (matrixSigningGraph matrix).Adj
      (walk.getVert (2 * row.val)) (walk.getVert (2 * column.val + 1)) := by
    rw [rows_eq, columns_eq]
    exact nonzero
  have member := chordless.mem_edges (walk.getVert_mem_support (2 * row.val))
    (walk.getVert_mem_support (2 * column.val + 1)) adjacent
  obtain ⟨index, index_lt, edge_eq⟩ := walk.mk_mem_edges_iff_exists.mp member
  rcases Sym2.eq_iff.mp edge_eq with forward | backward
  · have index_eq : index = 2 * row.val :=
      cycle.getVert_injOn' (by change index ≤ walk.length - 1; omega)
        (by change 2 * row.val ≤ walk.length - 1; omega) forward.1
    have next_eq : index + 1 = 2 * column.val + 1 :=
      cycle.getVert_injOn (by constructor <;> omega) (by constructor <;> omega) forward.2
    apply not_diagonal
    apply Fin.ext
    omega
  · have index_eq : index = 2 * column.val + 1 :=
      cycle.getVert_injOn' (by change index ≤ walk.length - 1; omega)
        (by change 2 * column.val + 1 ≤ walk.length - 1; omega) backward.1
    have next_eq : walk.getVert (2 * (finRotate length column).val) =
        walk.getVert (2 * row.val) := by
      rw [closedWalk_getVert_finRotate_two walk length_eq, ← backward.2]
      congr 1
      omega
    have values_eq : 2 * (finRotate length column).val = 2 * row.val :=
      cycle.getVert_injOn'
        (by change 2 * (finRotate length column).val ≤ walk.length - 1
            have := (finRotate length column).isLt
            omega)
        (by change 2 * row.val ≤ walk.length - 1; omega) next_eq
    apply not_next
    apply Fin.ext
    omega

theorem signingWalkProduct_eq_cycle_matchings {Row Column : Type*}
    (first second : Matrix Row Column ℤ) {start : Row} {length : ℕ}
    (walk : (matrixSigningGraph first).Walk (.inl start) (.inl start))
    (length_eq : walk.length = 2 * length)
    (rows : Fin length → Row) (columns : Fin length → Column)
    (rows_eq : ∀ index, walk.getVert (2 * index.val) = .inl (rows index))
    (columns_eq : ∀ index, walk.getVert (2 * index.val + 1) = .inr (columns index)) :
    signingWalkProduct (matrixRelativeSigning first second) walk =
      (∏ index, tuRelativeSign first second (rows index) (columns index)) *
      (∏ index, tuRelativeSign first second (rows (finRotate length index))
        (columns index)) := by
  rw [signingWalkProduct_eq_prod_range, length_eq, prod_range_two_mul,
    Finset.prod_range, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro index member
  rw [rows_eq, columns_eq,
    show 2 * index.val + 1 + 1 = 2 * index.val + 2 by omega,
    ← closedWalk_getVert_finRotate_two walk length_eq, rows_eq]
  rfl

theorem tuRelativeSign_chordlessWalk_product_inl {Row Column : Type*}
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (support : ∀ row column, first row column = 0 ↔ second row column = 0)
    {start : Row}
    (walk : (matrixSigningGraph first).Walk (.inl start) (.inl start))
    (cycle : walk.IsCycle) (chordless : walk.IsChordless) :
    signingWalkProduct (matrixRelativeSigning first second) walk = 1 := by
  obtain ⟨length, lower, length_eq, rows, columns, rows_eq, columns_eq⟩ :=
    matrixSigningGraph_cycle_indexing first walk cycle
  rw [signingWalkProduct_eq_cycle_matchings first second walk length_eq
    rows columns rows_eq columns_eq]
  apply tuRelativeSign_chordlessCycle_product first second first_tu second_tu
    support lower rows columns
  · exact matrixSigningGraph_chordless_submatrix_support first walk cycle
      chordless length_eq rows columns rows_eq columns_eq
  · intro index
    have adjacent := walk.adj_getVert_succ (i := 2 * index.val) (by omega)
    rw [rows_eq, columns_eq] at adjacent
    exact adjacent
  · intro index
    have adjacent := walk.adj_getVert_succ (i := 2 * index.val + 1) (by omega)
    rw [columns_eq, show 2 * index.val + 1 + 1 = 2 * index.val + 2 by omega,
      ← closedWalk_getVert_finRotate_two walk length_eq, rows_eq] at adjacent
    exact adjacent

theorem signingWalkProduct_rotate {Vertex : Type*} {graph : SimpleGraph Vertex}
    [DecidableEq Vertex] (sign : Vertex → Vertex → ℤ) {start : Vertex}
    (walk : graph.Walk start start) (vertex : Vertex) (member : vertex ∈ walk.support) :
    signingWalkProduct sign (walk.rotate vertex member) = signingWalkProduct sign walk := by
  rw [SimpleGraph.Walk.rotate, signingWalkProduct_append]
  conv_rhs => rw [← SimpleGraph.Walk.take_spec walk member, signingWalkProduct_append]
  exact mul_comm _ _

theorem chordlessWalk_rotate {Vertex : Type*} {graph : SimpleGraph Vertex}
    [DecidableEq Vertex] {start : Vertex} (walk : graph.Walk start start)
    (chordless : walk.IsChordless) (vertex : Vertex) (member : vertex ∈ walk.support) :
    (walk.rotate vertex member).IsChordless := by
  apply SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mpr
  intro source target source_mem target_mem adjacent
  have edge := chordless.mem_edges
    ((walk.mem_support_rotate_iff vertex member).mp source_mem)
    ((walk.mem_support_rotate_iff vertex member).mp target_mem) adjacent
  exact (walk.rotate_edges vertex member).perm.mem_iff.mpr edge

theorem tuRelativeSign_chordlessWalk_product {Row Column : Type*}
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (support : ∀ row column, first row column = 0 ↔ second row column = 0)
    (start : Row ⊕ Column) (walk : (matrixSigningGraph first).Walk start start)
    (cycle : walk.IsCycle) (chordless : walk.IsChordless) :
    signingWalkProduct (matrixRelativeSigning first second) walk = 1 := by
  classical
  cases start with
  | inl row =>
      exact tuRelativeSign_chordlessWalk_product_inl first second first_tu second_tu
        support walk cycle chordless
  | inr column =>
      have positive : 0 < walk.length := by have := cycle.three_le_length; omega
      have adjacent := walk.adj_getVert_succ (i := 0) positive
      rw [SimpleGraph.Walk.getVert_zero] at adjacent
      cases vertex_eq : walk.getVert 1 with
      | inr next =>
          rw [vertex_eq] at adjacent
          exact adjacent.elim
      | inl row =>
          have member : Sum.inl row ∈ walk.support := by
            rw [← vertex_eq]
            exact walk.getVert_mem_support 1
          rw [← signingWalkProduct_rotate (matrixRelativeSigning first second)
            walk (.inl row) member]
          exact tuRelativeSign_chordlessWalk_product_inl first second first_tu second_tu
            support (walk.rotate (.inl row) member) (cycle.rotate member)
            (chordlessWalk_rotate walk chordless (.inl row) member)

theorem totallyUnimodular_integral_equivalence_of_support {Row Column : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Column] [DecidableEq Column]
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (support : ∀ row column, first row column = 0 ↔ second row column = 0) :
    ∃ operation : (Matrix Row Row ℤ)ˣ, ∃ column_sign : Column → ℤ,
      (∀ column, column_sign column = 1 ∨ column_sign column = -1) ∧
      second = (operation : Matrix Row Row ℤ) * first * Matrix.diagonal column_sign :=
  integral_equivalence_of_chordless_cycle_products first second first_tu second_tu support
    (tuRelativeSign_chordlessWalk_product first second first_tu second_tu support)

theorem totallyUnimodular_arbitrary_rank_integral_equivalence {Row Column : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Column] [DecidableEq Column]
    (first second : Matrix Row Column ℤ)
    (first_tu : first.IsTotallyUnimodular) (second_tu : second.IsTotallyUnimodular)
    (full_rank : (first.map (Int.castRingHom ℚ)).rank = Fintype.card Row)
    (matching : rayMatroid (Field := ℚ) (fun column row => (first row column : ℚ)) =
      rayMatroid (Field := ℚ) (fun column row => (second row column : ℚ))) :
    ∃ operation : (Matrix Row Row ℤ)ˣ, ∃ signs : Column → ℤ,
      (∀ column, signs column = 1 ∨ signs column = -1) ∧
      second = (operation : Matrix Row Row ℤ) * first * Matrix.diagonal signs := by
  obtain ⟨basis_columns, first_unit, second_unit⟩ := totallyUnimodular_exists_common_basis
    first second first_tu second_tu full_rank matching
  have normalized_matching :
      rayMatroid (Field := ℚ)
        (fun column row => (basisNormalization first basis_columns row column : ℚ)) =
      rayMatroid (Field := ℚ)
        (fun column row => (basisNormalization second basis_columns row column : ℚ)) := by
    rw [basisNormalization_rayMatroid first basis_columns first_unit,
      basisNormalization_rayMatroid second basis_columns second_unit, matching]
  obtain ⟨normalized_operation, signs, signed, equality⟩ :=
    totallyUnimodular_integral_equivalence_of_support
      (basisNormalization first basis_columns) (basisNormalization second basis_columns)
      (basisNormalization_totallyUnimodular first first_tu basis_columns first_unit)
      (basisNormalization_totallyUnimodular second second_tu basis_columns second_unit)
      (normalized_integer_matroid_support _ _ basis_columns
        (basisNormalization_basis_block first basis_columns first_unit)
        (basisNormalization_basis_block second basis_columns second_unit) normalized_matching)
  obtain ⟨operation, matrix_equality⟩ := integral_equivalence_of_basisNormalization_signs
    first second basis_columns first_unit second_unit normalized_operation signs equality
  exact ⟨operation, signs, signed, matrix_equality⟩

end BondalThomsen
