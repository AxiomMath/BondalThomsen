module

public import BondalThomsen.Ports.Matroid.StandardRepresentation
public import Mathlib.Combinatorics.Matroid.Rank.ENat

@[expose] public section

namespace Matroid

open Set Submodule

variable {Label OtherLabel Field Vector OtherVector : Type*} [DivisionRing Field]
    [AddCommGroup Vector] [Module Field Vector]
    [AddCommGroup OtherVector] [Module Field OtherVector]
    {matroid : Matroid Label} {other : Matroid OtherLabel} {first second : Label}

def Parallel (matroid : Matroid Label) (first second : Label) : Prop :=
  matroid.IsNonloop first ∧ matroid.IsNonloop second ∧
    matroid.closure {first} = matroid.closure {second}

class Simple (matroid : Matroid Label) : Prop where
  parallel_iff_eq : ∀ {first second}, first ∈ matroid.E →
    (matroid.Parallel first second ↔ first = second)

def IsSimplification (smaller matroid : Matroid Label) : Prop :=
  smaller.Loopless ∧ smaller.IsRestriction matroid ∧
    ∀ element, matroid.IsNonloop element →
      ∃! representative, representative ∈ smaller.E ∧ matroid.Parallel element representative

theorem Parallel.symm (parallel : matroid.Parallel first second) :
    matroid.Parallel second first := ⟨parallel.2.1, parallel.1, parallel.2.2.symm⟩

theorem Parallel.trans {third : Label} (parallel : matroid.Parallel first second)
    (next : matroid.Parallel second third) : matroid.Parallel first third :=
  ⟨parallel.1, next.2.1, parallel.2.2.trans next.2.2⟩

theorem IsNonloop.parallel_self (nonloop : matroid.IsNonloop first) :
    matroid.Parallel first first := ⟨nonloop, nonloop, rfl⟩

theorem parallel_iff_isNonloop_isNonloop_indep_imp_eq :
    matroid.Parallel first second ↔ matroid.IsNonloop first ∧ matroid.IsNonloop second ∧
      (matroid.Indep {first, second} → first = second) := by
  constructor
  · rintro ⟨first_nonloop, second_nonloop, closures⟩
    refine ⟨first_nonloop, second_nonloop, ?_⟩
    intro independent
    by_contra different
    have outside := (second_nonloop.indep.notMem_closure_iff_of_notMem
      (by simpa using different) first_nonloop.mem_ground).mpr independent
    apply outside
    rw [← closures]
    exact matroid.mem_closure_self first first_nonloop.mem_ground
  · rintro ⟨first_nonloop, second_nonloop, independent_eq⟩
    by_cases same : first = second
    · subst second
      exact first_nonloop.parallel_self
    · have first_in : first ∈ matroid.closure {second} := by
        by_contra outside
        have independent := (second_nonloop.indep.notMem_closure_iff_of_notMem
          (by simpa using same) first_nonloop.mem_ground).mp outside
        exact same (independent_eq independent)
      have second_in := first_nonloop.mem_closure_singleton first_in
      exact ⟨first_nonloop, second_nonloop,
        Set.Subset.antisymm
          (matroid.closure_subset_closure_of_subset_closure
            (Set.singleton_subset_iff.mpr first_in))
          (matroid.closure_subset_closure_of_subset_closure
            (Set.singleton_subset_iff.mpr second_in))⟩

theorem simple_iff_forall_pair_indep : matroid.Simple ↔
    ∀ first second, first ∈ matroid.E → second ∈ matroid.E → matroid.Indep {first, second} := by
  constructor
  · intro simple first second first_member second_member
    have first_nonloop := ((@Simple.parallel_iff_eq _ matroid simple first first first_member).mpr
      rfl).1
    have second_nonloop := ((@Simple.parallel_iff_eq _ matroid simple second second second_member).mpr
      rfl).1
    by_cases same : first = second
    · subst second
      simpa using first_nonloop.indep
    · by_contra dependent
      have parallel := parallel_iff_isNonloop_isNonloop_indep_imp_eq.mpr
        ⟨first_nonloop, second_nonloop, fun independent => (dependent independent).elim⟩
      exact same ((@Simple.parallel_iff_eq _ matroid simple first second first_member).mp parallel)
  · intro pairs
    constructor
    intro first second first_member
    constructor
    · intro parallel
      exact (parallel_iff_isNonloop_isNonloop_indep_imp_eq.mp parallel).2.2
        (pairs first second first_member parallel.2.1.mem_ground)
    · rintro rfl
      have independent : matroid.Indep {first} := by simpa using pairs first first first_member first_member
      exact (indep_singleton.mp independent).parallel_self

theorem Indep.simple_of_contract_simple {contracted : Set Label}
    (independent : matroid.Indep contracted) (simple : (matroid.contract contracted).Simple) :
    matroid.Simple := by
  apply simple_iff_forall_pair_indep.mpr
  intro first second first_member second_member
  by_cases first_in : first ∈ contracted
  · by_cases second_in : second ∈ contracted
    · exact independent.subset (Set.pair_subset first_in second_in)
    · have nonloop : (matroid.contract contracted).IsNonloop second := by
        have pair := simple_iff_forall_pair_indep.mp simple second second
          ⟨second_member, second_in⟩ ⟨second_member, second_in⟩
        exact indep_singleton.mp (by simpa using pair)
      have union_independent := (independent.contract_indep_iff.mp nonloop.indep).2
      exact union_independent.subset (by intro element member; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at member; rcases member with rfl | rfl <;> simp_all)
  · by_cases second_in : second ∈ contracted
    · have nonloop : (matroid.contract contracted).IsNonloop first := by
        have pair := simple_iff_forall_pair_indep.mp simple first first
          ⟨first_member, first_in⟩ ⟨first_member, first_in⟩
        exact indep_singleton.mp (by simpa using pair)
      have union_independent := (independent.contract_indep_iff.mp nonloop.indep).2
      exact union_independent.subset (by intro element member; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at member; rcases member with rfl | rfl <;> simp_all)
    · exact (simple_iff_forall_pair_indep.mp simple first second
        ⟨first_member, first_in⟩ ⟨second_member, second_in⟩).of_contract

theorem Parallel.of_isRestriction {smaller : Matroid Label}
    (parallel : smaller.Parallel first second) (restriction : smaller.IsRestriction matroid) :
    matroid.Parallel first second := by
  have first_in : first ∈ smaller.closure {second} := by
    rw [← parallel.2.2]
    exact smaller.mem_closure_self first parallel.1.mem_ground
  have second_in : second ∈ smaller.closure {first} := by
    rw [parallel.2.2]
    exact smaller.mem_closure_self second parallel.2.1.mem_ground
  rw [← restriction.eq_restrict, matroid.restrict_closure_eq
    (Set.singleton_subset_iff.mpr parallel.2.1.mem_ground) restriction.subset] at first_in
  rw [← restriction.eq_restrict, matroid.restrict_closure_eq
    (Set.singleton_subset_iff.mpr parallel.1.mem_ground) restriction.subset] at second_in
  exact ⟨parallel.1.of_isRestriction restriction, parallel.2.1.of_isRestriction restriction,
    Set.Subset.antisymm
      (matroid.closure_subset_closure_of_subset_closure
        (Set.singleton_subset_iff.mpr first_in.1))
      (matroid.closure_subset_closure_of_subset_closure
        (Set.singleton_subset_iff.mpr second_in.1))⟩

theorem IsSimplification.exists_unique {smaller : Matroid Label}
    (simplification : smaller.IsSimplification matroid) (nonloop : matroid.IsNonloop first) :
    ∃! representative, representative ∈ smaller.E ∧ matroid.Parallel first representative :=
  simplification.2.2 first nonloop

theorem IsSimplification.eq_of_parallel {smaller : Matroid Label}
    (simplification : smaller.IsSimplification matroid)
    (first_member : first ∈ smaller.E) (second_member : second ∈ smaller.E)
    (parallel : matroid.Parallel first second) : first = second := by
  obtain ⟨representative, _, unique⟩ := simplification.exists_unique parallel.1
  exact (unique first ⟨first_member, parallel.1.parallel_self⟩).trans
    (unique second ⟨second_member, parallel⟩).symm

theorem IsSimplification.simple {smaller : Matroid Label}
    (simplification : smaller.IsSimplification matroid) : smaller.Simple := by
  have := simplification.1
  constructor
  intro first second first_member
  constructor
  · intro parallel
    exact simplification.eq_of_parallel first_member parallel.2.1.mem_ground
      (parallel.of_isRestriction simplification.2.1)
  · rintro rfl
    exact (smaller.isNonloop_of_loopless first_member).parallel_self

theorem IsSimplification.spanning {smaller : Matroid Label}
    (simplification : smaller.IsSimplification matroid) : matroid.Spanning smaller.E := by
  apply (matroid.spanning_iff smaller.E).mpr
  refine ⟨Set.Subset.antisymm (matroid.closure_subset_ground _) ?_, simplification.2.1.subset⟩
  intro element member
  rcases matroid.isLoop_or_isNonloop element member with loop | nonloop
  · exact loop.mem_closure _
  · obtain ⟨representative, ⟨representative_member, parallel⟩, _⟩ :=
      simplification.exists_unique nonloop
    have in_singleton : element ∈ matroid.closure {representative} := by
      rw [← parallel.2.2]
      exact matroid.mem_closure_self element member
    exact matroid.closure_subset_closure
      (Set.singleton_subset_iff.mpr representative_member) in_singleton

theorem IsSimplification.eRank_eq {smaller : Matroid Label}
    (simplification : smaller.IsSimplification matroid) : smaller.eRank = matroid.eRank := by
  rw [← simplification.2.1.eq_restrict]
  exact simplification.spanning.eRank_restrict

structure Iso (matroid : Matroid Label) (other : Matroid OtherLabel) where
  toEquiv : matroid.E ≃ other.E
  indep_image_iff' : ∀ selected : Set matroid.E,
    matroid.Indep (Subtype.val '' selected) ↔
      other.Indep (Subtype.val '' (toEquiv '' selected))

theorem Rep.ne_zero_iff_isNonloop (representation : matroid.Rep Field Vector) (element : Label) :
    representation element ≠ 0 ↔ matroid.IsNonloop element := by
  rw [Ne, representation.eq_zero_iff_not_indep, not_not, indep_singleton]

theorem Rep.parallel_iff_span_eq (representation : matroid.Rep Field Vector)
    (first : Label) (second : Label) :
    matroid.Parallel first second ↔ representation first ≠ 0 ∧ representation second ≠ 0 ∧
      span Field {representation first} = span Field {representation second} := by
  simp only [Parallel, ← representation.ne_zero_iff_isNonloop]
  constructor
  · rintro ⟨first_nonzero, second_nonzero, equality⟩
    have spans := representation.span_closure_congr equality
    refine ⟨first_nonzero, second_nonzero, ?_⟩
    simpa only [Set.image_singleton] using spans
  · rintro ⟨first_nonzero, second_nonzero, equality⟩
    refine ⟨first_nonzero, second_nonzero, ?_⟩
    rw [representation.closure_eq, representation.closure_eq, Set.image_singleton,
      Set.image_singleton, equality]

end Matroid
