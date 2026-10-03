module

public import BondalThomsen.Matroid.MinorTransport
public import Mathlib.Combinatorics.Matroid.Map

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {matroid : Matroid Label} {first second : Label}

theorem Parallel.mem_closure_iff_mem_closure (parallel : matroid.Parallel first second)
    {selected : Set Label} :
    first ∈ matroid.closure selected ↔ second ∈ matroid.closure selected := by
  have first_in_second : first ∈ matroid.closure {second} := by
    rw [← parallel.2.2]
    exact matroid.mem_closure_self first parallel.1.mem_ground
  have second_in_first : second ∈ matroid.closure {first} := by
    rw [parallel.2.2]
    exact matroid.mem_closure_self second parallel.2.1.mem_ground
  constructor
  · intro member
    exact matroid.closure_subset_closure_of_subset_closure
      (singleton_subset_iff.mpr member) second_in_first
  · intro member
    exact matroid.closure_subset_closure_of_subset_closure
      (singleton_subset_iff.mpr member) first_in_second

theorem Parallel.insert_indep_iff (parallel : matroid.Parallel first second)
    {selected : Set Label} (first_absent : first ∉ selected)
    (second_absent : second ∉ selected) :
    matroid.Indep (insert first selected) ↔ matroid.Indep (insert second selected) := by
  by_cases independent : matroid.Indep selected
  · rw [independent.insert_indep_iff_of_notMem first_absent,
      independent.insert_indep_iff_of_notMem second_absent]
    simp only [mem_sdiff, parallel.1.mem_ground, parallel.2.1.mem_ground, true_and]
    exact not_congr parallel.mem_closure_iff_mem_closure
  · constructor <;> intro extended <;>
      exact (independent (extended.subset (subset_insert _ _))).elim

theorem Parallel.indep_substitute_iff (parallel : matroid.Parallel first second)
    {selected : Set Label} (first_member : first ∈ selected)
    (second_absent : second ∉ selected) :
    matroid.Indep selected ↔ matroid.Indep (insert second (selected \ {first})) := by
  have reduced : matroid.Indep (insert first (selected \ {first})) ↔
      matroid.Indep (insert second (selected \ {first})) :=
    parallel.insert_indep_iff (by simp) (fun member => second_absent member.1)
  simpa [insert_sdiff_singleton, insert_eq_of_mem first_member] using reduced

theorem Parallel.contract_delete_comm (parallel : matroid.Parallel first second) :
    (matroid.contract {first}).delete {second} =
      (matroid.contract {second}).delete {first} := by
  obtain rfl | distinct := eq_or_ne first second
  · rfl
  apply Matroid.ext_indep (by simp [Set.sdiff_sdiff_comm])
  intro selected selected_ground
  have first_absent : first ∉ selected := by
    intro member
    have ground := selected_ground member
    simp only [delete_ground, contract_ground, mem_sdiff, mem_singleton_iff] at ground
    exact ground.1.2 trivial
  have second_absent : second ∉ selected := by
    intro member
    have ground := selected_ground member
    simp only [delete_ground, contract_ground, mem_sdiff, mem_singleton_iff] at ground
    exact ground.2 trivial
  simpa [delete_indep_iff, parallel.1.contractElem_indep_iff,
    parallel.2.1.contractElem_indep_iff, Set.disjoint_singleton_right,
    first_absent, second_absent] using
      parallel.insert_indep_iff first_absent second_absent

theorem Parallel.isCircuit_pair (parallel : matroid.Parallel first second)
    (distinct : first ≠ second) : matroid.IsCircuit {first, second} :=
  (parallel.1.closure_eq_closure_iff_isCircuit_of_ne distinct).mp parallel.2.2

theorem Parallel.delete_ground_ncard (parallel : matroid.Parallel first second) :
    (matroid.delete {first}).E.ncard = matroid.E.ncard - 1 := by
  rw [delete_ground]
  exact Set.ncard_sdiff_singleton_of_mem parallel.1.mem_ground

private theorem swap_image_of_one_member [DecidableEq Label] {selected : Set Label}
    (first_member : first ∈ selected) (second_absent : second ∉ selected) :
    Equiv.swap first second '' selected = insert second (selected \ {first}) := by
  rw [Equiv.image_eq_preimage_symm, Equiv.symm_swap]
  ext element
  by_cases same_first : element = first
  · subst element
    have distinct : first ≠ second := by
      rintro rfl
      exact second_absent first_member
    simp [first_member, second_absent, distinct]
  · by_cases same_second : element = second
    · subst element
      simp [first_member]
    · simp [Equiv.swap_apply_of_ne_of_ne same_first same_second, same_first, same_second]

theorem Parallel.eq_mapEquiv_swap [DecidableEq Label]
    (parallel : matroid.Parallel first second) :
    matroid.mapEquiv (Equiv.swap first second) = matroid := by
  apply Matroid.ext_indep
    (by
      rw [mapEquiv_ground_eq]
      exact (Equiv.swap_bijOn_self
        (iff_of_true parallel.1.mem_ground parallel.2.1.mem_ground)).image_eq)
  intro selected _
  rw [mapEquiv_indep_iff, Equiv.symm_swap]
  by_cases first_member : first ∈ selected
  · by_cases second_member : second ∈ selected
    · rw [(Equiv.swap_bijOn_self (iff_of_true first_member second_member)).image_eq]
    · rw [swap_image_of_one_member first_member second_member]
      exact (parallel.indep_substitute_iff first_member second_member).symm
  · by_cases second_member : second ∈ selected
    · rw [Equiv.swap_comm, swap_image_of_one_member second_member first_member]
      exact (parallel.symm.indep_substitute_iff second_member first_member).symm
    · rw [(Equiv.swap_bijOn_self (iff_of_false first_member second_member)).image_eq]

theorem series_contract_ground_ncard (series : matroid✶.Parallel first second) :
    (matroid.contract {first}).E.ncard = matroid.E.ncard - 1 := by
  rw [contract_ground]
  exact Set.ncard_sdiff_singleton_of_mem (by simpa using series.1.mem_ground)

theorem circuit_ground_dual_singleton_isBase (circuit : matroid.IsCircuit matroid.E)
    (member : first ∈ matroid.E) : matroid✶.IsBase {first} := by
  have complement_base : matroid.IsBase (matroid.E \ {first}) :=
    isBasis_ground_iff.mp (circuit.sdiff_singleton_isBasis member)
  have dual_base := complement_base.compl_isBase_dual
  simpa only [Set.sdiff_sdiff_cancel_left (singleton_subset_iff.mpr member)] using dual_base

theorem circuit_ground_series (circuit : matroid.IsCircuit matroid.E)
    (first_member : first ∈ matroid.E) (second_member : second ∈ matroid.E) :
    matroid✶.Parallel first second := by
  have first_base := circuit_ground_dual_singleton_isBase circuit first_member
  have second_base := circuit_ground_dual_singleton_isBase circuit second_member
  exact ⟨indep_singleton.mp first_base.indep, indep_singleton.mp second_base.indep,
    first_base.closure_eq.trans second_base.closure_eq.symm⟩

end Matroid
