module

public import Mathlib.Combinatorics.Matroid.Minor.Order
public import Mathlib.Combinatorics.Matroid.Loop

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {matroid smaller : Matroid Label}

theorem IsMinor.exists_contract_indep_delete_coindep (minor : smaller ≤m matroid) :
    ∃ contracted deleted, matroid.Indep contracted ∧ matroid.Coindep deleted ∧
      Disjoint contracted deleted ∧ smaller = (matroid.contract contracted).delete deleted := by
  suffices auxiliary : ∀ (intermediate : Matroid Label) (contracted : Set Label),
      contracted ⊆ intermediate.E →
      ∃ independent deleted, Disjoint independent deleted ∧ intermediate.Indep independent ∧
        intermediate.Coindep deleted ∧
        (intermediate.contract independent).delete deleted = intermediate.contract contracted by
    obtain ⟨contracted, deleted, contracted_subset, deleted_subset, disjoint, rfl⟩ :=
      minor.exists_eq_contract_delete_disjoint
    obtain ⟨first, second, first_second, first_indep, second_coindep, first_eq⟩ :=
      auxiliary (matroid.contract contracted)✶ deleted
        (subset_sdiff.mpr ⟨deleted_subset, disjoint.symm⟩)
    obtain ⟨third, fourth, third_fourth, third_indep, fourth_coindep, second_eq⟩ :=
      auxiliary matroid contracted contracted_subset
    rw [← second_eq, dual_coindep_iff, delete_indep_iff, third_indep.contract_indep_iff,
      union_comm] at second_coindep
    rw [← second_eq, dual_contract_delete, ← contract_delete_comm _ third_fourth.symm,
      delete_indep_iff, fourth_coindep.indep.contract_indep_iff] at first_indep
    refine ⟨third ∪ second, first ∪ fourth, second_coindep.1.2, first_indep.1.2, by tauto_set, ?_⟩
    rw [← dual_inj, dual_contract_delete, eq_comm, dual_contract, dual_dual] at first_eq
    rw [first_eq, ← second_eq, delete_delete,
      contract_delete_contract _ _ _ _ (by tauto_set), union_comm first]
  intro intermediate contracted contracted_subset
  obtain ⟨basisSet, basis⟩ := intermediate.exists_isBasis contracted
  refine ⟨basisSet, contracted \ basisSet, disjoint_sdiff_right, basis.indep, ?_,
    basis.contract_eq_contract_delete.symm⟩
  refine Indep.of_delete (D := basisSet) ((coloops_indep _).subset ?_)
  rw [← dual_contract, dual_coloops, contract_loops_eq, basis.closure_eq_closure]
  exact sdiff_subset_sdiff_left (intermediate.subset_closure contracted contracted_subset)

theorem IsMinor.exists_spanning_isRestriction_contract (minor : smaller ≤m matroid) :
    ∃ contracted, matroid.Indep contracted ∧ smaller.IsRestriction (matroid.contract contracted) ∧
      (matroid.contract contracted).closure smaller.E = (matroid.contract contracted).E := by
  obtain ⟨contracted, deleted, independent, coindependent, disjoint, rfl⟩ :=
    minor.exists_contract_indep_delete_coindep
  refine ⟨contracted, independent, delete_isRestriction _ _, ?_⟩
  rw [delete_ground]
  exact (coindependent.coindep_contract_of_disjoint disjoint.symm).closure_compl

theorem IsRestriction.isMinor (restriction : smaller.IsRestriction matroid) : smaller ≤m matroid := by
  refine ⟨∅, matroid.E \ smaller.E, ?_⟩
  rw [contract_empty, delete_compl restriction.subset, restriction.eq_restrict]

theorem contract_isMinor (matroid : Matroid Label) (contracted : Set Label) :
    matroid.contract contracted ≤m matroid :=
  ⟨contracted, ∅, by simp⟩

end Matroid
