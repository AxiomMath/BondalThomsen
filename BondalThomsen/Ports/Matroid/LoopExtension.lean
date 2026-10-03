module

public import BondalThomsen.Ports.Matroid.ParallelExtension
public import BondalThomsen.Matroid.Binary.MarkedRankFour

@[expose] public section

namespace Matroid

open Set

variable {Ground : Type*} {source : Matroid Ground} {added : Ground} {selected : Set Ground}

def addLoop (source : Matroid Ground) (added : Ground) : Matroid Ground :=
  source.restrict (insert added source.E)

@[simp] theorem addLoop_ground (source : Matroid Ground) (added : Ground) :
    (source.addLoop added).E = insert added source.E := rfl

@[simp] theorem addLoop_indep_iff : (source.addLoop added).Indep selected ↔ source.Indep selected := by
  rw [addLoop, restrict_indep_iff]
  constructor
  · exact fun independent => independent.1
  · exact fun independent => ⟨independent,
      independent.subset_ground.trans (subset_insert _ _)⟩

instance addLoop_finite (source : Matroid Ground) [source.Finite]
    (added : Ground) : (source.addLoop added).Finite :=
  ⟨source.ground_finite.insert added⟩

theorem addLoop_isLoop (new_label : added ∉ source.E) :
    (source.addLoop added).IsLoop added := by
  rw [← singleton_dep]
  refine ⟨?_, by simp⟩
  intro independent
  exact new_label ((addLoop_indep_iff.mp independent).subset_ground (by simp))

theorem addLoop_delete_eq (source : Matroid Ground) (new_label : added ∉ source.E) :
    (source.addLoop added).delete {added} = source := by
  apply ext_indep (by
    rw [delete_ground, addLoop_ground, insert_sdiff_self_of_notMem new_label])
  intro selected _
  rw [delete_indep_iff, addLoop_indep_iff, Set.disjoint_singleton_right]
  constructor
  · exact fun independent => independent.1
  · exact fun independent => ⟨independent,
      fun member => new_label (independent.subset_ground member)⟩

def addColoop (source : Matroid Ground) (added : Ground) : Matroid Ground :=
  (source✶.addLoop added)✶

@[simp] theorem addColoop_ground (source : Matroid Ground) (added : Ground) :
    (source.addColoop added).E = insert added source.E := by
  rw [addColoop, dual_ground, addLoop_ground, dual_ground]

instance addColoop_finite (source : Matroid Ground) [source.Finite]
    (added : Ground) : (source.addColoop added).Finite := by
  rw [addColoop]
  infer_instance

theorem addColoop_isColoop (new_label : added ∉ source.E) :
    (source.addColoop added).IsColoop added := by
  exact (source✶.addLoop_isLoop new_label).dual_isColoop

theorem addColoop_contract_eq (source : Matroid Ground) (new_label : added ∉ source.E) :
    (source.addColoop added).contract {added} = source := by
  rw [addColoop, ← dual_delete_dual, dual_dual,
    addLoop_delete_eq source✶ new_label, dual_dual]

theorem addColoop_delete_eq (source : Matroid Ground) (new_label : added ∉ source.E) :
    (source.addColoop added).delete {added} = source := by
  rw [← contract_eq_delete_of_subset_coloops
    (singleton_subset_iff.mpr (addColoop_isColoop new_label))]
  exact addColoop_contract_eq source new_label

end Matroid
