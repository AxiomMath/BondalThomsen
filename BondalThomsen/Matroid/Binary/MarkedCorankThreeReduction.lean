module

public import BondalThomsen.Matroid.Binary.MarkedCorankThree
public import BondalThomsen.Matroid.DualRepresentation

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source target : Matroid Label} {marked : Label} {length : ℕ}

theorem isNonloop_not_isColoop_dual_iff :
    source✶.IsNonloop marked ∧ ¬source✶.IsColoop marked ↔
      source.IsNonloop marked ∧ ¬source.IsColoop marked := by
  simp only [isNonloop_iff, dual_isLoop_iff_isColoop, dual_ground,
    dual_isColoop_iff_isLoop]
  tauto

theorem ElementarySeriesParallelReduction.dual
    (reduction : ElementarySeriesParallelReduction source target) :
    ElementarySeriesParallelReduction source✶ target✶ := by
  cases reduction with
  | loop element loop =>
    rw [dual_delete, contract_eq_delete_of_subset_coloops
      (singleton_subset_iff.mpr loop.dual_isColoop)]
    exact .coloop element loop.dual_isColoop
  | coloop element coloop =>
    rw [dual_delete, contract_eq_delete_of_subset_loops
      (singleton_subset_iff.mpr coloop.dual_isLoop)]
    exact .loop element coloop.dual_isLoop
  | parallel first second distinct parallel =>
    rw [dual_delete]
    exact .series first second distinct (by simpa only [dual_dual] using parallel)
  | series first second distinct series =>
    rw [dual_contract]
    exact .parallel first second distinct series

theorem SeriesParallelReductionTrace.dual
    (trace : SeriesParallelReductionTrace source target length) :
    SeriesParallelReductionTrace source✶ target✶ length := by
  induction trace with
  | nil candidate => exact .nil candidate✶
  | cons reduction remaining induction => exact .cons reduction.dual induction

theorem MarkedConnectedReductionTrace.dual
    (trace : MarkedConnectedReductionTrace marked source target length) :
    MarkedConnectedReductionTrace marked source✶ target✶ length := by
  induction trace with
  | nil candidate connected nonloop not_coloop =>
    obtain ⟨dual_nonloop, dual_not_coloop⟩ :=
      isNonloop_not_isColoop_dual_iff.mpr ⟨nonloop, not_coloop⟩
    exact .nil candidate✶ connected.to_dual dual_nonloop dual_not_coloop
  | cons connected nonloop not_coloop reduction remaining induction =>
    obtain ⟨dual_nonloop, dual_not_coloop⟩ :=
      isNonloop_not_isColoop_dual_iff.mpr ⟨nonloop, not_coloop⟩
    exact .cons connected.to_dual dual_nonloop dual_not_coloop reduction.dual induction

end Matroid
