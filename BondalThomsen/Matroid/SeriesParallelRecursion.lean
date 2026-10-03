module

public import BondalThomsen.Matroid.SeriesParallelReductions
public import BondalThomsen.Ports.Matroid.ProjectiveBound
public import BondalThomsen.Ports.Matroid.IsomorphismRank
public import Mathlib.Tactic

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {matroid : Matroid Label}

theorem binary_simple_rank_two_ground_card_le_three [matroid.Simple] [matroid.Finite]
    (binary : matroid.Representable (ZMod 2)) (rank : matroid.eRank ≤ 2) :
    matroid.E.ncard ≤ 3 := by
  have projective := binary.encard_le_of_simple
  have rank_nat : matroid.eRank.toNat ≤ 2 := ENat.toNat_le_toNat rank (by simp)
  have sum_bound :
      (∑ index ∈ Finset.range matroid.eRank.toNat, (ENat.card (ZMod 2)) ^ index) ≤ 3 := by
    interval_cases rank_value : matroid.eRank.toNat <;>
      norm_num [rank_value, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card,
        ZMod.card, Finset.sum_range_succ]
  have bound := projective.trans sum_bound
  rw [← matroid.ground_finite.cast_ncard_eq] at bound
  exact_mod_cast bound

inductive ElementarySeriesParallelReduction (source : Matroid Label) : Matroid Label → Prop
  | loop (element : Label) (loop : source.IsLoop element) :
      ElementarySeriesParallelReduction source (source.delete {element})
  | coloop (element : Label) (coloop : source.IsColoop element) :
      ElementarySeriesParallelReduction source (source.delete {element})
  | parallel (first second : Label) (distinct : first ≠ second)
      (parallel : source.Parallel first second) :
      ElementarySeriesParallelReduction source (source.delete {first})
  | series (first second : Label) (distinct : first ≠ second)
      (series : source✶.Parallel first second) :
      ElementarySeriesParallelReduction source (source.contract {first})

variable {reduced : Matroid Label}

theorem ElementarySeriesParallelReduction.isMinor
    (reduction : ElementarySeriesParallelReduction matroid reduced) : reduced ≤m matroid := by
  cases reduction with
  | loop element loop => exact ⟨∅, {element}, by simp⟩
  | coloop element coloop => exact ⟨∅, {element}, by simp⟩
  | parallel first second distinct parallel => exact ⟨∅, {first}, by simp⟩
  | series first second distinct series => exact contract_isMinor _ _

theorem ElementarySeriesParallelReduction.ground_ncard [matroid.Finite]
    (reduction : ElementarySeriesParallelReduction matroid reduced) :
    reduced.E.ncard + 1 = matroid.E.ncard := by
  have deletion_size (element : Label) (member : element ∈ matroid.E) :
      (matroid.E \ {element}).ncard + 1 = matroid.E.ncard := by
    have positive : 0 < matroid.E.ncard :=
      (Set.ncard_pos matroid.ground_finite).mpr ⟨element, member⟩
    rw [Set.ncard_sdiff_singleton_of_mem member]
    omega
  cases reduction with
  | loop element loop => simpa only [delete_ground] using deletion_size element loop.mem_ground
  | coloop element coloop =>
      simpa only [delete_ground] using deletion_size element coloop.mem_ground
  | parallel first second distinct parallel =>
      simpa only [delete_ground] using deletion_size first parallel.1.mem_ground
  | series first second distinct series =>
      have member : first ∈ matroid.E := by simpa using series.1.mem_ground
      simpa only [contract_ground] using deletion_size first member

inductive SeriesParallelReductionTrace : Matroid Label → Matroid Label → ℕ → Prop
  | nil (source : Matroid Label) : SeriesParallelReductionTrace source source 0
  | cons {source intermediate target : Matroid Label} {length : ℕ}
      (reduction : ElementarySeriesParallelReduction source intermediate)
      (remaining : SeriesParallelReductionTrace intermediate target length) :
      SeriesParallelReductionTrace source target (length + 1)

theorem SeriesParallelReductionTrace.isMinor {target : Matroid Label} {length : ℕ}
    (trace : SeriesParallelReductionTrace matroid target length) : target ≤m matroid := by
  induction trace with
  | nil source => exact IsMinor.refl
  | cons reduction remaining induction => exact induction.trans reduction.isMinor

theorem SeriesParallelReductionTrace.ground_ncard {target : Matroid Label} {length : ℕ}
    (trace : SeriesParallelReductionTrace matroid target length) [matroid.Finite] :
    length + target.E.ncard = matroid.E.ncard := by
  have finite_source : matroid.Finite := inferInstance
  revert finite_source
  induction trace with
  | nil source => intro _; simp
  | @cons source intermediate target length reduction remaining induction =>
      intro finite_source
      let : source.Finite := finite_source
      let : intermediate.Finite :=
        ⟨source.ground_finite.subset reduction.isMinor.subset⟩
      have step := reduction.ground_ncard
      have tail := induction inferInstance
      omega

theorem reduction_trace_of_minor_closed_reducibility
    (family : Matroid Label → Prop)
    (minor_closed : ∀ {source target}, family source → target ≤m source → family target)
    (reducible : ∀ source, family source → source.Finite → source.E.Nonempty →
      ∃ target, ElementarySeriesParallelReduction source target)
    [matroid.Finite] (member : family matroid) :
    ∃ target, target.E = ∅ ∧ SeriesParallelReductionTrace matroid target matroid.E.ncard := by
  suffices result : ∀ size : ℕ, ∀ source : Matroid Label, source.E.ncard = size →
      source.Finite → family source →
        ∃ target, target.E = ∅ ∧ SeriesParallelReductionTrace source target size by
    exact result matroid.E.ncard matroid rfl inferInstance member
  intro size
  induction size using Nat.strong_induction_on with
  | h size induction =>
      intro source size_eq finite_source family_source
      let : source.Finite := finite_source
      by_cases nonempty : source.E.Nonempty
      · obtain ⟨intermediate, reduction⟩ := reducible source family_source finite_source nonempty
        let : intermediate.Finite :=
          ⟨source.ground_finite.subset reduction.isMinor.subset⟩
        have size_step := reduction.ground_ncard
        have smaller : intermediate.E.ncard < size := by omega
        obtain ⟨target, empty, trace⟩ := induction intermediate.E.ncard smaller intermediate rfl
          inferInstance (minor_closed family_source reduction.isMinor)
        refine ⟨target, empty, ?_⟩
        have reconstructed := SeriesParallelReductionTrace.cons reduction trace
        have length_eq : intermediate.E.ncard + 1 = size := by omega
        exact length_eq ▸ reconstructed
      · have empty : source.E = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
        have zero : size = 0 := by simpa [empty] using size_eq.symm
        subst size
        refine ⟨source, empty, ?_⟩
        simpa only [empty, Set.ncard_empty] using SeriesParallelReductionTrace.nil source

end Matroid
