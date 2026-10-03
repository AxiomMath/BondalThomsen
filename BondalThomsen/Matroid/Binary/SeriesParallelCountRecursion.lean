module

public import BondalThomsen.Matroid.Binary.SeriesPairSimplification
public import BondalThomsen.DeepFan.Classification

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {element : Label}

theorem Simple.countRecursion_delete_simple [source.Simple] (deleted : Set Label) :
    (source.delete deleted).Simple := by
  apply simple_iff_forall_pair_indep.mpr
  intro first second first_member second_member
  rw [delete_indep_iff]
  exact ⟨simple_iff_forall_pair_indep.mp (inferInstance : source.Simple)
      first second first_member.1 second_member.1,
    disjoint_of_subset_left (pair_subset first_member.2 second_member.2)
      disjoint_compl_left⟩

theorem IsColoop.countRecursion_delete_rank_drop [source.Finite]
    (coloop : source.IsColoop element) :
    (source.delete {element}).eRank.toNat + 1 = source.eRank.toNat := by
  rw [← contract_eq_delete_of_subset_coloops
    (singleton_subset_iff.mpr coloop)]
  exact coloop.isNonloop.seriesPairContract_rank_drop

theorem simple_ground_card_bound_of_minor_closed_reducibility
    (family : Matroid Label → Prop)
    (minor_closed : ∀ {candidate smaller}, family candidate → smaller ≤m candidate →
      family smaller)
    (reducible : ∀ candidate, family candidate → candidate.Finite →
      candidate.E.Nonempty → ∃ smaller, ElementarySeriesParallelReduction candidate smaller)
    [source.Finite] [source.Simple] (member : family source) :
    source.E.ncard ≤ 2 * source.eRank.toNat - 1 := by
  suffices result : ∀ size : ℕ, ∀ candidate : Matroid Label,
      candidate.E.ncard = size → candidate.Finite → candidate.Simple → family candidate →
      candidate.E.ncard ≤ 2 * candidate.eRank.toNat - 1 by
    exact result source.E.ncard source rfl inferInstance inferInstance member
  intro size
  induction size using Nat.strong_induction_on with
  | h size induction =>
    intro candidate size_eq finite_candidate simple_candidate family_candidate
    let : candidate.Finite := finite_candidate
    let : candidate.Simple := simple_candidate
    by_cases nonempty : candidate.E.Nonempty
    · obtain ⟨smaller, reduction⟩ := reducible candidate family_candidate finite_candidate nonempty
      have size_step := reduction.ground_ncard
      cases reduction with
      | loop element loop =>
        exact (((Simple.parallel_iff_eq loop.mem_ground).mpr rfl).1.not_isLoop loop).elim
      | coloop element coloop =>
        let : (candidate.delete {element}).Simple := Simple.countRecursion_delete_simple _
        have smaller_bound := induction (candidate.delete {element}).E.ncard
          (by omega) (candidate.delete {element}) rfl inferInstance inferInstance
          (minor_closed family_candidate (delete_isRestriction _ _).isMinor)
        have rank_step := coloop.countRecursion_delete_rank_drop
        omega
      | parallel first second distinct parallel =>
        exact (distinct ((Simple.parallel_iff_eq parallel.1.mem_ground).mp parallel)).elim
      | series first second distinct series =>
        obtain ⟨simplified, simplification, form, simple_simplified, rank_step,
          ground_loss, cardinality⟩ :=
          Simple.seriesPairContract_exists_simplification series distinct
        let : simplified.Finite := simplification.2.1.finite
        let : simplified.Simple := simple_simplified
        have smaller_size : simplified.E.ncard < size := by
          have restriction_size := ncard_le_ncard simplification.2.1.subset
            (candidate.contract {first}).ground_finite
          omega
        have smaller_minor : simplified ≤m candidate :=
          simplification.2.1.isMinor.trans (contract_isMinor _ _)
        have smaller_bound := induction simplified.E.ncard smaller_size simplified rfl
          inferInstance inferInstance (minor_closed family_candidate smaller_minor)
        have retained : second ∈ (candidate.contract {first}).E :=
          ⟨by simpa using series.2.1.mem_ground, by simpa using distinct.symm⟩
        have retained_nonloop := Simple.seriesPairContract_isNonloop
          (show first ∈ candidate.E by simpa using series.1.mem_ground) retained
        obtain ⟨representative, representative_member, _⟩ :=
          simplification.exists_unique retained_nonloop
        have positive : 0 < simplified.E.ncard :=
          (ncard_pos simplified.ground_finite).mpr ⟨representative, representative_member.1⟩
        have rank_nat := IsNonloop.seriesPairContract_rank_drop
          (((Simple.parallel_iff_eq (show first ∈ candidate.E by
            simpa using series.1.mem_ground)).mpr rfl).1)
        rw [← simplification.eRank_eq] at rank_nat
        omega
    · have empty : candidate.E = ∅ := not_nonempty_iff_eq_empty.mp nonempty
      simp only [empty, ncard_empty, Nat.zero_le]

theorem SeriesParallelReductionTrace.exists_first_reduction_of_empty_endpoint
    {target : Matroid Label} {length : ℕ}
    (trace : SeriesParallelReductionTrace source target length)
    (empty : target.E = ∅) (nonempty : source.E.Nonempty) :
    ∃ smaller, ElementarySeriesParallelReduction source smaller := by
  cases trace with
  | nil candidate =>
    exact (nonempty.ne_empty empty).elim
  | cons reduction remaining => exact ⟨_, reduction⟩

theorem minor_closed_family_contains_simplification
    (family : Matroid Label → Prop)
    (minor_closed : ∀ {candidate smaller}, family candidate → smaller ≤m candidate →
      family smaller)
    (member : family source) {simplified : Matroid Label}
    (simplification : simplified.IsSimplification source) : family simplified :=
  minor_closed member simplification.2.1.isMinor

end Matroid

namespace TauCeti.Toric.Fan

open Module Set

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem simplification_ground_card_bound_of_minor_closed_reduction_family
    (fan : TauCeti.Toric.Fan embedding)
    (family : Matroid fan.Ray → Prop)
    (minor_closed : ∀ {candidate smaller}, family candidate → smaller ≤m candidate →
      family smaller)
    (reducible : ∀ candidate, family candidate → candidate.Finite →
      candidate.E.Nonempty → ∃ smaller,
        Matroid.ElementarySeriesParallelReduction candidate smaller)
    (member : family fan.rayMatroid)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin dimension) ℤ Lattice)
    {simplified : Matroid fan.Ray}
    (simplification : simplified.IsSimplification fan.rayMatroid) :
    simplified.E.ncard ≤ 2 * dimension - 1 := by
  let : simplified.Finite := simplification.2.1.finite
  let : simplified.Simple := simplification.simple
  have bound := Matroid.simple_ground_card_bound_of_minor_closed_reducibility
    family minor_closed reducible
    (Matroid.minor_closed_family_contains_simplification family minor_closed member simplification)
  rw [fan.simplification_eRank_of_complete_regular complete regular reference simplification,
    ENat.toNat_natCast] at bound
  exact bound

theorem ray_count_le_four_dimension_sub_two_of_minor_closed_reduction_family
    (fan : TauCeti.Toric.Fan embedding)
    (family : Matroid fan.Ray → Prop)
    (minor_closed : ∀ {candidate smaller}, family candidate → smaller ≤m candidate →
      family smaller)
    (reducible : ∀ candidate, family candidate → candidate.Finite →
      candidate.E.Nonempty → ∃ smaller,
        Matroid.ElementarySeriesParallelReduction candidate smaller)
    (member : family fan.rayMatroid)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin dimension) ℤ Lattice) (positive_dimension : 0 < dimension) :
    Nat.card fan.Ray ≤ 4 * dimension - 2 := by
  obtain ⟨simplified, simplification⟩ := fan.rayRep.exists_isSimplification
  have bound := fan.simplification_ground_card_bound_of_minor_closed_reduction_family
    family minor_closed reducible member complete regular reference simplification
  have antipodal := fan.ray_count_le_twice_simplification simplification
  change Nat.card fan.Ray ≤ 2 * simplified.E.ncard at antipodal
  omega

theorem ray_count_le_four_dimension_sub_two_of_complete_reduction_traces_on_minors
    (fan : TauCeti.Toric.Fan embedding)
    (complete_traces : ∀ candidate : Matroid fan.Ray, candidate ≤m fan.rayMatroid →
      Matroid.SeriesParallelReductionTrace candidate (Matroid.emptyOn fan.Ray) candidate.E.ncard)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin dimension) ℤ Lattice) (positive_dimension : 0 < dimension) :
    Nat.card fan.Ray ≤ 4 * dimension - 2 := by
  apply fan.ray_count_le_four_dimension_sub_two_of_minor_closed_reduction_family
    (fun candidate => candidate ≤m fan.rayMatroid)
    (fun member minor => minor.trans member) _ Matroid.IsMinor.refl
    complete regular reference positive_dimension
  intro candidate minor _ nonempty
  exact (complete_traces candidate minor).exists_first_reduction_of_empty_endpoint
    Matroid.emptyOn_ground nonempty

end TauCeti.Toric.Fan
