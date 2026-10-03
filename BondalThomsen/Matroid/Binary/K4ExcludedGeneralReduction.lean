module

public import BondalThomsen.Matroid.Binary.MarkedRankFour
public import BondalThomsen.Matroid.Binary.SeriesPairSimplification
public import BondalThomsen.Ports.Matroid.Connectedness

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {marked removed first second : Label}

theorem ConnectedTo.delete_or_contract (related : source.ConnectedTo first second)
    (first_avoids : first ≠ removed) (second_avoids : second ≠ removed) :
    (source.delete {removed}).ConnectedTo first second ∨
      (source.contract {removed}).ConnectedTo first second := by
  by_cases same : first = second
  · subst second
    exact Or.inl (connectedTo_self ⟨related.mem_ground_left, by simpa using first_avoids⟩)
  by_cases deleted : (source.delete {removed}).ConnectedTo first second
  · exact Or.inl deleted
  obtain ⟨circuit, property, first_member, second_member⟩ := related.exists_isCircuit_of_ne same
  have removed_member : removed ∈ circuit := by
    by_contra absent
    apply deleted
    exact Or.inr ⟨circuit, (delete_isCircuit_iff.mpr
      ⟨property, by simpa using absent⟩), first_member, second_member⟩
  refine Or.inr (Or.inr ⟨circuit \ {removed}, property.contractElem_isCircuit
    ⟨first, first_member, second, second_member, same⟩ removed_member, ?_, ?_⟩)
  · exact ⟨first_member, by simpa using first_avoids⟩
  · exact ⟨second_member, by simpa using second_avoids⟩

theorem Connected.delete_or_contract (connected : source.Connected)
    (nontrivial : source.E.Nontrivial) (removed : Label) :
    (source.delete {removed}).Connected ∨ (source.contract {removed}).Connected := by
  have ground_nonempty : (source.E \ {removed}).Nonempty := by
    obtain ⟨element, member, distinct⟩ := nontrivial.exists_ne removed
    exact ⟨element, member, by simpa using distinct⟩
  by_cases deleted : (source.delete {removed}).Connected
  · exact Or.inl deleted
  have disconnected : ¬ ∀ first ∈ source.E \ {removed},
      ∀ second ∈ source.E \ {removed}, (source.delete {removed}).ConnectedTo first second := by
    intro all_related
    exact deleted ⟨⟨ground_nonempty⟩, fun {_ _} member other_member =>
      all_related _ member _ other_member⟩
  push Not at disconnected
  obtain ⟨first, first_member, second, second_member, not_related⟩ := disconnected
  have contracted : (source.contract {removed}).ConnectedTo first second :=
    ((connected.forall_connectedTo first_member.1 second_member.1).delete_or_contract
      (by simpa using first_member.2) (by simpa using second_member.2)).resolve_left not_related
  have all_to_first : ∀ element ∈ source.E \ {removed},
      (source.contract {removed}).ConnectedTo element first := by
    intro element member
    by_cases first_related : (source.contract {removed}).ConnectedTo element first
    · exact first_related
    have deleted_first :=
      ((connected.forall_connectedTo member.1 first_member.1).delete_or_contract
        (by simpa using member.2) (by simpa using first_member.2)).resolve_right first_related
    have deleted_second : ¬ (source.delete {removed}).ConnectedTo element second := by
      intro related
      exact not_related (deleted_first.symm.trans related)
    have contracted_second :=
      ((connected.forall_connectedTo member.1 second_member.1).delete_or_contract
        (by simpa using member.2) (by simpa using second_member.2)).resolve_left deleted_second
    exact contracted_second.trans contracted.symm
  refine Or.inr ⟨⟨ground_nonempty⟩, ?_⟩
  intro first second first_member second_member
  exact (all_to_first first first_member).trans (all_to_first second second_member).symm

theorem Simple.contract_parallel_isCircuit_triple [source.Simple]
    (parallel : (source.contract {removed}).Parallel first second) (distinct : first ≠ second) :
    source.IsCircuit (insert removed {first, second}) := by
  obtain ⟨circuit, property, contained, bounded⟩ :=
    (parallel.isCircuit_pair distinct).exists_subset_isCircuit_of_contract
  have removed_member : removed ∈ circuit := by
    by_contra absent
    have pair_eq : circuit = {first, second} := by
      apply Set.Subset.antisymm _ contained
      intro element member
      rcases bounded member with retained | contracted
      · exact retained
      · have same : element = removed := by simpa using contracted
        exact (absent (same ▸ member)).elim
    have original_parallel := (pair_eq ▸ property).parallel_of_pair distinct
    exact distinct ((Simple.parallel_iff_eq original_parallel.1.mem_ground).mp original_parallel)
  have triple_eq : circuit = insert removed {first, second} := by
    apply Set.Subset.antisymm
    · intro element member
      rcases bounded member with retained | contracted
      · exact Set.mem_insert_of_mem _ retained
      · exact Or.inl (by simpa using contracted)
    · exact Set.insert_subset removed_member contained
  exact triple_eq ▸ property

theorem cosimple_delete_series_isCocircuit_triple [source✶.Simple]
    (series : (source.delete {removed})✶.Parallel first second) (distinct : first ≠ second) :
    source.IsCocircuit (insert removed {first, second}) := by
  have parallel : (source✶.contract {removed}).Parallel first second := by
    simpa only [dual_delete] using series
  exact Simple.contract_parallel_isCircuit_triple parallel distinct

def BinaryK4MarkedFailure (source : Matroid Label) (marked : Label) : Prop :=
  source.Finite ∧ source.Connected ∧ source.Representable (ZMod 2) ∧
    (¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate)) ∧
    marked ∈ source.E ∧ 3 ≤ source.E.ncard ∧ ¬MarkedSeriesParallelPair source marked

def ConnectedMarkedMinorMinimal (source : Matroid Label) (marked : Label) : Prop :=
  BinaryK4MarkedFailure source marked ∧
    ∀ candidate : Matroid Label, candidate <m source → candidate.Connected →
      3 ≤ candidate.E.ncard → ∀ basepoint ∈ candidate.E,
        MarkedSeriesParallelPair candidate basepoint

theorem ConnectedMarkedMinorMinimal.rank_corank_size
    (minimal : ConnectedMarkedMinorMinimal source marked) :
    5 ≤ source.eRank ∧ 5 ≤ source✶.eRank ∧ 10 ≤ source.E.ncard := by
  let : source.Finite := minimal.1.1
  exact connected_binary_no_marked_pair_forces_rank_corank_five minimal.1.2.1
    minimal.1.2.2.1 minimal.1.2.2.2.2.2.1 minimal.1.2.2.2.1
    minimal.1.2.2.2.2.1 minimal.1.2.2.2.2.2.2

theorem ConnectedMarkedMinorMinimal.no_parallel
    (minimal : ConnectedMarkedMinorMinimal source marked)
    (parallel : source.Parallel first second) : first = second := by
  classical
  let : source.Finite := minimal.1.1
  obtain ⟨_, _, size⟩ := minimal.rank_corank_size
  have connected := minimal.1.2.1
  have failure := minimal.1.2.2.2.2.2.2
  by_contra distinct
  have lift {partner : Label} (marked_parallel : source.Parallel marked partner)
      (different : marked ≠ partner) : False := by
    have minor : source.delete {marked} ≤m source := (delete_isRestriction _ _).isMinor
    have strict : source.delete {marked} <m source := by
      refine ⟨minor, ?_⟩
      intro reverse
      have retained := reverse.subset marked_parallel.1.mem_ground
      exact retained.2 (by simp)
    have cardinality := marked_parallel.delete_ground_ncard
    have smaller_pair := minimal.2 _ strict
      (connected.delete_parallel marked_parallel different) (by omega) partner
      ⟨marked_parallel.2.1.mem_ground, by simpa using different.symm⟩
    exact failure (smaller_pair.of_parallel_delete marked_parallel different)
  by_cases first_marked : first = marked
  · subst first
    exact lift parallel distinct
  by_cases second_marked : second = marked
  · subst second
    exact lift parallel.symm (Ne.symm distinct)
  exact failure ⟨first, parallel.1.mem_ground, second, parallel.2.1.mem_ground,
    distinct, first_marked, second_marked, Or.inl parallel⟩

theorem ConnectedMarkedMinorMinimal.no_series
    (minimal : ConnectedMarkedMinorMinimal source marked)
    (series : source✶.Parallel first second) : first = second := by
  classical
  let : source.Finite := minimal.1.1
  obtain ⟨_, _, size⟩ := minimal.rank_corank_size
  have connected := minimal.1.2.1
  have failure := minimal.1.2.2.2.2.2.2
  by_contra distinct
  have lift {partner : Label} (marked_series : source✶.Parallel marked partner)
      (different : marked ≠ partner) : False := by
    have minor : source.contract {marked} ≤m source := contract_isMinor _ _
    have strict : source.contract {marked} <m source := by
      refine ⟨minor, ?_⟩
      intro reverse
      have retained := reverse.subset marked_series.1.mem_ground
      exact retained.2 (by simp)
    have cardinality := series_contract_ground_ncard marked_series
    have smaller_pair := minimal.2 _ strict
      (connected.contract_series marked_series different) (by omega) partner
      ⟨marked_series.2.1.mem_ground, by simpa using different.symm⟩
    exact failure (smaller_pair.of_series_contract marked_series different)
  by_cases first_marked : first = marked
  · subst first
    exact lift series distinct
  by_cases second_marked : second = marked
  · subst second
    exact lift series.symm (Ne.symm distinct)
  exact failure ⟨first, series.1.mem_ground, second, series.2.1.mem_ground,
    distinct, first_marked, second_marked, Or.inr series⟩

theorem ConnectedMarkedMinorMinimal.simple_cosimple
    (minimal : ConnectedMarkedMinorMinimal source marked) : source.Simple ∧ source✶.Simple := by
  let : source.Finite := minimal.1.1
  let : Finite source.E := source.ground_finite.to_subtype
  have nontrivial : source.E.Nontrivial := Set.one_lt_ncard_iff_nontrivial.mp
    (by have size := minimal.rank_corank_size.2.2; omega)
  have connected := minimal.1.2.1
  constructor
  · refine ⟨fun {first second} member => ?_⟩
    constructor
    · exact fun parallel => minimal.no_parallel parallel
    · intro same
      subst second
      exact (connected.isNonloop nontrivial member).parallel_self
  · refine ⟨fun {first second} member => ?_⟩
    constructor
    · exact fun series => minimal.no_series series
    · intro same
      subst second
      exact (connected.to_dual.isNonloop nontrivial member).parallel_self

theorem exists_connectedMarkedMinorMinimal (failure : BinaryK4MarkedFailure source marked) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      ∃ basepoint, ConnectedMarkedMinorMinimal candidate basepoint := by
  classical
  let : source.Finite := failure.1
  let possible : ℕ → Prop := fun size => ∃ candidate : Matroid Label,
    candidate ≤m source ∧ ∃ basepoint,
      BinaryK4MarkedFailure candidate basepoint ∧ candidate.E.ncard = size
  have exists_size : ∃ size, possible size :=
    ⟨source.E.ncard, source, .refl, marked, failure, rfl⟩
  obtain ⟨candidate, minor, basepoint, candidate_failure, cardinality⟩ := Nat.find_spec exists_size
  let : candidate.Finite := candidate_failure.1
  refine ⟨candidate, minor, basepoint, candidate_failure, ?_⟩
  intro smaller strict connected lower smaller_marked member
  let : smaller.Finite := ⟨candidate.ground_finite.subset strict.isMinor.subset⟩
  by_contra no_pair
  have smaller_failure : BinaryK4MarkedFailure smaller smaller_marked := by
    refine ⟨inferInstance, connected,
      candidate_failure.2.2.1.of_isMinor strict.isMinor, ?_, member, lower, no_pair⟩
    rintro ⟨k4, k4_minor, isomorphism⟩
    exact candidate_failure.2.2.2.1 ⟨k4, k4_minor.trans strict.isMinor, isomorphism⟩
  have minimum : Nat.find exists_size ≤ smaller.E.ncard := Nat.find_min' exists_size
    ⟨smaller, strict.isMinor.trans minor, smaller_marked, smaller_failure, rfl⟩
  have smaller_card : smaller.E.ncard < candidate.E.ncard :=
    Set.ncard_lt_ncard strict.ssubset candidate.ground_finite
  omega

theorem ConnectedMarkedMinorMinimal.contract_triangle_avoiding
    (minimal : ConnectedMarkedMinorMinimal source marked) (removed_member : removed ∈ source.E)
    (connected : (source.contract {removed}).Connected)
    (basepoint : Label) (basepoint_member : basepoint ∈ (source.contract {removed}).E) :
    ∃ first ∈ (source.contract {removed}).E, ∃ second ∈ (source.contract {removed}).E,
      first ≠ second ∧ first ≠ basepoint ∧ second ≠ basepoint ∧
        source.IsCircuit (insert removed {first, second}) := by
  let : source.Finite := minimal.1.1
  let : source.Simple := minimal.simple_cosimple.1
  let : source✶.Simple := minimal.simple_cosimple.2
  have strict : source.contract {removed} <m source := by
    refine ⟨contract_isMinor _ _, ?_⟩
    intro reverse
    exact (reverse.subset removed_member).2 (by simp)
  have cardinality : (source.contract {removed}).E.ncard + 1 = source.E.ncard :=
    Set.ncard_sdiff_singleton_add_one removed_member source.ground_finite
  have lower : 3 ≤ (source.contract {removed}).E.ncard := by
    have size := minimal.rank_corank_size.2.2
    omega
  obtain ⟨first, first_member, second, second_member, distinct,
    first_avoids, second_avoids, property⟩ := minimal.2 _ strict connected lower basepoint basepoint_member
  refine ⟨first, first_member, second, second_member, distinct, first_avoids, second_avoids, ?_⟩
  rcases property with parallel | series
  · exact Simple.contract_parallel_isCircuit_triple parallel distinct
  · have deleted_parallel : (source✶.delete {removed}).Parallel first second := by
      simpa only [dual_contract] using series
    have original_series := deleted_parallel.of_isRestriction (delete_isRestriction _ _)
    exact (distinct (minimal.no_series original_series)).elim

theorem ConnectedMarkedMinorMinimal.delete_triad_avoiding
    (minimal : ConnectedMarkedMinorMinimal source marked) (removed_member : removed ∈ source.E)
    (connected : (source.delete {removed}).Connected)
    (basepoint : Label) (basepoint_member : basepoint ∈ (source.delete {removed}).E) :
    ∃ first ∈ (source.delete {removed}).E, ∃ second ∈ (source.delete {removed}).E,
      first ≠ second ∧ first ≠ basepoint ∧ second ≠ basepoint ∧
        source.IsCocircuit (insert removed {first, second}) := by
  let : source.Finite := minimal.1.1
  let : source.Simple := minimal.simple_cosimple.1
  let : source✶.Simple := minimal.simple_cosimple.2
  have strict : source.delete {removed} <m source := by
    refine ⟨(delete_isRestriction _ _).isMinor, ?_⟩
    intro reverse
    exact (reverse.subset removed_member).2 (by simp)
  have cardinality : (source.delete {removed}).E.ncard + 1 = source.E.ncard :=
    Set.ncard_sdiff_singleton_add_one removed_member source.ground_finite
  have lower : 3 ≤ (source.delete {removed}).E.ncard := by
    have size := minimal.rank_corank_size.2.2
    omega
  obtain ⟨first, first_member, second, second_member, distinct,
    first_avoids, second_avoids, property⟩ := minimal.2 _ strict connected lower basepoint basepoint_member
  refine ⟨first, first_member, second, second_member, distinct, first_avoids, second_avoids, ?_⟩
  rcases property with parallel | series
  · exact (distinct (minimal.no_parallel
      (parallel.of_isRestriction (delete_isRestriction _ _)))).elim
  · exact cosimple_delete_series_isCocircuit_triple series distinct

def ConnectedTriangleTriadProfile (source : Matroid Label) : Prop :=
  ∀ removed ∈ source.E,
    ((source.contract {removed}).Connected →
      ∀ basepoint ∈ source.E \ {removed},
        ∃ first ∈ source.E \ {removed}, ∃ second ∈ source.E \ {removed},
          first ≠ second ∧ first ≠ basepoint ∧ second ≠ basepoint ∧
            source.IsCircuit (insert removed {first, second})) ∧
    ((source.delete {removed}).Connected →
      ∀ basepoint ∈ source.E \ {removed},
        ∃ first ∈ source.E \ {removed}, ∃ second ∈ source.E \ {removed},
          first ≠ second ∧ first ≠ basepoint ∧ second ≠ basepoint ∧
            source.IsCocircuit (insert removed {first, second}))

theorem ConnectedMarkedMinorMinimal.triangle_triad_profile
    (minimal : ConnectedMarkedMinorMinimal source marked) : ConnectedTriangleTriadProfile source := by
  intro removed member
  exact ⟨fun connected basepoint basepoint_member =>
    minimal.contract_triangle_avoiding member connected basepoint basepoint_member,
    fun connected basepoint basepoint_member =>
      minimal.delete_triad_avoiding member connected basepoint basepoint_member⟩

theorem binary_marked_failure_has_simple_cosimple_profile_minor
    (failure : BinaryK4MarkedFailure source marked) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      candidate.Finite ∧ candidate.Connected ∧ candidate.Representable (ZMod 2) ∧
      candidate.Simple ∧ candidate✶.Simple ∧
      5 ≤ candidate.eRank ∧ 5 ≤ candidate✶.eRank ∧ 10 ≤ candidate.E.ncard ∧
      ConnectedTriangleTriadProfile candidate ∧
      ¬ ∃ k4 : Matroid Label, k4 ≤m candidate ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid k4) := by
  obtain ⟨candidate, minor, basepoint, minimal⟩ := exists_connectedMarkedMinorMinimal failure
  exact ⟨candidate, minor, minimal.1.1, minimal.1.2.1, minimal.1.2.2.1,
    minimal.simple_cosimple.1, minimal.simple_cosimple.2,
    minimal.rank_corank_size.1, minimal.rank_corank_size.2.1, minimal.rank_corank_size.2.2,
    minimal.triangle_triad_profile, minimal.1.2.2.2.1⟩

def BinaryConnectedTriangleTriadK4MinorLemma (Label : Type*) : Prop :=
  ∀ candidate : Matroid Label, candidate.Finite → candidate.Connected →
    candidate.Representable (ZMod 2) → candidate.Simple → candidate✶.Simple →
    5 ≤ candidate.eRank → 5 ≤ candidate✶.eRank → 10 ≤ candidate.E.ncard →
    ConnectedTriangleTriadProfile candidate →
      ∃ k4 : Matroid Label, k4 ≤m candidate ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid k4)

theorem connected_binary_pair_avoiding_of_triangle_triad_minor_lemma
    (minor_lemma : BinaryConnectedTriangleTriadK4MinorLemma Label) [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (lower : 3 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) : MarkedSeriesParallelPair source marked := by
  by_contra failure
  obtain ⟨candidate, _, finite_candidate, candidate_connected, candidate_binary,
    simple, cosimple, rank, corank, size, profile, candidate_excluded⟩ :=
    binary_marked_failure_has_simple_cosimple_profile_minor
      ⟨inferInstance, connected, binary, excluded, marked_member, lower, failure⟩
  exact candidate_excluded (minor_lemma candidate finite_candidate candidate_connected
    candidate_binary simple cosimple rank corank size profile)

theorem connected_binary_marked_leaf_reduction_of_triangle_triad_minor_lemma
    (minor_lemma : BinaryConnectedTriangleTriadK4MinorLemma Label) [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (lower : 3 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced ∧ reduced.Connected ∧
      marked ∈ reduced.E ∧ reduced.IsNonloop marked ∧ ¬reduced.IsColoop marked ∧
      reduced.E.ncard + 1 = source.E.ncard ∧ reduced.Representable (ZMod 2) ∧
      ¬ ∃ candidate : Matroid Label, candidate ≤m reduced ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) :=
  (connected_binary_pair_avoiding_of_triangle_triad_minor_lemma minor_lemma
    connected binary lower excluded marked_member).exists_connected_marked_leaf_reduction
      connected binary excluded marked_member

theorem connected_binary_marked_trace_of_triangle_triad_minor_lemma
    (minor_lemma : BinaryConnectedTriangleTriadK4MinorLemma Label) [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (lower : 2 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) :
    ∃ target, target.E.ncard = 2 ∧ target.Connected ∧ marked ∈ target.E ∧
      target.IsNonloop marked ∧ ¬target.IsColoop marked ∧ target.Representable (ZMod 2) ∧
      (¬ ∃ candidate : Matroid Label, candidate ≤m target ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate)) ∧
      MarkedConnectedReductionTrace marked source target (source.E.ncard - 2) := by
  classical
  suffices result : ∀ cardinality : ℕ, ∀ candidate : Matroid Label, candidate.Finite →
      candidate.E.ncard = cardinality → candidate.Connected → candidate.Representable (ZMod 2) →
      2 ≤ cardinality →
      (¬ ∃ smaller : Matroid Label, smaller ≤m candidate ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller)) →
      marked ∈ candidate.E →
      ∃ target, target.E.ncard = 2 ∧ target.Connected ∧ marked ∈ target.E ∧
        target.IsNonloop marked ∧ ¬target.IsColoop marked ∧ target.Representable (ZMod 2) ∧
        (¬ ∃ smaller : Matroid Label, smaller ≤m target ∧
          Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller)) ∧
        MarkedConnectedReductionTrace marked candidate target (cardinality - 2) by
    exact result source.E.ncard source inferInstance rfl connected binary lower excluded marked_member
  intro cardinality
  induction cardinality using Nat.strong_induction_on with
  | h cardinality induction =>
    intro candidate finite_candidate cardinality_eq connected binary lower excluded marked_member
    let : candidate.Finite := finite_candidate
    let : Finite candidate.E := candidate.ground_finite.to_subtype
    have nontrivial : candidate.E.Nontrivial := Set.one_lt_ncard_iff_nontrivial.mp (by omega)
    have nonloop := connected.isNonloop nontrivial marked_member
    have not_coloop := connected.not_isColoop nontrivial marked_member
    by_cases terminal : cardinality = 2
    · refine ⟨candidate, by omega, connected, marked_member, nonloop, not_coloop,
        binary, excluded, ?_⟩
      simpa only [terminal, Nat.sub_self] using
        MarkedConnectedReductionTrace.nil candidate connected nonloop not_coloop
    obtain ⟨reduced, reduction, reduced_connected, marked_retained, _, _,
      smaller_size, reduced_binary, reduced_excluded⟩ :=
      connected_binary_marked_leaf_reduction_of_triangle_triad_minor_lemma minor_lemma
        connected binary (by omega) excluded marked_member
    let : reduced.Finite := ⟨candidate.ground_finite.subset reduction.isMinor.subset⟩
    obtain ⟨target, target_size, target_connected, target_marked, target_nonloop,
      target_not_coloop, target_binary, target_excluded, remaining⟩ :=
      induction reduced.E.ncard (by omega) reduced inferInstance rfl reduced_connected
        reduced_binary (by omega) reduced_excluded marked_retained
    refine ⟨target, target_size, target_connected, target_marked, target_nonloop,
      target_not_coloop, target_binary, target_excluded, ?_⟩
    have trace := MarkedConnectedReductionTrace.cons connected nonloop not_coloop reduction remaining
    convert trace using 1; omega

end Matroid
