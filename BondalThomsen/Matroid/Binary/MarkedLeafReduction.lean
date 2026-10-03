module

public import BondalThomsen.Matroid.Binary.SixElementCoverage

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {first second marked : Label}

def ConnectedTo (source : Matroid Label) (first second : Label) : Prop :=
  (first = second ∧ first ∈ source.E) ∨
    ∃ circuit, source.IsCircuit circuit ∧ first ∈ circuit ∧ second ∈ circuit

structure Connected (source : Matroid Label) : Prop where
  nonempty : source.Nonempty
  forall_connectedTo : ∀ ⦃first second⦄,
    first ∈ source.E → second ∈ source.E → source.ConnectedTo first second

theorem ConnectedTo.exists_isCircuit_of_ne (connected : source.ConnectedTo first second)
    (distinct : first ≠ second) :
    ∃ circuit, source.IsCircuit circuit ∧ first ∈ circuit ∧ second ∈ circuit := by
  simpa only [ConnectedTo, distinct, false_and, false_or] using connected

theorem IsCircuit.parallel_of_pair (circuit : source.IsCircuit {first, second})
    (distinct : first ≠ second) : source.Parallel first second := by
  have nontrivial : ({first, second} : Set Label).Nontrivial :=
    ⟨first, by simp, second, by simp, distinct⟩
  apply parallel_iff_isNonloop_isNonloop_indep_imp_eq.mpr
  exact ⟨circuit.isNonloop_of_mem nontrivial (by simp),
    circuit.isNonloop_of_mem nontrivial (by simp),
    fun independent => (circuit.not_indep independent).elim⟩

theorem Parallel.mem_isCocircuit_of_mem (parallel : source.Parallel first second)
    {cocircuit : Set Label} (cocircuit_property : source.IsCocircuit cocircuit)
    (member : first ∈ cocircuit) : second ∈ cocircuit := by
  by_cases same : first = second
  · exact same ▸ member
  by_contra absent
  apply (parallel.isCircuit_pair same).inter_isCocircuit_ne_singleton cocircuit_property
    (e := first)
  ext element
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, chosen⟩
    · rfl
    · exact (absent chosen).elim
  · rintro rfl
    exact ⟨Or.inl rfl, member⟩

theorem ConnectedTo.to_dual (connected : source.ConnectedTo first second) :
    source✶.ConnectedTo first second := by
  by_cases same : first = second
  · subst second
    rcases connected with ⟨_, member⟩ | ⟨circuit, property, member, _⟩
    · exact Or.inl ⟨rfl, member⟩
    · exact Or.inl ⟨rfl, property.subset_ground member⟩
  obtain ⟨circuit, property, first_member, second_member⟩ :=
    connected.exists_isCircuit_of_ne same
  have contracted_circuit : (source.contract (circuit \ {first, second})).IsCircuit
      {first, second} := property.contract_sdiff_isCircuit (by simp)
        (Set.pair_subset first_member second_member)
  have parallel := contracted_circuit.parallel_of_pair same
  obtain ⟨basisSet, base, first_basis⟩ := parallel.1.exists_mem_isBase
  have cocircuit := fundCocircuit_isCocircuit first_basis base
  exact Or.inr ⟨_, cocircuit.of_contract.isCircuit, mem_fundCocircuit _ _ _,
    parallel.mem_isCocircuit_of_mem cocircuit (mem_fundCocircuit _ _ _)⟩

theorem Connected.to_dual (connected : source.Connected) : source✶.Connected := by
  refine ⟨?_, fun _ _ first_member second_member =>
    (connected.forall_connectedTo first_member second_member).to_dual⟩
  let : source.Nonempty := connected.nonempty
  infer_instance

theorem connected_dual_iff : source✶.Connected ↔ source.Connected := by
  constructor
  · intro connected
    simpa only [dual_dual] using connected.to_dual
  · exact Connected.to_dual

theorem Connected.exists_isCircuit_of_ne (connected : source.Connected)
    (first_member : first ∈ source.E) (second_member : second ∈ source.E)
    (distinct : first ≠ second) :
    ∃ circuit, source.IsCircuit circuit ∧ first ∈ circuit ∧ second ∈ circuit :=
  (connected.forall_connectedTo first_member second_member).exists_isCircuit_of_ne distinct

theorem Connected.isNonloop (connected : source.Connected) (nontrivial : source.E.Nontrivial)
    (member : first ∈ source.E) : source.IsNonloop first := by
  obtain ⟨second, second_member, distinct⟩ := nontrivial.exists_ne first
  obtain ⟨circuit, property, first_circuit, second_circuit⟩ :=
    connected.exists_isCircuit_of_ne member second_member distinct.symm
  exact property.isNonloop_of_mem
    ⟨first, first_circuit, second, second_circuit, distinct.symm⟩ first_circuit

theorem Connected.not_isColoop (connected : source.Connected)
    (nontrivial : source.E.Nontrivial) (member : first ∈ source.E) :
    ¬ source.IsColoop first := by
  obtain ⟨second, second_member, distinct⟩ := nontrivial.exists_ne first
  obtain ⟨circuit, property, first_circuit, _⟩ :=
    connected.exists_isCircuit_of_ne member second_member distinct.symm
  exact property.not_isColoop_of_mem first_circuit

theorem Connected.loopless (connected : source.Connected) (nontrivial : source.E.Nontrivial) :
    source.Loopless := by
  apply loopless_iff_forall_isNonloop.mpr
  intro element member
  exact connected.isNonloop nontrivial member

theorem IsCircuit.mapEquiv_image {OtherLabel : Type*} {selected : Set Label}
    (circuit : source.IsCircuit selected) (equivalence : Label ≃ OtherLabel) :
    (source.mapEquiv equivalence).IsCircuit (equivalence '' selected) := by
  apply isCircuit_iff_dep_forall_sdiff_singleton_indep.mpr
  refine ⟨?_, ?_⟩
  · rw [mapEquiv_dep_iff]
    simpa using circuit.dep
  · rintro element ⟨original, member, rfl⟩
    rw [mapEquiv_indep_iff, ← Set.image_singleton,
      ← Set.image_sdiff equivalence.injective]
    simpa using circuit.sdiff_singleton_indep member

theorem Connected.delete_parallel (connected : source.Connected)
    (parallel : source.Parallel first second) (distinct : first ≠ second) :
    (source.delete {first}).Connected := by
  classical
  refine ⟨⟨⟨second, parallel.2.1.mem_ground, by simpa using distinct.symm⟩⟩, ?_⟩
  intro left right left_member right_member
  by_cases equal : left = right
  · exact Or.inl ⟨equal, left_member⟩
  obtain ⟨circuit, property, left_circuit, right_circuit⟩ :=
    connected.exists_isCircuit_of_ne left_member.1 right_member.1 equal
  by_cases deleted_absent : first ∉ circuit
  · exact Or.inr ⟨circuit, delete_isCircuit_iff.mpr
      ⟨property, by simpa only [Set.disjoint_singleton_right] using deleted_absent⟩,
      left_circuit, right_circuit⟩
  have deleted_member : first ∈ circuit := Classical.not_not.mp deleted_absent
  have retained_absent : second ∉ circuit := by
    intro retained_member
    have pair_eq := property.eq_of_not_indep_subset
      (parallel.isCircuit_pair distinct).not_indep (Set.pair_subset deleted_member retained_member)
    have left_second : left = second := by
      rw [← pair_eq] at left_circuit
      rcases left_circuit with same | same
      · exact (left_member.2 same).elim
      · exact same
    have right_second : right = second := by
      rw [← pair_eq] at right_circuit
      rcases right_circuit with same | same
      · exact (right_member.2 same).elim
      · exact same
    exact equal (left_second.trans right_second.symm)
  let swapped := Equiv.swap first second
  have swapped_circuit : source.IsCircuit (swapped '' circuit) := by
    have transported := property.mapEquiv_image swapped
    rw [parallel.eq_mapEquiv_swap] at transported
    exact transported
  refine Or.inr ⟨swapped '' circuit, delete_isCircuit_iff.mpr ⟨swapped_circuit, ?_⟩, ?_, ?_⟩
  · apply Set.disjoint_singleton_right.mpr
    rintro ⟨original, member, equality⟩
    have original_eq : original = second := swapped.injective
      (equality.trans (Equiv.swap_apply_right first second).symm)
    exact retained_absent (original_eq ▸ member)
  · refine ⟨left, left_circuit, ?_⟩
    exact Equiv.swap_apply_of_ne_of_ne (by simpa using left_member.2)
      (fun equality => retained_absent (equality ▸ left_circuit))
  · refine ⟨right, right_circuit, ?_⟩
    exact Equiv.swap_apply_of_ne_of_ne (by simpa using right_member.2)
      (fun equality => retained_absent (equality ▸ right_circuit))

theorem Connected.contract_series (connected : source.Connected)
    (series : source✶.Parallel first second) (distinct : first ≠ second) :
    (source.contract {first}).Connected := by
  have dual_connected := connected.to_dual.delete_parallel series distinct
  have original_connected := dual_connected.to_dual
  simpa only [dual_delete, dual_dual] using original_connected

theorem Parallel.series_of_delete_avoiding (parallel : source.Parallel first second)
    (parallel_distinct : first ≠ second) {left right : Label} (distinct : left ≠ right)
    (left_avoids : left ≠ second) (right_avoids : right ≠ second)
    (series : (source.delete {first})✶.Parallel left right) :
    source✶.Parallel left right := by
  have contracted_circuit : (source✶.contract {first}).IsCircuit {left, right} := by
    simpa only [dual_delete] using series.isCircuit_pair distinct
  obtain ⟨lifted, circuit, contains_pair, contained⟩ :=
    contracted_circuit.exists_subset_isCircuit_of_contract
  have first_absent : first ∉ lifted := by
    intro first_member
    have second_member := parallel.mem_isCocircuit_of_mem circuit first_member
    have second_options := contained second_member
    rcases second_options with in_pair | in_singleton
    · rcases in_pair with equality | equality
      · exact left_avoids equality.symm
      · exact right_avoids equality.symm
    · have equal : second = first := in_singleton
      exact parallel_distinct equal.symm
  have lifted_eq : lifted = {left, right} := by
    apply Set.Subset.antisymm _ contains_pair
    intro element member
    rcases contained member with in_pair | in_singleton
    · exact in_pair
    · have equal : element = first := in_singleton
      exact (first_absent (equal ▸ member)).elim
  rw [lifted_eq] at circuit
  exact circuit.parallel_of_pair distinct

theorem Connected.two_element_parallel_and_series (connected : source.Connected)
    (ground : source.E = {first, second}) (distinct : first ≠ second) :
    source.Parallel first second ∧ source✶.Parallel first second := by
  have first_member : first ∈ source.E := by rw [ground]; simp
  have second_member : second ∈ source.E := by rw [ground]; simp
  obtain ⟨circuit, property, first_circuit, second_circuit⟩ :=
    connected.exists_isCircuit_of_ne first_member second_member distinct
  have equality : circuit = source.E := Set.Subset.antisymm property.subset_ground (by
    rw [ground]
    exact Set.pair_subset first_circuit second_circuit)
  have whole_circuit : source.IsCircuit source.E := equality ▸ property
  exact ⟨(ground ▸ whole_circuit).parallel_of_pair distinct,
    circuit_ground_series whole_circuit first_member second_member⟩

def MarkedSeriesParallelPair (source : Matroid Label) (marked : Label) : Prop :=
  ∃ first ∈ source.E, ∃ second ∈ source.E,
    first ≠ second ∧ first ≠ marked ∧ second ≠ marked ∧
      (source.Parallel first second ∨ source✶.Parallel first second)

theorem markedSeriesParallelPair_dual_iff :
    MarkedSeriesParallelPair source✶ marked ↔ MarkedSeriesParallelPair source marked := by
  simp only [MarkedSeriesParallelPair, dual_ground, dual_dual, or_comm]

theorem MarkedSeriesParallelPair.of_parallel_delete
    (parallel : source.Parallel marked second) (distinct : marked ≠ second)
    (pair : MarkedSeriesParallelPair (source.delete {marked}) second) :
    MarkedSeriesParallelPair source marked := by
  obtain ⟨left, left_member, right, right_member, left_right,
    left_avoids, right_avoids, property⟩ := pair
  refine ⟨left, left_member.1, right, right_member.1, left_right,
    by simpa using left_member.2, by simpa using right_member.2, ?_⟩
  rcases property with parallel_pair | series_pair
  · exact Or.inl (parallel_pair.of_isRestriction (delete_isRestriction _ _))
  · exact Or.inr (parallel.series_of_delete_avoiding distinct
      left_right left_avoids right_avoids series_pair)

theorem MarkedSeriesParallelPair.of_series_contract
    (series : source✶.Parallel marked second) (distinct : marked ≠ second)
    (pair : MarkedSeriesParallelPair (source.contract {marked}) second) :
    MarkedSeriesParallelPair source marked := by
  have dual_pair : MarkedSeriesParallelPair (source✶.delete {marked}) second := by
    obtain ⟨left, left_member, right, right_member, left_right,
      left_avoids, right_avoids, property⟩ := pair
    refine ⟨left, left_member, right, right_member, left_right,
      left_avoids, right_avoids, ?_⟩
    rcases property with parallel | series
    · exact Or.inr (by simpa only [dual_delete, dual_dual] using parallel)
    · exact Or.inl (by simpa only [dual_contract] using series)
  have lifted := dual_pair.of_parallel_delete series distinct
  obtain ⟨left, left_member, right, right_member, left_right,
    left_avoids, right_avoids, property⟩ := lifted
  refine ⟨left, left_member, right, right_member, left_right,
    left_avoids, right_avoids, ?_⟩
  rcases property with series | parallel
  · exact Or.inr series
  · exact Or.inl (by simpa only [dual_dual] using parallel)

theorem Connected.three_element_pair_avoiding_of_parallel [source.Finite]
    (connected : source.Connected) (parallel : source.Parallel marked second)
    (distinct : marked ≠ second) (size : source.E.ncard = 3) :
    MarkedSeriesParallelPair source marked := by
  have smaller_connected := connected.delete_parallel parallel distinct
  have smaller_size : (source.delete {marked}).E.ncard = 2 := by
    rw [parallel.delete_ground_ncard, size]
  obtain ⟨left, right, left_right, ground⟩ := Set.ncard_eq_two.mp smaller_size
  have pair := smaller_connected.two_element_parallel_and_series ground left_right
  have left_member : left ∈ (source.delete {marked}).E := by rw [ground]; simp
  have right_member : right ∈ (source.delete {marked}).E := by rw [ground]; simp
  exact ⟨left, left_member.1, right, right_member.1, left_right,
    by simpa using left_member.2, by simpa using right_member.2,
    Or.inl (pair.1.of_isRestriction (delete_isRestriction _ _))⟩

theorem Connected.three_element_pair_avoiding_of_series [source.Finite]
    (connected : source.Connected) (series : source✶.Parallel marked second)
    (distinct : marked ≠ second) (size : source.E.ncard = 3) :
    MarkedSeriesParallelPair source marked := by
  have smaller_connected := connected.contract_series series distinct
  have smaller_size : (source.contract {marked}).E.ncard = 2 := by
    rw [series_contract_ground_ncard series, size]
  obtain ⟨left, right, left_right, ground⟩ := Set.ncard_eq_two.mp smaller_size
  have pair := smaller_connected.two_element_parallel_and_series ground left_right
  have left_member : left ∈ (source.contract {marked}).E := by rw [ground]; simp
  have right_member : right ∈ (source.contract {marked}).E := by rw [ground]; simp
  have series_pair : source✶.Parallel left right := by
    have deleted_series : (source✶.delete {marked}).Parallel left right := by
      simpa only [dual_contract] using pair.2
    exact deleted_series.of_isRestriction (delete_isRestriction _ _)
  exact ⟨left, left_member.1, right, right_member.1, left_right,
    by simpa using left_member.2, by simpa using right_member.2, Or.inr series_pair⟩

theorem connected_binary_six_element_pair_avoiding [source.Finite]
    (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (lower : 3 ≤ source.E.ncard) (upper : source.E.ncard ≤ 6)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate))
    (marked_member : marked ∈ source.E) : MarkedSeriesParallelPair source marked := by
  classical
  suffices result : ∀ size : ℕ, ∀ candidate : Matroid Label, candidate.Finite →
      candidate.E.ncard = size → candidate.Connected → candidate.Representable (ZMod 2) →
      3 ≤ size → size ≤ 6 →
      (¬ ∃ smaller : Matroid Label, smaller ≤m candidate ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller)) →
      ∀ basepoint ∈ candidate.E, MarkedSeriesParallelPair candidate basepoint by
    exact result source.E.ncard source inferInstance rfl connected binary lower upper
      excluded marked marked_member
  intro size
  induction size using Nat.strong_induction_on with
  | h size induction =>
    intro candidate finite_candidate size_eq connected binary lower upper excluded
      basepoint basepoint_member
    let : candidate.Finite := finite_candidate
    let : Finite candidate.E := candidate.ground_finite.to_subtype
    have nontrivial : candidate.E.Nontrivial := Set.one_lt_ncard_iff_nontrivial.mp (by omega)
    obtain ⟨reduced, reduction⟩ := binary_six_element_k4_excluded_exists_elementary_reduction
      binary (by omega) excluded ⟨basepoint, basepoint_member⟩
    have recurse_parallel {other : Label} (parallel : candidate.Parallel basepoint other)
        (distinct : basepoint ≠ other) : MarkedSeriesParallelPair candidate basepoint := by
      by_cases three : size = 3
      · exact connected.three_element_pair_avoiding_of_parallel parallel distinct (by omega)
      have smaller_size := parallel.delete_ground_ncard
      have smaller_minor : candidate.delete {basepoint} ≤m candidate :=
        (delete_isRestriction _ _).isMinor
      have smaller_excluded : ¬ ∃ smaller : Matroid Label,
          smaller ≤m candidate.delete {basepoint} ∧
            Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller) := by
        rintro ⟨smaller, minor, isomorphism⟩
        exact excluded ⟨smaller, minor.trans smaller_minor, isomorphism⟩
      have pair := induction (candidate.delete {basepoint}).E.ncard (by omega)
        (candidate.delete {basepoint}) inferInstance rfl
        (connected.delete_parallel parallel distinct) (binary.delete {basepoint})
        (by omega) (by omega) smaller_excluded other
        ⟨parallel.2.1.mem_ground, by simpa using distinct.symm⟩
      exact pair.of_parallel_delete parallel distinct
    have recurse_series {other : Label} (series : candidate✶.Parallel basepoint other)
        (distinct : basepoint ≠ other) : MarkedSeriesParallelPair candidate basepoint := by
      by_cases three : size = 3
      · exact connected.three_element_pair_avoiding_of_series series distinct (by omega)
      have smaller_size := series_contract_ground_ncard series
      have smaller_minor : candidate.contract {basepoint} ≤m candidate := contract_isMinor _ _
      have smaller_excluded : ¬ ∃ smaller : Matroid Label,
          smaller ≤m candidate.contract {basepoint} ∧
            Nonempty (Iso BondalThomsen.k4GraphCycleMatroid smaller) := by
        rintro ⟨smaller, minor, isomorphism⟩
        exact excluded ⟨smaller, minor.trans smaller_minor, isomorphism⟩
      have pair := induction (candidate.contract {basepoint}).E.ncard (by omega)
        (candidate.contract {basepoint}) inferInstance rfl
        (connected.contract_series series distinct) (binary.contract {basepoint})
        (by omega) (by omega) smaller_excluded other
        ⟨series.2.1.mem_ground, by simpa using distinct.symm⟩
      exact pair.of_series_contract series distinct
    cases reduction with
    | loop element loop =>
      exact ((connected.isNonloop nontrivial loop.mem_ground).not_isLoop loop).elim
    | coloop element coloop =>
      exact (connected.not_isColoop nontrivial coloop.mem_ground coloop).elim
    | parallel left right distinct parallel =>
      by_cases left_marked : left = basepoint
      · subst left
        exact recurse_parallel parallel distinct
      by_cases right_marked : right = basepoint
      · subst right
        exact recurse_parallel parallel.symm distinct.symm
      exact ⟨left, parallel.1.mem_ground, right, parallel.2.1.mem_ground,
        distinct, left_marked, right_marked, Or.inl parallel⟩
    | series left right distinct series =>
      by_cases left_marked : left = basepoint
      · subst left
        exact recurse_series series distinct
      by_cases right_marked : right = basepoint
      · subst right
        exact recurse_series series.symm distinct.symm
      exact ⟨left, series.1.mem_ground, right, series.2.1.mem_ground,
        distinct, left_marked, right_marked, Or.inr series⟩

theorem MarkedSeriesParallelPair.ground_ncard_ge_three [source.Finite]
    (pair : MarkedSeriesParallelPair source marked) (marked_member : marked ∈ source.E) :
    3 ≤ source.E.ncard := by
  obtain ⟨left, left_member, right, right_member, distinct,
    left_avoids, right_avoids, _⟩ := pair
  have subset : ({left, right, marked} : Set Label) ⊆ source.E :=
    Set.insert_subset left_member (Set.pair_subset right_member marked_member)
  have bound := Set.ncard_le_ncard subset source.ground_finite
  simpa [distinct, left_avoids, right_avoids] using bound

end Matroid
