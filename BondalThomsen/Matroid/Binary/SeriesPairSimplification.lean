module

public import BondalThomsen.Matroid.Binary.MarkedRankFour
public import BondalThomsen.Matroid.RepresentedSimplification
public import BondalThomsen.Matroid.Binary.FourQuotientContraction

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label}
    {contracted partner first second : Label}

theorem series_pair_mem_isCircuit_iff (series : source✶.Parallel contracted partner)
    {circuit : Set Label} (property : source.IsCircuit circuit) :
    contracted ∈ circuit ↔ partner ∈ circuit := by
  constructor
  · exact series.mem_isCocircuit_of_mem property.isCocircuit
  · exact series.symm.mem_isCocircuit_of_mem property.isCocircuit

theorem Simple.seriesPairContract_isNonloop [source.Simple]
    (contracted_member : contracted ∈ source.E)
    (member : first ∈ (source.contract {contracted}).E) :
    (source.contract {contracted}).IsNonloop first := by
  have independent := simple_iff_forall_pair_indep.mp (inferInstance : source.Simple)
    contracted first contracted_member member.1
  have nonloop : source.IsNonloop contracted :=
    ((Simple.parallel_iff_eq contracted_member).mpr rfl).1
  apply indep_singleton.mp
  rw [nonloop.contractElem_indep_iff]
  exact ⟨by simpa only [mem_singleton_iff, eq_comm] using member.2, independent⟩

theorem Simple.seriesPairContract_loopless [source.Simple]
    (contracted_member : contracted ∈ source.E) :
    (source.contract {contracted}).Loopless := by
  exact loopless_iff_forall_isNonloop.mpr fun _ member =>
    Simple.seriesPairContract_isNonloop contracted_member member

theorem Simple.seriesPairContract_parallel_involves_partner [source.Simple]
    (series : source✶.Parallel contracted partner)
    (series_distinct : contracted ≠ partner)
    (parallel : (source.contract {contracted}).Parallel first second)
    (distinct : first ≠ second) : first = partner ∨ second = partner := by
  obtain ⟨circuit, property, contained, bounded⟩ :=
    (parallel.isCircuit_pair distinct).exists_subset_isCircuit_of_contract
  have contracted_circuit : contracted ∈ circuit := by
    by_contra absent
    have circuit_pair : circuit = {first, second} := by
      apply subset_antisymm _ contained
      intro element member
      rcases bounded member with retained | removed
      · exact retained
      · have equal : element = contracted := by simpa using removed
        exact (absent (equal ▸ member)).elim
    rw [circuit_pair] at property
    have original_parallel := property.parallel_of_pair distinct
    exact distinct ((@Simple.parallel_iff_eq _ source inferInstance first second
      original_parallel.1.mem_ground).mp original_parallel)
  have partner_circuit := (series_pair_mem_isCircuit_iff series property).mp contracted_circuit
  rcases bounded partner_circuit with retained | removed
  · simpa only [mem_insert_iff, mem_singleton_iff, eq_comm] using retained
  · have equal : partner = contracted := by simpa using removed
    exact (series_distinct equal.symm).elim

theorem IsNonloop.seriesPairContract_eRank_add_one [source.Finite]
    (nonloop : source.IsNonloop contracted) :
    (source.contract {contracted}).eRank + 1 = source.eRank := by
  obtain ⟨basis, property, contained⟩ := nonloop.indep.exists_isBase_superset
  have member : contracted ∈ basis := contained (by simp)
  have base_contracted : (source.contract {contracted}).IsBase (basis \ {contracted}) := by
    apply nonloop.indep.contract_isBase_iff.mpr
    exact ⟨by simpa only [sdiff_union_of_subset contained] using property,
      disjoint_sdiff_left⟩
  rw [← base_contracted.encard_eq_eRank, ← property.encard_eq_eRank]
  have decomposition : basis = insert contracted (basis \ {contracted}) := by
    ext element
    simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff]
    constructor
    · intro chosen
      by_cases same : element = contracted
      · exact Or.inl same
      · exact Or.inr ⟨chosen, same⟩
    · rintro (rfl | ⟨chosen, _⟩)
      · exact member
      · exact chosen
  conv_rhs => rw [decomposition]
  exact (encard_insert_of_notMem (by simp)).symm

theorem IsNonloop.seriesPairContract_rank_drop [source.Finite]
    (nonloop : source.IsNonloop contracted) :
    (source.contract {contracted}).eRank.toNat + 1 = source.eRank.toNat := by
  have equality := congrArg ENat.toNat nonloop.seriesPairContract_eRank_add_one
  rw [ENat.toNat_add ((source.contract {contracted}).eRank_ne_top_iff.mpr inferInstance)
    (by simp)] at equality
  simpa using equality

theorem Simple.seriesPairContract_simplification_rank [source.Finite] [source.Simple]
    (series : source✶.Parallel contracted partner)
    {simplified : Matroid Label}
    (simplification : simplified.IsSimplification (source.contract {contracted})) :
    simplified.eRank + 1 = source.eRank := by
  rw [simplification.eRank_eq]
  exact IsNonloop.seriesPairContract_eRank_add_one
    (((Simple.parallel_iff_eq (show contracted ∈ source.E by
      simpa using series.1.mem_ground)).mpr rfl).1)

theorem Simple.seriesPairContract_simplification_ground_loss_le_two
    [source.Finite] [source.Simple]
    (series : source✶.Parallel contracted partner)
    (series_distinct : contracted ≠ partner)
    {simplified : Matroid Label}
    (simplification : simplified.IsSimplification (source.contract {contracted})) :
    source.E.ncard ≤ simplified.E.ncard + 2 := by
  classical
  have contracted_member : contracted ∈ source.E := by simpa using series.1.mem_ground
  have partner_member : partner ∈ (source.contract {contracted}).E := by
    exact ⟨by simpa using series.2.1.mem_ground,
      by simpa only [mem_singleton_iff] using series_distinct.symm⟩
  let representative : Label → Label := fun element =>
    if nonloop : (source.contract {contracted}).IsNonloop element then
      (simplification.exists_unique nonloop).choose else element
  have representative_spec : ∀ element ∈ (source.contract {contracted}).E,
      representative element ∈ simplified.E ∧
        (source.contract {contracted}).Parallel element (representative element) := by
    intro element member
    have nonloop := Simple.seriesPairContract_isNonloop contracted_member member
    simpa only [representative, dite_eq_left nonloop] using
      (simplification.exists_unique nonloop).choose_spec.1
  have representative_injective : InjOn representative
      ((source.contract {contracted}).E \ {partner}) := by
    intro first first_member second second_member equality
    have first_spec := representative_spec first first_member.1
    have second_spec := representative_spec second second_member.1
    rw [equality] at first_spec
    by_contra distinct
    rcases Simple.seriesPairContract_parallel_involves_partner series series_distinct
      (first_spec.2.trans second_spec.2.symm) distinct with equal | equal
    · exact first_member.2 (by simpa using equal)
    · exact second_member.2 (by simpa using equal)
  have simplified_finite := simplification.2.1.finite
  let : simplified.Finite := simplified_finite
  have bound := ncard_le_ncard_of_injOn representative
    (fun element member => (representative_spec element member.1).1)
    representative_injective simplified.ground_finite
  have contraction_count := series_contract_ground_ncard series
  have remaining_count := ncard_sdiff_singleton_of_mem partner_member
  have partner_positive : 1 ≤ (source.contract {contracted}).E.ncard := by
    have singleton_bound := ncard_le_ncard (singleton_subset_iff.mpr partner_member)
      (source.contract {contracted}).ground_finite
    simpa only [ncard_singleton] using singleton_bound
  omega

theorem Simple.seriesPairContract_simplification_ground_card_range
    [source.Finite] [source.Simple]
    (series : source✶.Parallel contracted partner)
    (series_distinct : contracted ≠ partner)
    {simplified : Matroid Label}
    (simplification : simplified.IsSimplification (source.contract {contracted})) :
    simplified.E.ncard = source.E.ncard - 1 ∨
      simplified.E.ncard = source.E.ncard - 2 := by
  have upper := ncard_le_ncard simplification.2.1.subset
    (source.contract {contracted}).ground_finite
  rw [series_contract_ground_ncard series] at upper
  have lower := Simple.seriesPairContract_simplification_ground_loss_le_two
    series series_distinct simplification
  omega

theorem Simple.seriesPairContract_simple_of_no_partner_parallel [source.Simple]
    (series : source✶.Parallel contracted partner)
    (series_distinct : contracted ≠ partner)
    (no_pair : ∀ element, (source.contract {contracted}).Parallel partner element →
      element = partner) : (source.contract {contracted}).Simple := by
  have contracted_member : contracted ∈ source.E := by simpa using series.1.mem_ground
  let : (source.contract {contracted}).Loopless :=
    Simple.seriesPairContract_loopless contracted_member
  constructor
  intro first second first_member
  constructor
  · intro parallel
    by_contra distinct
    rcases Simple.seriesPairContract_parallel_involves_partner series series_distinct
      parallel distinct with equal | equal
    · subst first
      exact distinct (no_pair second parallel).symm
    · subst second
      exact distinct (no_pair first parallel.symm)
  · rintro rfl
    exact (isNonloop_of_loopless first_member).parallel_self

theorem Simple.seriesPairContract_delete_partner_isSimplification [source.Simple]
    (series : source✶.Parallel contracted partner)
    (series_distinct : contracted ≠ partner)
    (parallel : (source.contract {contracted}).Parallel partner first)
    (parallel_distinct : first ≠ partner) :
    ((source.contract {contracted}).delete {partner}).IsSimplification
      (source.contract {contracted}) := by
  have contracted_member : contracted ∈ source.E := by simpa using series.1.mem_ground
  let : (source.contract {contracted}).Loopless :=
    Simple.seriesPairContract_loopless contracted_member
  refine ⟨(delete_isRestriction _ _).loopless, delete_isRestriction _ _, ?_⟩
  intro element nonloop
  have unique : ∀ representative other,
      representative ∈ ((source.contract {contracted}).delete {partner}).E →
      other ∈ ((source.contract {contracted}).delete {partner}).E →
      (source.contract {contracted}).Parallel element representative →
      (source.contract {contracted}).Parallel element other → other = representative := by
    intro representative other representative_member other_member first_pair second_pair
    by_contra distinct
    rcases Simple.seriesPairContract_parallel_involves_partner series series_distinct
      (second_pair.symm.trans first_pair) distinct with equal | equal
    · exact other_member.2 (by simpa using equal)
    · exact representative_member.2 (by simpa using equal)
  by_cases same : element = partner
  · subst element
    have retained : first ∈ ((source.contract {contracted}).delete {partner}).E :=
      ⟨parallel.2.1.mem_ground, by simpa using parallel_distinct⟩
    exact ⟨first, ⟨retained, parallel⟩, fun other property =>
      unique first other retained property.1 parallel property.2⟩
  · have retained : element ∈ ((source.contract {contracted}).delete {partner}).E :=
      ⟨nonloop.mem_ground, by simpa using same⟩
    exact ⟨element, ⟨retained, nonloop.parallel_self⟩, fun other property =>
      unique element other retained property.1 nonloop.parallel_self property.2⟩

theorem Simple.seriesPairContract_exists_simplification [source.Finite] [source.Simple]
    (series : source✶.Parallel contracted partner)
    (series_distinct : contracted ≠ partner) :
    ∃ simplified : Matroid Label,
      simplified.IsSimplification (source.contract {contracted}) ∧
      (simplified = source.contract {contracted} ∨
        simplified = (source.contract {contracted}).delete {partner}) ∧
      simplified.Simple ∧ simplified.eRank + 1 = source.eRank ∧
      source.E.ncard ≤ simplified.E.ncard + 2 ∧
      (simplified.E.ncard = source.E.ncard - 1 ∨
        simplified.E.ncard = source.E.ncard - 2) := by
  classical
  suffices construction : ∃ simplified : Matroid Label,
      simplified.IsSimplification (source.contract {contracted}) ∧
      (simplified = source.contract {contracted} ∨
        simplified = (source.contract {contracted}).delete {partner}) by
    obtain ⟨simplified, simplification, form⟩ := construction
    exact ⟨simplified, simplification, form, simplification.simple,
      Simple.seriesPairContract_simplification_rank series simplification,
      Simple.seriesPairContract_simplification_ground_loss_le_two
        series series_distinct simplification,
      Simple.seriesPairContract_simplification_ground_card_range
        series series_distinct simplification⟩
  by_cases pair : ∃ element, (source.contract {contracted}).Parallel partner element ∧
      element ≠ partner
  · obtain ⟨element, parallel, distinct⟩ := pair
    exact ⟨(source.contract {contracted}).delete {partner},
      Simple.seriesPairContract_delete_partner_isSimplification
        series series_distinct parallel distinct, Or.inr rfl⟩
  · have no_pair : ∀ element, (source.contract {contracted}).Parallel partner element →
        element = partner := by
      intro element parallel
      by_contra distinct
      exact pair ⟨element, parallel, distinct⟩
    let : (source.contract {contracted}).Simple :=
      Simple.seriesPairContract_simple_of_no_partner_parallel series series_distinct no_pair
    let : (source.contract {contracted}).Loopless :=
      Simple.seriesPairContract_loopless (by simpa using series.1.mem_ground)
    refine ⟨source.contract {contracted}, ⟨inferInstance, IsRestriction.refl, ?_⟩,
      Or.inl rfl⟩
    intro element nonloop
    refine ⟨element, ⟨nonloop.mem_ground, nonloop.parallel_self⟩, ?_⟩
    intro other property
    exact ((Simple.parallel_iff_eq nonloop.mem_ground).mp property.2).symm

end Matroid
