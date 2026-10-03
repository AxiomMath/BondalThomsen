module

public import BondalThomsen.Matroid.Binary.TriangleTriadK4Construction
public import BondalThomsen.Matroid.Binary.FourQuotientContraction

@[expose] public section

namespace Matroid

open Set Submodule

variable {Label : Type*} {source : Matroid Label}
    {pivot first second third firstPartner secondPartner : Label}

theorem IsCircuit.shorten_to_triple {circuit : Set Label}
    (property : source.IsCircuit circuit) (first_member : first ∈ circuit)
    (second_member : second ∈ circuit) (third_member : third ∈ circuit) :
    (source.contract (circuit \ {first, second, third})).IsCircuit {first, second, third} :=
  property.contract_sdiff_isCircuit (by simp)
    (by simp only [Set.insert_subset_iff, Set.singleton_subset_iff];
        exact ⟨first_member, second_member, third_member⟩)

section Representation

variable {Vector : Type*} [AddCommGroup Vector] [Module (ZMod 2) Vector]
    (representation : source.Rep (ZMod 2) Vector)

theorem Rep.binary_parallel_eq (parallel : source.Parallel first second) :
    representation first = representation second := by
  have closure_member : first ∈ source.closure {second} := by
    rw [← parallel.2.2]
    exact source.mem_closure_self first parallel.1.mem_ground
  have member : representation first ∈ span (ZMod 2) {representation second} := by
    simpa only [Set.image_singleton] using
      (representation.mem_closure_iff parallel.1.mem_ground).mp closure_member
  obtain ⟨coefficient, equality⟩ := Submodule.mem_span_singleton.mp member
  have cases : coefficient = 0 ∨ coefficient = 1 := by
    exact (by decide : ∀ coefficient : ZMod 2, coefficient = 0 ∨ coefficient = 1) coefficient
  rcases cases with rfl | rfl
  · have zero : representation first = 0 := by simpa using equality.symm
    exact ((representation.ne_zero_iff_isNonloop first).mpr parallel.1 zero).elim
  · simpa using equality.symm

theorem Rep.binary_triangle_add [source.Simple]
    (triangle : source.IsCircuit {first, second, third}) :
    representation third = representation first + representation second := by
  have third_member : third ∈ source.E := triangle.subset_ground (by simp)
  have closure := Simple.triangle_completion_mem_closure triangle
  have span_member := (representation.mem_closure_iff third_member).mp closure
  rw [Set.image_pair] at span_member
  obtain ⟨first_coefficient, second_coefficient, equality⟩ := Submodule.mem_span_pair.mp span_member
  have cases : ∀ coefficient : ZMod 2, coefficient = 0 ∨ coefficient = 1 := by decide
  have distinct := Simple.isCircuit_triple_distinct triangle
  have no_equal (member : third ∈ source.closure {first}) : False := by
    have nonloop : source.IsNonloop third := ((Simple.parallel_iff_eq third_member).mpr rfl).1
    have first_nonloop : source.IsNonloop first :=
      ((Simple.parallel_iff_eq (triangle.subset_ground (by simp))).mpr rfl).1
    have parallel : source.Parallel third first :=
      ⟨nonloop, first_nonloop, nonloop.closure_eq_of_mem_closure member⟩
    exact distinct.2.1 ((Simple.parallel_iff_eq third_member).mp parallel).symm
  have no_equal_second (member : third ∈ source.closure {second}) : False := by
    have nonloop : source.IsNonloop third := ((Simple.parallel_iff_eq third_member).mpr rfl).1
    have second_nonloop : source.IsNonloop second :=
      ((Simple.parallel_iff_eq (triangle.subset_ground (by simp))).mpr rfl).1
    have parallel : source.Parallel third second :=
      ⟨nonloop, second_nonloop, nonloop.closure_eq_of_mem_closure member⟩
    exact distinct.2.2 ((Simple.parallel_iff_eq third_member).mp parallel).symm
  rcases cases first_coefficient with rfl | rfl <;>
    rcases cases second_coefficient with rfl | rfl
  · have zero : representation third = 0 := by simpa using equality.symm
    exact ((representation.ne_zero_iff_isNonloop third).mpr
      ((Simple.parallel_iff_eq third_member).mpr rfl).1 zero).elim
  · apply (no_equal_second ?_).elim
    apply (representation.mem_closure_iff third_member).mpr
    rw [Set.image_singleton]
    have same : representation third = representation second := by simpa using equality.symm
    rw [same]
    exact Submodule.mem_span_singleton_self _
  · apply (no_equal ?_).elim
    apply (representation.mem_closure_iff third_member).mpr
    rw [Set.image_singleton]
    have same : representation third = representation first := by simpa using equality.symm
    rw [same]
    exact Submodule.mem_span_singleton_self _
  · simpa using equality.symm

end Representation

def binaryConnectorCoefficients (twisted : Bool) : Fin 6 → Fin 3 → ZMod 2 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1],
    if twisted then ![1, 1, 1] else ![0, 1, 1]]

theorem binaryConnectorCoefficients_nonzero :
    ∀ twisted index, binaryConnectorCoefficients twisted index ≠ 0 := by decide

theorem binaryConnectorCoefficients_injective :
    ∀ twisted, Function.Injective (binaryConnectorCoefficients twisted) := by decide

section Certificate

variable {Vector : Type*} [AddCommGroup Vector] [Module (ZMod 2) Vector]

theorem Rep.binary_connector_certificate_has_graph_k4_minor
    (representation : source.Rep (ZMod 2) Vector)
    (basisLabels : Fin 3 → Label) (labels : Fin 6 → Label) (twisted : Bool)
    (independent : LinearIndependent (ZMod 2) (representation ∘ basisLabels))
    (ground : ∀ index, labels index ∈ source.E)
    (equations : ∀ index, representation (labels index) =
      Fintype.linearCombination (ZMod 2) (representation ∘ basisLabels)
        (binaryConnectorCoefficients twisted index)) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
  classical
  let change : (Fin 3 → ZMod 2) →ₗ[ZMod 2] Vector :=
    Fintype.linearCombination (ZMod 2) (representation ∘ basisLabels)
  have change_injective : Function.Injective change :=
    independent.fintypeLinearCombination_injective
  have nonzero : ∀ index, representation (labels index) ≠ 0 := by
    intro index zero
    apply binaryConnectorCoefficients_nonzero twisted index
    apply change_injective
    simpa only [change, equations, map_zero] using zero
  have labels_injective : Function.Injective labels := by
    intro first second equality
    apply binaryConnectorCoefficients_injective twisted
    apply change_injective
    simpa only [change, ← equations] using congrArg representation equality
  have image_injective : Set.InjOn representation (Set.range labels) := by
    rintro first ⟨first_index, rfl⟩ second ⟨second_index, rfl⟩ equality
    have indices : first_index = second_index := binaryConnectorCoefficients_injective twisted
      (change_injective (by simpa only [change, ← equations] using equality))
    exact congrArg labels indices
  let selected : Set Label := Set.range labels
  have subset : selected ⊆ source.E := by rintro label ⟨index, rfl⟩; exact ground index
  let : (source.restrict selected).Finite := ⟨Set.finite_range labels⟩
  let : (source.restrict selected).Simple := by
    constructor
    intro first second first_member
    have first_selected : first ∈ selected := first_member
    constructor
    · intro parallel
      have equality := (representation.restrict selected).binary_parallel_eq parallel
      apply image_injective first_member parallel.2.1.mem_ground
      have second_selected : second ∈ selected := parallel.2.1.mem_ground
      change selected.indicator representation first = selected.indicator representation second at equality
      simpa [Set.indicator, first_selected, second_selected] using equality
    · rintro rfl
      have original_nonzero : representation first ≠ 0 := by
        obtain ⟨index, equality⟩ := first_member
        exact equality ▸ nonzero index
      have restricted_nonzero : (representation.restrict selected) first ≠ 0 := by
        change selected.indicator representation first ≠ 0
        simpa [Set.indicator, first_selected] using original_nonzero
      exact ((representation.restrict selected).ne_zero_iff_isNonloop first).mp
        restricted_nonzero |>.parallel_self
  have count : selected.ncard = 6 := by
    change (Set.range labels).ncard = 6
    rw [Set.ncard_range_of_injective labels_injective]
    simp
  have basis_subset : Set.range basisLabels ⊆ source.E := by
    intro label member
    have nonzero_basis := independent.ne_zero (Classical.choose member)
    have equality := Classical.choose_spec member
    by_contra outside
    exact nonzero_basis (by simpa only [Function.comp_apply, equality] using
      representation.eq_zero_of_notMem_ground outside)
  have closure : selected ⊆ source.closure (Set.range basisLabels) := by
    rintro label ⟨index, rfl⟩
    apply (representation.mem_closure_iff (ground index)).mpr
    rw [equations index, Fintype.linearCombination_apply]
    apply Submodule.sum_mem
    intro coordinate member
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨basisLabels coordinate, Set.mem_range_self coordinate, rfl⟩
  have rank : (source.restrict selected).eRank ≤ 3 := by
    calc
      (source.restrict selected).eRank = source.eRk selected := source.eRank_restrict selected
      _ ≤ source.eRk (source.closure (Set.range basisLabels)) := source.eRk_mono closure
      _ = source.eRk (Set.range basisLabels) := source.eRk_closure_eq _
      _ ≤ (Set.range basisLabels).encard := source.eRk_le_encard _
      _ ≤ 3 := by
        simpa [Set.image_univ, Set.encard_univ, ENat.card_eq_coe_natCard,
          Nat.card_eq_fintype_card, Fintype.card_fin] using
          Set.encard_image_le basisLabels Set.univ
  obtain ⟨isomorphism⟩ := binary_simple_rank_three_six_restriction_iso_graph_k4
    (representation.restrict selected).representable rank (Set.Subset.refl selected) count
  refine ⟨source.restrict selected, (source.restrict_isRestriction selected subset).isMinor, ?_⟩
  exact ⟨by simpa only [source.restrict_restrict_eq (Set.Subset.refl selected)] using isomorphism.symm⟩

end Certificate

section CircuitRepresentation

variable {Vector : Type*} [AddCommGroup Vector] [Module (ZMod 2) Vector]

theorem Rep.binary_distinct_triangle_add
    (representation : source.Rep (ZMod 2) Vector)
    (triangle : source.IsCircuit {first, second, third})
    (first_second : first ≠ second) (first_third : first ≠ third)
    (second_third : second ≠ third) :
    representation third = representation first + representation second := by
  classical
  have nontrivial : ({first, second, third} : Set Label).Nontrivial :=
    Set.nontrivial_of_mem_mem_ne (by simp) (by simp) first_second
  have third_nonloop := triangle.isNonloop_of_mem nontrivial (by simp : third ∈ _)
  have closure : third ∈ source.closure {first, second} := by
    have remainder : ({first, second, third} : Set Label) \ {third} = {first, second} := by
      ext element
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    simpa only [remainder] using
      triangle.mem_closure_sdiff_singleton_of_mem (by simp : third ∈ _)
  have span_member := (representation.mem_closure_iff third_nonloop.mem_ground).mp closure
  rw [Set.image_pair] at span_member
  obtain ⟨first_coefficient, second_coefficient, equality⟩ := Submodule.mem_span_pair.mp span_member
  have not_first : representation third ∉ span (ZMod 2) {representation first} := by
    have independent : source.Indep {first, third} := by
      convert triangle.sdiff_singleton_indep (by simp : second ∈ _) using 1
      ext element
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    have outside := (representation.onIndep independent).notMem_span (by simp : third ∈ _)
    simpa [first_third] using outside
  have not_second : representation third ∉ span (ZMod 2) {representation second} := by
    have independent : source.Indep {second, third} := by
      convert triangle.sdiff_singleton_indep (by simp : first ∈ _) using 1
      ext element
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    have outside := (representation.onIndep independent).notMem_span (by simp : third ∈ _)
    simpa [second_third] using outside
  have cases : ∀ coefficient : ZMod 2, coefficient = 0 ∨ coefficient = 1 := by decide
  rcases cases first_coefficient with rfl | rfl <;>
    rcases cases second_coefficient with rfl | rfl
  · exact ((representation.ne_zero_iff_isNonloop third).mpr third_nonloop
      (by simpa using equality.symm)).elim
  · exact (not_second (by simp [equality.symm])).elim
  · exact (not_first (by simp [equality.symm])).elim
  · simpa using equality.symm

theorem Rep.binary_contract_triangle_connector
    (representation : source.Rep (ZMod 2) Vector)
    (triangle : (source.contract {pivot}).IsCircuit {first, second, third})
    (first_second : first ≠ second) (first_third : first ≠ third)
    (second_third : second ≠ third) :
    representation third = representation first + representation second ∨
      representation third = representation pivot + representation first + representation second := by
  have equality := (representation.contract {pivot}).binary_distinct_triangle_add
    triangle first_second first_third second_third
  let pivot_span := span (ZMod 2) (representation '' {pivot})
  have quotient_equality : pivot_span.mkQ (representation third) =
      pivot_span.mkQ (representation first + representation second) := by
    change pivot_span.mkQ (representation third) =
      pivot_span.mkQ (representation first) + pivot_span.mkQ (representation second) at equality
    simpa only [map_add] using equality
  have member := (Submodule.Quotient.eq pivot_span).mp quotient_equality
  change representation third - (representation first + representation second) ∈
    span (ZMod 2) (representation '' {pivot}) at member
  rw [Set.image_singleton, Submodule.mem_span_singleton] at member
  obtain ⟨coefficient, equality⟩ := member
  have cases : coefficient = 0 ∨ coefficient = 1 :=
    (by decide : ∀ coefficient : ZMod 2, coefficient = 0 ∨ coefficient = 1) coefficient
  rcases cases with rfl | rfl
  · left
    exact sub_eq_zero.mp (by simpa using equality.symm)
  · right
    have difference : representation third - (representation first + representation second) =
        representation pivot := by simpa using equality.symm
    simpa only [add_assoc] using sub_eq_iff_eq_add.mp difference

end CircuitRepresentation

theorem IsCircuit.exists_third_of_indep_pair {circuit : Set Label}
    (property : source.IsCircuit circuit) (_first_member : first ∈ circuit)
    (_second_member : second ∈ circuit) (independent : source.Indep {first, second}) :
    ∃ third ∈ circuit, third ≠ first ∧ third ≠ second := by
  classical
  by_contra absent
  push Not at absent
  apply property.not_indep
  apply independent.subset
  intro element member
  by_cases same : element = first
  · simp [same]
  · simp [absent element member same]

theorem IsCircuit.avoids_parallel_partner {circuit : Set Label}
    (property : source.IsCircuit circuit) (first_member : first ∈ circuit)
    (second_member : second ∈ circuit) (pair_circuit : source.IsCircuit {first, firstPartner})
    (second_avoids : second ≠ first) (second_avoids_partner : second ≠ firstPartner) :
    firstPartner ∉ circuit := by
  intro partner_member
  have equality := pair_circuit.eq_of_subset_isCircuit property
    (Set.pair_subset first_member partner_member)
  have member : second ∈ ({first, firstPartner} : Set Label) := equality.symm ▸ second_member
  simp [second_avoids, second_avoids_partner] at member

theorem binary_two_triangles_connected_contract_shortening [source.Simple]
    (first_triangle : source.IsCircuit {pivot, first, firstPartner})
    (second_triangle : source.IsCircuit {pivot, second, secondPartner})
    (independent : source.Indep {pivot, first, second})
    (connected : (source.contract {pivot}).Connected)
    (first_second : first ≠ second)
    (second_avoids_partner : second ≠ firstPartner)
    (first_avoids_partner : first ≠ secondPartner) :
    ∃ contracted : Set Label, ∃ third : Label,
      source.Indep contracted ∧ third ∈ source.E ∧
      pivot ∉ contracted ∧ first ∉ contracted ∧ second ∉ contracted ∧
      firstPartner ∉ contracted ∧ secondPartner ∉ contracted ∧ third ∉ contracted ∧
      third ≠ pivot ∧ third ≠ first ∧ third ≠ second ∧
      (source.contract contracted).Indep {pivot, first, second} ∧
      ((source.contract contracted).contract {pivot}).IsCircuit {first, second, third} := by
  classical
  have distinct := Simple.isCircuit_triple_distinct first_triangle
  have other_distinct := Simple.isCircuit_triple_distinct second_triangle
  have pivot_nonloop : source.IsNonloop pivot :=
    first_triangle.isNonloop_of_mem (Set.nontrivial_of_mem_mem_ne
      (by simp) (by simp) distinct.1) (by simp)
  have pair_independent : (source.contract {pivot}).Indep {first, second} := by
    rw [pivot_nonloop.contractElem_indep_iff]
    refine ⟨by simp [distinct.1, other_distinct.1], independent⟩
  have first_member : first ∈ (source.contract {pivot}).E :=
    pair_independent.subset_ground (by simp)
  have second_member : second ∈ (source.contract {pivot}).E :=
    pair_independent.subset_ground (by simp)
  have first_pair : (source.contract {pivot}).IsCircuit {first, firstPartner} := by
    convert first_triangle.contractElem_isCircuit (e := pivot)
      (Set.nontrivial_of_mem_mem_ne (by simp) (by simp) distinct.1) (by simp) using 1
    ext element
    simp [distinct.1, distinct.2.1]
  have second_pair : (source.contract {pivot}).IsCircuit {second, secondPartner} := by
    convert second_triangle.contractElem_isCircuit (e := pivot)
      (Set.nontrivial_of_mem_mem_ne (by simp) (by simp) other_distinct.1) (by simp) using 1
    ext element
    simp [other_distinct.1, other_distinct.2.1]
  obtain same | ⟨circuit, property, first_in, second_in⟩ :=
    connected.forall_connectedTo first_member second_member
  · exact (first_second same.1).elim
  have firstPartner_out := property.avoids_parallel_partner first_in second_in first_pair
    first_second.symm second_avoids_partner
  have secondPartner_out := property.avoids_parallel_partner second_in first_in second_pair
    first_second first_avoids_partner
  obtain ⟨third, third_in, third_first, third_second⟩ :=
    property.exists_third_of_indep_pair first_in second_in pair_independent
  have pivot_out : pivot ∉ circuit := by
    intro member
    have ground := property.subset_ground member
    simp at ground
  let contracted := circuit \ {first, second, third}
  have contracted_subset : contracted ⊆ circuit \ {third} := by
    intro element member
    exact ⟨member.1, fun same => member.2 (by simp [Set.mem_singleton_iff.mp same])⟩
  have remaining_independent := property.sdiff_singleton_indep third_in
  have contracted_independent : (source.contract {pivot}).Indep contracted :=
    remaining_independent.subset contracted_subset
  have original_independent :=
    (pivot_nonloop.contractElem_indep_iff.mp contracted_independent).2
  have contracted_original : source.Indep contracted := original_independent.subset
    (Set.subset_insert _ _)
  have combined : source.Indep (insert pivot (circuit \ {third})) :=
    (pivot_nonloop.contractElem_indep_iff.mp remaining_independent).2
  have final_independent : (source.contract contracted).Indep {pivot, first, second} := by
    rw [contracted_original.contract_indep_iff]
    constructor
    · rw [Set.disjoint_left]
      intro element member contracted_member
      rcases member with same | same | same
      · exact pivot_out (same ▸ contracted_member.1)
      · exact contracted_member.2 (by simp [same])
      · exact contracted_member.2 (by simp [Set.mem_singleton_iff.mp same])
    · apply combined.subset
      intro element member
      rcases member with member | member
      · rcases member with same | same | same
        · simp [same]
        · exact Or.inr ⟨same ▸ first_in, by simpa [same] using third_first.symm⟩
        · exact Or.inr ⟨Set.mem_singleton_iff.mp same ▸ second_in,
            by simpa [Set.mem_singleton_iff.mp same] using third_second.symm⟩
      · exact Or.inr (contracted_subset member)
  refine ⟨contracted, third, contracted_original,
    (property.subset_ground third_in).1, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, third_first, third_second, final_independent, ?_⟩
  · exact fun member => pivot_out member.1
  · simp [contracted]
  · simp [contracted]
  · exact fun member => firstPartner_out member.1
  · exact fun member => secondPartner_out member.1
  · simp [contracted]
  · exact fun same => pivot_out (same ▸ third_in)
  · rw [source.contract_comm]
    exact property.shorten_to_triple first_in second_in third_in

theorem binary_two_triangles_connected_contract_has_graph_k4_minor [source.Simple]
    (binary : source.Representable (ZMod 2))
    (first_triangle : source.IsCircuit {pivot, first, firstPartner})
    (second_triangle : source.IsCircuit {pivot, second, secondPartner})
    (independent : source.Indep {pivot, first, second})
    (connected : (source.contract {pivot}).Connected)
    (first_second : first ≠ second)
    (second_avoids_partner : second ≠ firstPartner)
    (first_avoids_partner : first ≠ secondPartner) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
  classical
  obtain ⟨contracted, third, contracted_independent, third_ground, pivot_out, first_out,
    second_out, firstPartner_out, secondPartner_out, third_out, third_pivot, third_first,
    third_second, final_independent, final_triangle⟩ :=
    binary_two_triangles_connected_contract_shortening first_triangle second_triangle independent
      connected first_second second_avoids_partner first_avoids_partner
  obtain ⟨original_representation⟩ := binary
  let representation := original_representation.contract contracted
  have first_add := original_representation.binary_triangle_add first_triangle
  have second_add := original_representation.binary_triangle_add second_triangle
  have first_contracted_add : representation firstPartner =
      representation pivot + representation first := by
    change (span (ZMod 2) (original_representation '' contracted)).mkQ
      (original_representation firstPartner) = _
    rw [first_add, map_add]
    rfl
  have second_contracted_add : representation secondPartner =
      representation pivot + representation second := by
    change (span (ZMod 2) (original_representation '' contracted)).mkQ
      (original_representation secondPartner) = _
    rw [second_add, map_add]
    rfl
  have connector := representation.binary_contract_triangle_connector final_triangle
    first_second third_first.symm third_second.symm
  let basisLabels : Fin 3 → Label := ![pivot, first, second]
  let labels : Fin 6 → Label := ![pivot, first, second, firstPartner, secondPartner, third]
  have distinct := Simple.isCircuit_triple_distinct first_triangle
  have other_distinct := Simple.isCircuit_triple_distinct second_triangle
  have basis_injective : Function.Injective basisLabels := by
    intro first_index second_index equality
    fin_cases first_index <;> fin_cases second_index <;>
      simp_all [basisLabels]
  have basis_range : Set.range basisLabels = {pivot, first, second} := by
    ext element
    simp [basisLabels, Matrix.range_cons]
    tauto
  have basis_independent : LinearIndependent (ZMod 2) (representation ∘ basisLabels) :=
    LinearIndependent.of_linearIndepOn_range basis_injective representation
      (by rw [basis_range]; exact representation.onIndep final_independent)
  have ground : ∀ index, labels index ∈ (source.contract contracted).E := by
    intro index
    fin_cases index <;>
      simp only [labels, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk, contract_ground, Set.mem_sdiff] <;>
      aesop (add safe (by exact first_triangle.subset_ground (by simp : pivot ∈ _)))
        (add safe (by exact first_triangle.subset_ground (by simp : first ∈ _)))
        (add safe (by exact first_triangle.subset_ground (by simp : firstPartner ∈ _)))
        (add safe (by exact second_triangle.subset_ground (by simp : second ∈ _)))
        (add safe (by exact second_triangle.subset_ground (by simp : secondPartner ∈ _)))
  have certificate : ∃ twisted : Bool, ∀ index, representation (labels index) =
      Fintype.linearCombination (ZMod 2) (representation ∘ basisLabels)
        (binaryConnectorCoefficients twisted index) := by
    rcases connector with connector | connector
    · refine ⟨false, ?_⟩
      intro index
      fin_cases index <;>
        simp [labels, basisLabels, binaryConnectorCoefficients, Fintype.linearCombination_apply,
          Fin.sum_univ_succ, first_contracted_add, second_contracted_add, connector]
    · refine ⟨true, ?_⟩
      intro index
      fin_cases index <;>
        simp [labels, basisLabels, binaryConnectorCoefficients, Fintype.linearCombination_apply,
          Fin.sum_univ_succ, first_contracted_add, second_contracted_add, connector, add_assoc]
  obtain ⟨twisted, equations⟩ := certificate
  obtain ⟨candidate, minor, isomorphism⟩ :=
    representation.binary_connector_certificate_has_graph_k4_minor basisLabels labels twisted
      basis_independent ground equations
  refine ⟨candidate, minor.trans ?_, isomorphism⟩
  simpa using source.contract_delete_isMinor contracted ∅

theorem ConnectedTriangleTriadProfile.dual
    (profile : ConnectedTriangleTriadProfile source) :
    ConnectedTriangleTriadProfile source✶ := by
  intro removed member
  constructor
  · intro contracted basepoint basepoint_member
    have deleted : (source.delete {removed}).Connected := by
      apply connected_dual_iff.mp
      rw [dual_delete]
      exact contracted
    exact (profile removed member).2 deleted basepoint basepoint_member
  · intro deleted basepoint basepoint_member
    have contracted : (source.contract {removed}).Connected := by
      apply connected_dual_iff.mp
      rw [dual_contract]
      exact deleted
    obtain ⟨first, first_member, second, second_member, distinct,
      first_avoids, second_avoids, triangle⟩ :=
      (profile removed member).1 contracted basepoint basepoint_member
    exact ⟨first, first_member, second, second_member, distinct, first_avoids,
      second_avoids, triangle.isCocircuit⟩

theorem ConnectedTriangleTriadProfile.has_graph_k4_minor_of_connected_contract
    [source.Simple] (binary : source.Representable (ZMod 2))
    (profile : ConnectedTriangleTriadProfile source)
    (pivot_member : pivot ∈ source.E) (connected : (source.contract {pivot}).Connected) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
  obtain ⟨first, _, firstPartner, _, second, _, secondPartner, _, _, _,
    second_first, second_firstPartner, first_secondPartner, _, independent,
    first_triangle, second_triangle⟩ :=
    profile.independent_two_triangles_of_connected_contract binary pivot_member connected
  exact binary_two_triangles_connected_contract_has_graph_k4_minor binary first_triangle
    second_triangle independent connected second_first.symm second_firstPartner
    first_secondPartner.symm

theorem ConnectedTriangleTriadProfile.has_graph_k4_minor
    [source.Finite] [source.Simple] [source✶.Simple] (binary : source.Representable (ZMod 2))
    (connected : source.Connected) (nontrivial : source.E.Nontrivial)
    (profile : ConnectedTriangleTriadProfile source) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
  classical
  obtain ⟨pivot, pivot_member⟩ := nontrivial.nonempty
  rcases connected.delete_or_contract nontrivial pivot with deleted | contracted
  · have dual_contracted : (source✶.contract {pivot}).Connected := by
      rw [← dual_delete]
      exact deleted.to_dual
    by_contra excluded
    exact ((BondalThomsen.graph_k4_excluded_dual_iff source).mpr excluded)
      (profile.dual.has_graph_k4_minor_of_connected_contract
        binary.dual pivot_member dual_contracted)
  · exact profile.has_graph_k4_minor_of_connected_contract binary pivot_member contracted

theorem binaryConnectedTriangleTriadK4MinorLemma_proved :
    BinaryConnectedTriangleTriadK4MinorLemma Label := by
  intro candidate finite_candidate connected binary simple cosimple _rank _corank size profile
  let : candidate.Finite := finite_candidate
  let : candidate.Simple := simple
  let : candidate✶.Simple := cosimple
  have nontrivial : candidate.E.Nontrivial :=
    (Set.one_lt_ncard_iff_nontrivial_and_finite.mp (by omega : 1 < candidate.E.ncard)).1
  exact profile.has_graph_k4_minor binary connected nontrivial

end Matroid
