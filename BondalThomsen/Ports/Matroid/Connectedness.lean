module

public import BondalThomsen.Matroid.Binary.MarkedLeafReduction
public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Combinatorics.Matroid.Sum

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {first second third : Label}

theorem connectedTo_self (member : first ∈ source.E) : source.ConnectedTo first first :=
  Or.inl ⟨rfl, member⟩

theorem ConnectedTo.symm (connected : source.ConnectedTo first second) :
    source.ConnectedTo second first := by
  rcases connected with ⟨same, member⟩ | ⟨circuit, property, first_member, second_member⟩
  · exact Or.inl ⟨same.symm, same ▸ member⟩
  · exact Or.inr ⟨circuit, property, second_member, first_member⟩

theorem ConnectedTo.mem_ground_left (connected : source.ConnectedTo first second) :
    first ∈ source.E := by
  rcases connected with ⟨_, member⟩ | ⟨circuit, property, member, _⟩
  · exact member
  · exact property.subset_ground member

theorem ConnectedTo.mem_ground_right (connected : source.ConnectedTo first second) :
    second ∈ source.E := connected.symm.mem_ground_left

theorem IsCircuit.mem_connectedTo_mem {circuit : Set Label} (property : source.IsCircuit circuit)
    (first_member : first ∈ circuit) (second_member : second ∈ circuit) :
    source.ConnectedTo first second := Or.inr ⟨circuit, property, first_member, second_member⟩

theorem IsCocircuit.mem_connectedTo_mem {cocircuit : Set Label}
    (property : source.IsCocircuit cocircuit)
    (first_member : first ∈ cocircuit) (second_member : second ∈ cocircuit) :
    source.ConnectedTo first second := by
  simpa only [dual_dual] using
    (property.isCircuit.mem_connectedTo_mem first_member second_member).to_dual

theorem ConnectedTo.of_delete {deleted : Set Label}
    (connected : (source.delete deleted).ConnectedTo first second) :
    source.ConnectedTo first second := by
  rcases connected with ⟨same, member⟩ | ⟨circuit, property, first_member, second_member⟩
  · exact Or.inl ⟨same, delete_subset_ground source deleted member⟩
  · exact property.of_delete.mem_connectedTo_mem first_member second_member

theorem IsCocircuit.insert_compl_spanning {cocircuit : Set Label}
    (property : source.IsCocircuit cocircuit) (member : first ∈ cocircuit) :
    source.Spanning (insert first (source.E \ cocircuit)) := by
  have minimal := isCocircuit_iff_minimal_compl_nonspanning.mp property
  have spanning : source.Spanning (source.E \ (cocircuit \ {first})) := by
    by_contra nonspanning
    exact (sdiff_singleton_ssubset.mpr member).ne
      (minimal.eq_of_subset nonspanning Set.sdiff_subset)
  convert spanning using 1
  classical
  ext element
  have ground := property.subset_ground member
  by_cases same : element = first
  · subst element
    simp [ground]
  · simp [same]

theorem IsCocircuit.notMem_closure_compl {cocircuit : Set Label}
    (property : source.IsCocircuit cocircuit) (member : first ∈ cocircuit) :
    first ∉ source.closure (source.E \ cocircuit) := by
  intro in_closure
  have spanning := property.insert_compl_spanning member
  have nonspanning := (isCocircuit_iff_minimal_compl_nonspanning.mp property).prop
  apply nonspanning
  rw [spanning_iff_closure_eq Set.sdiff_subset]
  rw [← source.closure_insert_eq_of_mem_closure in_closure]
  exact spanning.closure_eq

theorem IsCocircuit.insert_isBase_of_basis_compl {cocircuit basisSet : Set Label}
    (property : source.IsCocircuit cocircuit)
    (basis : source.IsBasis basisSet (source.E \ cocircuit)) (member : first ∈ cocircuit) :
    source.IsBase (insert first basisSet) := by
  have outside : first ∉ source.closure basisSet := by
    rw [basis.closure_eq_closure]
    exact property.notMem_closure_compl member
  have independent := (basis.indep.notMem_closure_iff (property.subset_ground member)).mp outside
  apply independent.1.isBase_of_spanning
  rw [spanning_iff_closure_eq (Set.insert_subset (property.subset_ground member) basis.indep.subset_ground)]
  rw [source.closure_insert_congr_right basis.closure_eq_closure]
  exact (property.insert_compl_spanning member).closure_eq

private theorem connectedTo_of_all_insert_bases {independentSet : Set Label}
    (insert_base : ∀ element ∈ source.E \ independentSet,
      source.IsBase (insert element independentSet))
    (outside : first ∈ source.E \ independentSet) (inside : second ∈ independentSet)
    (not_coloop : ¬ source.IsColoop second) : source.ConnectedTo first second := by
  have base := insert_base first outside
  have not_forall := (base.isColoop_iff_forall_notMem_fundCircuit (Or.inr inside)).not.mp not_coloop
  push Not at not_forall
  obtain ⟨other, other_member, second_circuit⟩ := not_forall
  have circuit := base.fundCircuit_isCircuit other_member.1 other_member.2
  apply circuit.mem_connectedTo_mem _ second_circuit
  by_contra first_absent
  have subset : source.fundCircuit other (insert first independentSet) ⊆
      insert other independentSet := by
    intro element member
    have := source.fundCircuit_subset_insert other (insert first independentSet) member
    rcases this with rfl | same | original
    · exact Or.inl rfl
    · exact (first_absent (same ▸ member)).elim
    · exact Or.inr original
  have other_outside : other ∈ source.E \ independentSet :=
    ⟨other_member.1, fun member => other_member.2 (Or.inr member)⟩
  exact circuit.not_indep ((insert_base other other_outside).indep.subset subset)

theorem ConnectedTo.trans (first_connected : source.ConnectedTo first second)
    (second_connected : source.ConnectedTo second third) : source.ConnectedTo first third := by
  classical
  by_cases same : first = third
  · exact Or.inl ⟨same, first_connected.mem_ground_left⟩
  by_cases first_same : first = second
  · exact first_same ▸ second_connected
  by_cases second_same : second = third
  · exact second_same ▸ first_connected
  obtain ⟨cocircuit, cocircuit_property, first_cocircuit, second_cocircuit⟩ :=
    first_connected.to_dual.exists_isCircuit_of_ne first_same
  have cocircuit_property : source.IsCocircuit cocircuit := cocircuit_property
  obtain ⟨circuit, circuit_property, second_circuit, third_circuit⟩ :=
    second_connected.exists_isCircuit_of_ne second_same
  by_cases third_cocircuit : third ∈ cocircuit
  · exact cocircuit_property.mem_connectedTo_mem first_cocircuit third_cocircuit
  have independent : source.Indep (circuit \ cocircuit) :=
    (circuit_property.sdiff_singleton_indep second_circuit).subset
      (fun element member => ⟨member.1, fun equality =>
        member.2 (equality ▸ second_cocircuit)⟩)
  obtain ⟨basisSet, basis, circuit_part_subset⟩ := independent.subset_isBasis_of_subset
    (Set.sdiff_subset_sdiff_left circuit_property.subset_ground) Set.sdiff_subset
  let deleted := (source.E \ cocircuit) \ basisSet
  have first_not_basis : first ∉ basisSet :=
    fun member => (basis.subset member).2 first_cocircuit
  have first_not_deleted : first ∉ deleted :=
    fun member => member.1.2 first_cocircuit
  have third_basis : third ∈ basisSet := circuit_part_subset ⟨third_circuit, third_cocircuit⟩
  have circuit_disjoint : Disjoint circuit deleted := by
    apply Set.disjoint_left.mpr
    intro element circuit_member deleted_member
    exact deleted_member.2 (circuit_part_subset ⟨circuit_member, deleted_member.1.2⟩)
  have deleted_circuit : (source.delete deleted).IsCircuit circuit :=
    delete_isCircuit_iff.mpr ⟨circuit_property, circuit_disjoint⟩
  apply ConnectedTo.of_delete (deleted := deleted)
  apply connectedTo_of_all_insert_bases
    (independentSet := basisSet) _
    (show first ∈ (source.delete deleted).E \ basisSet from
      ⟨⟨first_connected.mem_ground_left, first_not_deleted⟩, first_not_basis⟩)
    third_basis (deleted_circuit.not_isColoop_of_mem third_circuit)
  intro element member
  have element_cocircuit : element ∈ cocircuit := by
    by_contra absent
    exact member.1.2 ⟨⟨member.1.1, absent⟩, member.2⟩
  have source_base := cocircuit_property.insert_isBase_of_basis_compl basis element_cocircuit
  have disjoint : Disjoint (insert element basisSet) deleted := by
    apply Set.disjoint_left.mpr
    intro other other_member deleted_member
    rcases other_member with rfl | basis_member
    · exact deleted_member.1.2 element_cocircuit
    · exact deleted_member.2 basis_member
  have deleted_independent : (source.delete deleted).Indep (insert element basisSet) :=
    delete_indep_iff.mpr ⟨source_base.indep, disjoint⟩
  apply deleted_independent.isBase_of_spanning
  rw [spanning_iff_closure_eq deleted_independent.subset_ground,
    source.delete_closure_eq_of_disjoint disjoint, source_base.closure_eq, delete_ground]

end Matroid
