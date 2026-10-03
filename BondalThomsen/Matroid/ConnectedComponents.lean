module

public import BondalThomsen.Ports.Matroid.Connectedness
public import Mathlib.Data.Set.Card

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} (source : Matroid Label)

def connectedComponentSet (element : source.E) : Set Label :=
  {other | source.ConnectedTo element.val other}

theorem connectedComponentSet_subset_ground (element : source.E) :
    source.connectedComponentSet element ⊆ source.E := fun _ related => related.mem_ground_right

theorem connectedComponentSet_nonempty (element : source.E) :
    (source.connectedComponentSet element).Nonempty :=
  ⟨element.val, connectedTo_self element.property⟩

theorem connectedComponentSet_eq_of_mem {element : source.E} {other : Label}
    (related : other ∈ source.connectedComponentSet element) :
    source.connectedComponentSet ⟨other, related.mem_ground_right⟩ =
      source.connectedComponentSet element := by
  ext label
  exact ⟨fun next => related.trans next, fun next => related.symm.trans next⟩

theorem connectedComponentSet_disjoint_of_ne {first second : source.E}
    (distinct : source.connectedComponentSet first ≠ source.connectedComponentSet second) :
    Disjoint (source.connectedComponentSet first) (source.connectedComponentSet second) := by
  apply Set.disjoint_left.mpr
  intro shared first_member second_member
  exact distinct ((source.connectedComponentSet_eq_of_mem first_member).symm.trans
    (source.connectedComponentSet_eq_of_mem second_member))

theorem IsCircuit.subset_connectedComponentSet {element : source.E} {circuit : Set Label}
    (property : source.IsCircuit circuit) {member : Label}
    (circuit_member : member ∈ circuit) (component_member : member ∈ source.connectedComponentSet element) :
    circuit ⊆ source.connectedComponentSet element :=
  fun _ other_member => component_member.trans
    (property.mem_connectedTo_mem circuit_member other_member)

theorem connectedComponentSet_restrict_connected (element : source.E) :
    (source.restrict (source.connectedComponentSet element)).Connected := by
  refine ⟨⟨source.connectedComponentSet_nonempty element⟩, ?_⟩
  intro first second first_member second_member
  have related : source.ConnectedTo first second := first_member.symm.trans second_member
  by_cases same : first = second
  · exact Or.inl ⟨same, first_member⟩
  obtain ⟨circuit, property, first_circuit, second_circuit⟩ := related.exists_isCircuit_of_ne same
  exact Or.inr ⟨circuit, (restrict_isCircuit_iff
    (source.connectedComponentSet_subset_ground element)).mpr
      ⟨property, property.subset_connectedComponentSet source first_circuit first_member⟩,
    first_circuit, second_circuit⟩

def ConnectedComponent := Set.range source.connectedComponentSet

def componentMatroid (component : source.ConnectedComponent) : Matroid Label :=
  source.restrict component.val

theorem component_subset_ground (component : source.ConnectedComponent) :
    component.val ⊆ source.E := by
  obtain ⟨element, equality⟩ := component.property
  rw [← equality]
  exact source.connectedComponentSet_subset_ground element

theorem componentMatroid_ground (component : source.ConnectedComponent) :
    (source.componentMatroid component).E = component.val := rfl

theorem componentMatroid_connected (component : source.ConnectedComponent) :
    (source.componentMatroid component).Connected := by
  obtain ⟨element, equality⟩ := component.property
  change (source.restrict component.val).Connected
  rw [← equality]
  exact source.connectedComponentSet_restrict_connected element

theorem componentMatroid_pairwise_disjoint :
    Pairwise (fun first second : source.ConnectedComponent =>
      Disjoint (source.componentMatroid first).E (source.componentMatroid second).E) := by
  intro first second distinct
  obtain ⟨first_element, first_eq⟩ := first.property
  obtain ⟨second_element, second_eq⟩ := second.property
  change Disjoint first.val second.val
  rw [← first_eq, ← second_eq]
  apply source.connectedComponentSet_disjoint_of_ne
  intro equality
  exact distinct (Subtype.ext (first_eq.symm.trans (equality.trans second_eq)))

theorem componentMatroid_iUnion_ground :
    (⋃ component : source.ConnectedComponent, (source.componentMatroid component).E) = source.E := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun component => source.component_subset_ground component
  · intro element member
    exact Set.mem_iUnion.mpr ⟨⟨source.connectedComponentSet ⟨element, member⟩,
      ⟨⟨element, member⟩, rfl⟩⟩, connectedTo_self member⟩

theorem eq_componentMatroid_disjointSigma :
    source = Matroid.disjointSigma source.componentMatroid source.componentMatroid_pairwise_disjoint := by
  apply Matroid.ext_indep
  · rw [disjointSigma_ground_eq, source.componentMatroid_iUnion_ground]
  intro selected selected_subset
  rw [disjointSigma_indep_iff, source.componentMatroid_iUnion_ground,
    and_iff_left selected_subset]
  constructor
  · intro independent component
    change (source.restrict component.val).Indep (selected ∩ component.val)
    rw [restrict_indep_iff]
    exact ⟨independent.subset Set.inter_subset_left, Set.inter_subset_right⟩
  · intro component_independent
    apply (indep_iff_forall_subset_not_isCircuit selected_subset).mpr
    intro circuit circuit_subset property
    obtain ⟨element, circuit_member⟩ := property.nonempty
    let ground_element : source.E := ⟨element, property.subset_ground circuit_member⟩
    let component : source.ConnectedComponent :=
      ⟨source.connectedComponentSet ground_element, ⟨ground_element, rfl⟩⟩
    have component_subset : circuit ⊆ component.val :=
      property.subset_connectedComponentSet source circuit_member (connectedTo_self ground_element.property)
    have independent := (restrict_indep_iff.mp (component_independent component)).1
    exact property.not_indep (independent.subset (Set.subset_inter circuit_subset component_subset))

instance componentMatroid_finite [source.Finite] (component : source.ConnectedComponent) :
    (source.componentMatroid component).Finite :=
  ⟨source.ground_finite.subset (source.component_subset_ground component)⟩

instance connectedComponent_finite [source.Finite] : Finite source.ConnectedComponent := by
  let : Finite source.E := source.ground_finite.to_subtype
  exact Finite.of_surjective
    (fun element : source.E => (⟨source.connectedComponentSet element, ⟨element, rfl⟩⟩ :
      source.ConnectedComponent)) (fun component => by
        obtain ⟨element, equality⟩ := component.property
        exact ⟨element, Subtype.ext equality⟩)

end Matroid
