module

public import BondalThomsen.Matroid.Binary.EightElementObstruction
public import BondalThomsen.Matroid.Binary.SixElementCoverage
public import BondalThomsen.Matroid.RestrictionContraction
public import BondalThomsen.Matroid.DualRepresentation
public import BondalThomsen.Matroid.RepresentedSimplification

@[expose] public section

namespace BondalThomsen

open Set Submodule Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem binaryFourQuotient_zero_iff :
    ∀ (pivot : Fin 4 → ZMod 2) (coordinate : Fin 4), pivot coordinate = 1 →
      ∀ vector : Fin 4 → ZMod 2,
        binaryFourQuotient pivot coordinate vector = 0 ↔ vector = 0 ∨ vector = pivot := by
  decide +kernel

theorem binaryFourQuotient_ker {pivot : Fin 4 → ZMod 2} {coordinate : Fin 4}
    (pivot_one : pivot coordinate = 1) :
    (binaryFourQuotient pivot coordinate).ker = span (ZMod 2) {pivot} := by
  ext vector
  rw [LinearMap.mem_ker, binaryFourQuotient_zero_iff pivot coordinate pivot_one,
    mem_span_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rintro ⟨scalar, rfl⟩
    have scalar_cases : scalar = 0 ∨ scalar = 1 := by
      fin_cases scalar <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases scalar_cases with rfl | rfl <;> simp

theorem binaryFourQuotient_ne_zero {pivot vector : Fin 4 → ZMod 2} {coordinate : Fin 4}
    (pivot_one : pivot coordinate = 1) (nonzero : vector ≠ 0) (not_pivot : vector ≠ pivot) :
    binaryFourQuotient pivot coordinate vector ≠ 0 := by
  intro zero
  rcases (binaryFourQuotient_zero_iff pivot coordinate pivot_one vector).mp zero with
    zero | same
  · exact nonzero zero
  · exact not_pivot same

end BondalThomsen

namespace Matroid

open Set Submodule BondalThomsen

variable {Label : Type*} {source : Matroid Label} {element : Label} {coordinate : Fin 4}

noncomputable def Rep.binaryFourContract
    (representation : source.Rep (ZMod 2) (Fin 4 → ZMod 2))
    (pivot_one : representation element coordinate = 1) :
    (source.contract {element}).Rep (ZMod 2) (Fin 3 → ZMod 2) := by
  let quotient := binaryFourQuotient (representation element) coordinate
  let pivot_span : Submodule (ZMod 2) (Fin 4 → ZMod 2) :=
    span (ZMod 2) (representation '' {element})
  have kernel : quotient.ker = pivot_span := by
    simpa only [pivot_span, image_singleton] using binaryFourQuotient_ker pivot_one
  let descended := pivot_span.liftQ quotient kernel.ge
  exact (representation.contract {element}).comp' descended
    (pivot_span.ker_liftQ_eq_bot quotient kernel.ge kernel.le)

theorem Rep.binaryFourContract_apply
    (representation : source.Rep (ZMod 2) (Fin 4 → ZMod 2))
    (pivot_one : representation element coordinate = 1) (label : Label) :
    representation.binaryFourContract pivot_one label =
      binaryFourQuotient (representation element) coordinate (representation label) := by
  rfl

theorem Rep.binary_restrict_simple_of_nonzero_injOn
    (representation : source.Rep (ZMod 2) (Fin 3 → ZMod 2)) {selected : Set Label}
    (nonzero : ∀ label ∈ selected, representation label ≠ 0)
    (injective : Set.InjOn representation selected) : (source.restrict selected).Simple := by
  apply simple_iff_forall_pair_indep.mpr
  intro first second first_member second_member
  change first ∈ selected at first_member
  change second ∈ selected at second_member
  apply restrict_indep_iff.mpr
  refine ⟨representation.indep_iff.mpr ?_, pair_subset first_member second_member⟩
  by_cases distinct : first = second
  · subst second
    simpa using nonzero first first_member
  rw [linearIndepOn_pair_iff representation distinct (nonzero first first_member)]
  intro scalar equality
  have scalar_cases : scalar = 0 ∨ scalar = 1 := by
    fin_cases scalar <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases scalar_cases with rfl | rfl
  · exact nonzero second second_member (by simpa using equality.symm)
  · exact distinct (injective first_member second_member (by simpa using equality))

theorem Rep.exists_graph_k4_restriction_of_nonzero_image_card_ge_six
    (representation : source.Rep (ZMod 2) (Fin 3 → ZMod 2))
    (lower : 6 ≤ (representation '' source.E \ {0}).ncard) :
    ∃ selected ⊆ source.E, selected.ncard = 6 ∧ (source.restrict selected).Simple ∧
      Nonempty (Iso (source.restrict selected) k4GraphCycleMatroid) := by
  classical
  obtain ⟨chosen, chosen_subset, chosen_card⟩ := Set.exists_subset_card_eq lower
  have exists_label (vector : chosen) :
      ∃ label ∈ source.E, representation label = vector.val :=
    (chosen_subset vector.property).1
  let representative : chosen → Label := fun vector => (exists_label vector).choose
  have representative_member (vector : chosen) : representative vector ∈ source.E :=
    (exists_label vector).choose_spec.1
  have representative_value (vector : chosen) : representation (representative vector) = vector.val :=
    (exists_label vector).choose_spec.2
  let selected : Set Label := Set.range representative
  have subset : selected ⊆ source.E := by
    rintro label ⟨vector, rfl⟩
    exact representative_member vector
  have nonzero : ∀ label ∈ selected, representation label ≠ 0 := by
    rintro label ⟨vector, rfl⟩
    rw [representative_value]
    exact (chosen_subset vector.property).2
  have injective : Set.InjOn representation selected := by
    rintro first ⟨first_vector, rfl⟩ second ⟨second_vector, rfl⟩ equality
    have same : first_vector = second_vector := by
      apply Subtype.ext
      simpa only [representative_value] using equality
    exact congrArg representative same
  have representative_injective : Function.Injective representative := by
    intro first second equality
    apply Subtype.ext
    rw [← representative_value first, ← representative_value second, equality]
  have selected_card : selected.ncard = 6 := by
    change Nat.card (Set.range representative) = 6
    rw [Nat.card_range_of_injective representative_injective]
    exact chosen_card
  have simple := representation.binary_restrict_simple_of_nonzero_injOn nonzero injective
  let : (source.restrict selected).Simple := simple
  obtain ⟨isomorphism⟩ := (representation.restrict selected).six_binary_coordinates_iso_k4
    (by simpa only [restrict_ground_eq] using selected_card)
  exact ⟨selected, subset, selected_card, simple,
    ⟨isomorphism.trans k4Matroid_iso_graphCycleMatroid⟩⟩

theorem Rep.binaryFourContract_has_graph_k4_minor_of_image_card_ge_six
    (representation : source.Rep (ZMod 2) (Fin 4 → ZMod 2))
    (pivot_one : representation element coordinate = 1)
    (lower : 6 ≤ ((representation.binaryFourContract pivot_one) ''
      (source.contract {element}).E \ {0}).ncard) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso k4GraphCycleMatroid candidate) := by
  obtain ⟨selected, subset, cardinality, simple, ⟨isomorphism⟩⟩ :=
    (representation.binaryFourContract pivot_one).exists_graph_k4_restriction_of_nonzero_image_card_ge_six
      lower
  exact ⟨(source.contract {element}).restrict selected,
    ((source.contract {element}).restrict_isRestriction selected subset).isMinor.trans
      (contract_isMinor source {element}), ⟨isomorphism.symm⟩⟩

theorem Rep.binaryFourContract_nonzero_image_eq [source.Simple]
    (representation : source.Rep (ZMod 2) (Fin 4 → ZMod 2))
    (pivot_one : representation element coordinate = 1) (member : element ∈ source.E)
    {points : Finset (Fin 4 → ZMod 2)}
    (ground_image : representation '' source.E = (points : Set (Fin 4 → ZMod 2))) :
    (representation.binaryFourContract pivot_one) '' (source.contract {element}).E \ {0} =
      ((points.erase (representation element)).image
        (binaryFourQuotient (representation element) coordinate) : Finset (Fin 3 → ZMod 2)) := by
  classical
  have representation_injective : Set.InjOn representation source.E := by
    intro first first_member second second_member equality
    exact congrArg Subtype.val
      (representation.binaryPoint_injective (Subtype.ext equality) :
        (⟨first, first_member⟩ : source.E) = ⟨second, second_member⟩)
  ext vector
  constructor
  · rintro ⟨⟨label, label_member, rfl⟩, nonzero⟩
    have source_member : label ∈ source.E := label_member.1
    have label_distinct : label ≠ element := label_member.2
    apply Finset.mem_image.mpr
    refine ⟨representation label, Finset.mem_erase.mpr ⟨?_, ?_⟩, ?_⟩
    · exact fun equality => label_distinct (representation_injective source_member member equality)
    · have image_member : representation label ∈ representation '' source.E :=
        ⟨label, source_member, rfl⟩
      rwa [ground_image] at image_member
    · exact (representation.binaryFourContract_apply pivot_one label).symm
  · intro image_member
    obtain ⟨point, point_member, rfl⟩ := Finset.mem_image.mp image_member
    obtain ⟨point_distinct, point_member⟩ := Finset.mem_erase.mp point_member
    have image_member : point ∈ representation '' source.E := by
      rw [ground_image]
      exact point_member
    obtain ⟨label, label_member, rfl⟩ := image_member
    have label_distinct : label ≠ element := fun equality => point_distinct (congrArg representation equality)
    refine ⟨⟨label, ?_, (representation.binaryFourContract_apply pivot_one label)⟩, ?_⟩
    · exact ⟨label_member, label_distinct⟩
    · exact binaryFourQuotient_ne_zero pivot_one (representation.binaryPoint ⟨label, label_member⟩).property
        point_distinct

theorem Rep.has_graph_k4_minor_of_normalized_eight_binary_points [source.Simple]
    (representation : source.Rep (ZMod 2) (Fin 4 → ZMod 2))
    (selected : Finset (Fin 11)) (cardinality : selected.card = 4)
    (ground_image : representation '' source.E =
      (binaryFourNormalizedPoints selected : Set (Fin 4 → ZMod 2))) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso k4GraphCycleMatroid candidate) := by
  classical
  obtain ⟨pivot, pivot_member, coordinate, pivot_one, lower⟩ :=
    eight_normalized_binary_points_quotient_test selected cardinality
  have image_member : pivot ∈ representation '' source.E := by
    rw [ground_image]
    exact pivot_member
  obtain ⟨element, element_member, rfl⟩ := image_member
  apply representation.binaryFourContract_has_graph_k4_minor_of_image_card_ge_six pivot_one
  rw [representation.binaryFourContract_nonzero_image_eq pivot_one element_member ground_image]
  simpa only [Set.ncard_coe_finset] using lower

end Matroid
