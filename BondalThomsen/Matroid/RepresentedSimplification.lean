module

public import BondalThomsen.Fan.ParallelIndependence
public import BondalThomsen.Ports.Matroid.MinorPresentation

@[expose] public section

namespace Matroid

open Set Submodule

variable {Label OtherLabel Field Vector : Type*} [_root_.Field Field]
    [AddCommGroup Vector] [Module Field Vector] {matroid : Matroid Label}

def Rep.nonzeroLines (representation : matroid.Rep Field Vector) : Set (Submodule Field Vector) :=
  {line | ∃ element, representation element ≠ 0 ∧ span Field {representation element} = line}

theorem Rep.isSimplification_restrict_range (representation : matroid.Rep Field Vector)
    (representative : representation.nonzeroLines → Label)
    (representative_nonzero : ∀ line, representation (representative line) ≠ 0)
    (representative_line : ∀ line,
      span Field {representation (representative line)} = line.val) :
    (matroid.restrict (Set.range representative)).IsSimplification matroid := by
  classical
  let ground := Set.range representative
  have subset_ground : ground ⊆ matroid.E := by
    rintro element ⟨line, rfl⟩
    exact ((representation.ne_zero_iff_isNonloop _).mp (representative_nonzero line)).mem_ground
  refine ⟨?_, matroid.restrict_isRestriction ground subset_ground, ?_⟩
  · apply loopless_iff_forall_isNonloop.mpr
    intro element member
    change element ∈ ground at member
    obtain ⟨line, rfl⟩ := member
    rw [restrict_isNonloop_iff]
    exact ⟨(representation.ne_zero_iff_isNonloop _).mp (representative_nonzero line), ⟨line, rfl⟩⟩
  · intro element nonloop
    have nonzero := (representation.ne_zero_iff_isNonloop element).mpr nonloop
    let line : representation.nonzeroLines :=
      ⟨span Field {representation element}, element, nonzero, rfl⟩
    refine ⟨representative line, ⟨⟨line, rfl⟩, ?_⟩, ?_⟩
    · rw [representation.parallel_iff_span_eq]
      exact ⟨nonzero, representative_nonzero line, (representative_line line).symm⟩
    · intro other properties
      obtain ⟨other_line, other_eq⟩ := properties.1
      have same_span := (representation.parallel_iff_span_eq element other).mp properties.2
      have same_line : other_line = line := by
        apply Subtype.ext
        rw [← representative_line other_line, other_eq, ← same_span.2.2]
      rw [← other_eq, same_line]

theorem Rep.exists_isSimplification (representation : matroid.Rep Field Vector) :
    ∃ smaller : Matroid Label, smaller.IsSimplification matroid := by
  let representative := fun line : representation.nonzeroLines => line.property.choose
  exact ⟨matroid.restrict (Set.range representative), representation.isSimplification_restrict_range
    representative (fun line => line.property.choose_spec.1)
    (fun line => line.property.choose_spec.2)⟩

theorem Rep.exists_isSimplification_of_simple_restriction
    (representation : matroid.Rep Field Vector) {smaller : Matroid Label}
    (simple : smaller.Simple) (restriction : smaller.IsRestriction matroid) :
    ∃ simplified : Matroid Label,
      simplified.IsSimplification matroid ∧ smaller.IsRestriction simplified := by
  classical
  have simple_nonzero : ∀ element ∈ smaller.E, representation element ≠ 0 := by
    intro element member
    have nonloop : smaller.IsNonloop element :=
      ((@Simple.parallel_iff_eq _ smaller simple element element member).mpr rfl).1
    exact (representation.ne_zero_iff_isNonloop element).mpr (nonloop.of_isRestriction restriction)
  let meets := fun line : representation.nonzeroLines =>
    ∃ element, element ∈ smaller.E ∧ span Field {representation element} = line.val
  let representative := fun line : representation.nonzeroLines =>
    if meeting : meets line then meeting.choose else line.property.choose
  have representative_nonzero : ∀ line, representation (representative line) ≠ 0 := by
    intro line
    by_cases meeting : meets line
    · simpa only [representative, dite_eq_left meeting] using
        simple_nonzero meeting.choose meeting.choose_spec.1
    · simpa only [representative, dite_eq_right meeting] using line.property.choose_spec.1
  have representative_line : ∀ line,
      span Field {representation (representative line)} = line.val := by
    intro line
    by_cases meeting : meets line
    · simpa only [representative, dite_eq_left meeting] using meeting.choose_spec.2
    · simpa only [representative, dite_eq_right meeting] using line.property.choose_spec.2
  have included : smaller.E ⊆ Set.range representative := by
    intro element member
    let line : representation.nonzeroLines :=
      ⟨span Field {representation element}, element, simple_nonzero element member, rfl⟩
    have meeting : meets line := ⟨element, member, rfl⟩
    refine ⟨line, ?_⟩
    have representative_member : representative line ∈ smaller.E := by
      simpa only [representative, dite_eq_left meeting] using meeting.choose_spec.1
    have parallel : matroid.Parallel (representative line) element := by
      rw [representation.parallel_iff_span_eq]
      exact ⟨representative_nonzero line, simple_nonzero element member, representative_line line⟩
    have in_restriction : smaller.Parallel (representative line) element := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← restriction.eq_restrict, restrict_isNonloop_iff]
        exact ⟨parallel.1, representative_member⟩
      · rw [← restriction.eq_restrict, restrict_isNonloop_iff]
        exact ⟨parallel.2.1, member⟩
      · rw [← restriction.eq_restrict,
          matroid.restrict_closure_eq (Set.singleton_subset_iff.mpr representative_member)
            restriction.subset,
          matroid.restrict_closure_eq (Set.singleton_subset_iff.mpr member) restriction.subset,
          parallel.2.2]
    exact (@Simple.parallel_iff_eq _ smaller simple _ _ representative_member).mp in_restriction
  refine ⟨matroid.restrict (Set.range representative),
    representation.isSimplification_restrict_range representative representative_nonzero
      representative_line, ?_⟩
  rw [← restriction.eq_restrict]
  have nested := (matroid.restrict (Set.range representative)).restrict_isRestriction
    smaller.E included
  rwa [matroid.restrict_restrict_eq included] at nested

theorem Rep.exists_isMinor_isSimplification (representation : matroid.Rep Field Vector)
    {smaller : Matroid Label} (minor : smaller ≤m matroid) (simple : smaller.Simple) :
    ∃ simplified : Matroid Label,
      smaller ≤m simplified ∧ simplified.IsSimplification matroid := by
  obtain ⟨contracted, independent, restriction, _⟩ :=
    minor.exists_spanning_isRestriction_contract
  have smaller_eq : (matroid.restrict (smaller.E ∪ contracted)).contract contracted = smaller := by
    rw [← matroid.contract_restrict_eq_restrict_contract
      (Set.subset_sdiff.mp restriction.subset).2.symm, restriction.eq_restrict]
  have simple_restriction : (matroid.restrict (smaller.E ∪ contracted)).Simple := by
    apply Indep.simple_of_contract_simple (contracted := contracted)
    · exact restrict_indep_iff.mpr ⟨independent, Set.subset_union_right⟩
    · rwa [smaller_eq]
  obtain ⟨simplified, simplification, extended⟩ :=
    representation.exists_isSimplification_of_simple_restriction simple_restriction
      (matroid.restrict_isRestriction _ (Set.union_subset minor.subset independent.subset_ground))
  refine ⟨simplified, IsMinor.trans ?_ extended.isMinor, simplification⟩
  have contracted_minor := contract_isMinor (matroid.restrict (smaller.E ∪ contracted)) contracted
  rwa [smaller_eq] at contracted_minor

theorem Rep.nonzero_of_mem_simplification (representation : matroid.Rep Field Vector)
    {smaller : Matroid Label} (simplification : smaller.IsSimplification matroid)
    {element : Label} (member : element ∈ smaller.E) : representation element ≠ 0 := by
  have := simplification.1
  exact (representation.ne_zero_iff_isNonloop element).mpr
    ((smaller.isNonloop_of_loopless member).of_isRestriction simplification.2.1)

noncomputable def Rep.simplificationLineEquiv (representation : matroid.Rep Field Vector)
    {smaller : Matroid Label} (simplification : smaller.IsSimplification matroid) :
    smaller.E ≃ representation.nonzeroLines := by
  let to_line := fun element : smaller.E =>
    (⟨span Field {representation element.val}, element.val,
      representation.nonzero_of_mem_simplification simplification element.property, rfl⟩ :
        representation.nonzeroLines)
  apply Equiv.ofBijective to_line
  constructor
  · intro first second equality
    apply Subtype.ext
    apply simplification.eq_of_parallel first.property second.property
    rw [representation.parallel_iff_span_eq]
    exact ⟨representation.nonzero_of_mem_simplification simplification first.property,
      representation.nonzero_of_mem_simplification simplification second.property,
      congrArg Subtype.val equality⟩
  · intro line
    obtain ⟨element, nonzero, equality⟩ := line.property
    obtain ⟨representative, ⟨member, parallel⟩, _⟩ := simplification.exists_unique
      ((representation.ne_zero_iff_isNonloop element).mp nonzero)
    refine ⟨⟨representative, member⟩, ?_⟩
    apply Subtype.ext
    exact ((representation.parallel_iff_span_eq element representative).mp parallel).2.2.symm.trans
      equality

noncomputable def Rep.simplificationIso {other_matroid : Matroid OtherLabel}
    (representation : matroid.Rep Field Vector)
    (other_representation : other_matroid.Rep Field Vector)
    {smaller : Matroid Label} {other_smaller : Matroid OtherLabel}
    (simplification : smaller.IsSimplification matroid)
    (other_simplification : other_smaller.IsSimplification other_matroid)
    (same_lines : representation.nonzeroLines = other_representation.nonzeroLines) :
    Iso smaller other_smaller := by
  let matching := (representation.simplificationLineEquiv simplification).trans
    ((Set.equivOfEq same_lines).trans
      (other_representation.simplificationLineEquiv other_simplification).symm)
  have same_spans : ∀ element : smaller.E,
      span Field {representation element.val} =
        span Field {other_representation (matching element).val} := by
    intro element
    have equal_lines : other_representation.simplificationLineEquiv other_simplification
        (matching element) = Set.equivOfEq same_lines
          (representation.simplificationLineEquiv simplification element) := by
      simp only [matching, Equiv.trans_apply, Equiv.apply_symm_apply]
    have equal_spans := congrArg Subtype.val equal_lines
    change span Field {other_representation (matching element).val} =
      span Field {representation element.val} at equal_spans
    exact equal_spans.symm
  refine ⟨matching, ?_⟩
  intro selected
  rw [simplification.2.1.indep_iff, other_simplification.2.1.indep_iff,
    representation.indep_iff, other_representation.indep_iff]
  have selected_subset : Subtype.val '' selected ⊆ smaller.E := by
    rintro _ ⟨element, _, rfl⟩
    exact element.property
  have other_subset : Subtype.val '' (matching '' selected) ⊆ other_smaller.E := by
    rintro _ ⟨element, _, rfl⟩
    exact element.property
  rw [and_iff_left selected_subset, and_iff_left other_subset]
  have first_independence : LinearIndepOn Field representation (Subtype.val '' selected) ↔
      LinearIndepOn Field (fun element : smaller.E => representation element.val) selected := by
    exact ⟨fun independent => independent.comp_of_image Subtype.val_injective.injOn,
      fun independent => independent.image_of_comp Subtype.val representation⟩
  have second_independence :
      LinearIndepOn Field other_representation (Subtype.val '' (matching '' selected)) ↔
        LinearIndepOn Field (fun element : smaller.E =>
          other_representation (matching element).val) selected := by
    rw [Set.image_image]
    let mapped := fun element : smaller.E => (matching element).val
    have injective : Function.Injective mapped :=
      Subtype.val_injective.comp matching.injective
    exact ⟨fun independent => independent.comp_of_image injective.injOn,
      fun independent => independent.image_of_comp mapped other_representation⟩
  rw [first_independence, second_independence]
  exact BondalThomsen.linearIndepOn_iff_of_span_eq _ _ selected
    (fun element _ => other_representation.nonzero_of_mem_simplification other_simplification
      (matching element).property) (fun element _ => same_spans element)

end Matroid
