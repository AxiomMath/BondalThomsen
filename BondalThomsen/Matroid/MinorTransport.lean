module

public import BondalThomsen.Ports.Matroid.Isomorphism

@[expose] public section

namespace Matroid

open Set

variable {Label OtherLabel : Type*} {matroid smaller : Matroid Label}
    {other : Matroid OtherLabel}

@[simp] theorem Iso.setImage_ground (isomorphism : Iso matroid other) :
    isomorphism.setImage matroid.E = other.E := by
  simp [Iso.setImage]

@[simp] theorem Iso.setImage_diff (isomorphism : Iso matroid other)
    (selected removed : Set Label) :
    isomorphism.setImage (selected \ removed) =
      isomorphism.setImage selected \ isomorphism.setImage removed := by
  simp only [Iso.setImage, Set.preimage_sdiff,
    Set.image_sdiff isomorphism.toEquiv.injective, Set.image_sdiff Subtype.val_injective]

theorem Iso.mem_setImage_iff (isomorphism : Iso matroid other)
    (selected : Set Label) (element : matroid.E) :
    (isomorphism.toEquiv element).val ∈ isomorphism.setImage selected ↔
      element.val ∈ selected := by
  constructor
  · rintro ⟨_, ⟨source, member, rfl⟩, equality⟩
    have same : isomorphism.toEquiv source = isomorphism.toEquiv element :=
      Subtype.ext equality
    exact isomorphism.toEquiv.injective same ▸ member
  · intro member
    exact ⟨isomorphism.toEquiv element, ⟨element, member, rfl⟩, rfl⟩

theorem Iso.disjoint_setImage_iff (isomorphism : Iso matroid other)
    {first second : Set Label} (first_subset : first ⊆ matroid.E)
    (second_subset : second ⊆ matroid.E) :
    Disjoint (isomorphism.setImage first) (isomorphism.setImage second) ↔
      Disjoint first second := by
  rw [Set.disjoint_left, Set.disjoint_left]
  constructor
  · intro disjoint element first_member second_member
    exact disjoint
      ((isomorphism.mem_setImage_iff first ⟨element, first_subset first_member⟩).mpr first_member)
      ((isomorphism.mem_setImage_iff second ⟨element, second_subset second_member⟩).mpr second_member)
  · intro disjoint element first_member second_member
    obtain ⟨_, ⟨source, source_member, rfl⟩, rfl⟩ := first_member
    exact disjoint source_member ((isomorphism.mem_setImage_iff second source).mp second_member)

noncomputable def Iso.contractGroundEquiv (isomorphism : Iso matroid other)
    (contracted : Set Label) :
    ↑(matroid.E \ contracted) ≃ ↑(other.E \ isomorphism.setImage contracted) :=
  (isomorphism.setEquiv (matroid.E \ contracted) Set.sdiff_subset).trans
    (Set.equivOfEq (by rw [isomorphism.setImage_diff, isomorphism.setImage_ground]))

@[simp] theorem Iso.contractGroundEquiv_apply (isomorphism : Iso matroid other)
    (contracted : Set Label) (element : ↑(matroid.E \ contracted)) :
    (isomorphism.contractGroundEquiv contracted element).val =
      (isomorphism.toEquiv ⟨element.val, element.property.1⟩).val := rfl

theorem Iso.contractGroundEquiv_image (isomorphism : Iso matroid other)
    (contracted : Set Label) (chosen : Set ↑(matroid.E \ contracted)) :
    Subtype.val '' (isomorphism.contractGroundEquiv contracted '' chosen) =
      isomorphism.setImage (Subtype.val '' chosen) := by
  ext element
  constructor
  · rintro ⟨_, ⟨source, member, rfl⟩, rfl⟩
    exact ⟨isomorphism.toEquiv ⟨source.val, source.property.1⟩,
      ⟨⟨source.val, source.property.1⟩, ⟨source, member, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨source, ⟨original, member, equality⟩, rfl⟩, rfl⟩
    refine ⟨isomorphism.contractGroundEquiv contracted original,
      ⟨original, member, rfl⟩, ?_⟩
    change (isomorphism.toEquiv ⟨original.val, original.property.1⟩).val =
      (isomorphism.toEquiv source).val
    have same : (⟨original.val, original.property.1⟩ : matroid.E) = source :=
      Subtype.ext equality
    rw [same]

noncomputable def Iso.contractIndep (isomorphism : Iso matroid other)
    {contracted : Set Label} (independent : matroid.Indep contracted) :
    Iso (matroid.contract contracted) (other.contract (isomorphism.setImage contracted)) where
  toEquiv := isomorphism.contractGroundEquiv contracted
  indep_image_iff' := by
    change ∀ chosen : Set ↑(matroid.E \ contracted),
      (matroid.contract contracted).Indep (Subtype.val '' chosen) ↔
        (other.contract (isomorphism.setImage contracted)).Indep
          (Subtype.val '' (isomorphism.contractGroundEquiv contracted '' chosen))
    intro chosen
    have chosen_subset : Subtype.val '' chosen ⊆ matroid.E := by
      rintro _ ⟨element, _, rfl⟩
      exact element.property.1
    have image_independent :=
      (isomorphism.indep_setImage_iff independent.subset_ground).mp independent
    rw [independent.contract_indep_iff, image_independent.contract_indep_iff,
      isomorphism.contractGroundEquiv_image,
      isomorphism.disjoint_setImage_iff chosen_subset independent.subset_ground,
      ← isomorphism.setImage_union,
      ← isomorphism.indep_setImage_iff (Set.union_subset chosen_subset independent.subset_ground)]

theorem Iso.simple (isomorphism : Iso matroid other) (simple : matroid.Simple) :
    other.Simple := by
  apply simple_iff_forall_pair_indep.mpr
  intro first second first_member second_member
  let source_first := isomorphism.toEquiv.symm ⟨first, first_member⟩
  let source_second := isomorphism.toEquiv.symm ⟨second, second_member⟩
  have independent := simple_iff_forall_pair_indep.mp simple
    source_first.val source_second.val source_first.property source_second.property
  have preservation := isomorphism.indep_image_iff' {source_first, source_second}
  simpa only [Set.image_pair, source_first, source_second, Equiv.apply_symm_apply] using
    preservation.mp (by simpa only [Set.image_pair] using independent)

theorem Iso.exists_isMinor (isomorphism : Iso matroid other) (minor : smaller ≤m matroid) :
    ∃ transported : Matroid OtherLabel, transported ≤m other ∧
      Nonempty (Iso smaller transported) := by
  obtain ⟨contracted, independent, restriction, _⟩ :=
    minor.exists_spanning_isRestriction_contract
  let contraction_iso := isomorphism.contractIndep independent
  refine ⟨(other.contract (isomorphism.setImage contracted)).restrict
    (contraction_iso.setImage smaller.E), ?_, ?_⟩
  · exact (restrict_isRestriction _ _
      (contraction_iso.setImage_subset_ground smaller.E)).isMinor.trans
      (contract_isMinor other (isomorphism.setImage contracted))
  · exact ⟨by simpa only [restriction.eq_restrict] using
      contraction_iso.restrict smaller.E restriction.subset⟩

theorem Iso.exists_simple_isMinor (isomorphism : Iso matroid other)
    (minor : smaller ≤m matroid) (simple : smaller.Simple) :
    ∃ transported : Matroid OtherLabel, transported ≤m other ∧ transported.Simple ∧
      Nonempty (Iso smaller transported) := by
  obtain ⟨transported, transported_minor, ⟨minor_iso⟩⟩ := isomorphism.exists_isMinor minor
  exact ⟨transported, transported_minor, minor_iso.simple simple, ⟨minor_iso⟩⟩

end Matroid
