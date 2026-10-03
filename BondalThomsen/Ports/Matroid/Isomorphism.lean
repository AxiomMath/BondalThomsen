module

public import BondalThomsen.Ports.Matroid.Simplification
public import BondalThomsen.Ports.Matroid.MinorPresentation

@[expose] public section

namespace Matroid

open Set

variable {Label OtherLabel ThirdLabel : Type*} {matroid : Matroid Label}
    {other : Matroid OtherLabel} {third : Matroid ThirdLabel}

def Iso.refl (matroid : Matroid Label) : Iso matroid matroid :=
  ⟨Equiv.refl _, fun _ => by simp⟩

def Iso.symm (isomorphism : Iso matroid other) : Iso other matroid where
  toEquiv := isomorphism.toEquiv.symm
  indep_image_iff' selected := by
    have preservation := isomorphism.indep_image_iff' (isomorphism.toEquiv.symm '' selected)
    simpa using preservation.symm

def Iso.trans (first : Iso matroid other) (second : Iso other third) : Iso matroid third where
  toEquiv := first.toEquiv.trans second.toEquiv
  indep_image_iff' selected := by
    rw [first.indep_image_iff', second.indep_image_iff']
    simp only [Equiv.coe_trans, Set.image_image, Function.comp_def]

def Iso.setImage (isomorphism : Iso matroid other) (selected : Set Label) : Set OtherLabel :=
  Subtype.val '' (isomorphism.toEquiv '' (Subtype.val ⁻¹' selected))

theorem Iso.setImage_subset_ground (isomorphism : Iso matroid other) (selected : Set Label) :
    isomorphism.setImage selected ⊆ other.E := by
  rintro _ ⟨element, _, rfl⟩
  exact element.property

@[simp] theorem Iso.setImage_union (isomorphism : Iso matroid other)
    (first second : Set Label) :
    isomorphism.setImage (first ∪ second) =
      isomorphism.setImage first ∪ isomorphism.setImage second := by
  simp [Iso.setImage, Set.preimage_union, Set.image_union]

theorem Iso.indep_setImage_iff (isomorphism : Iso matroid other) {selected : Set Label}
    (subset : selected ⊆ matroid.E) :
    matroid.Indep selected ↔ other.Indep (isomorphism.setImage selected) := by
  have source_eq : Subtype.val '' (Subtype.val ⁻¹' selected : Set matroid.E) = selected := by
    ext element
    constructor
    · rintro ⟨original, member, rfl⟩
      exact member
    · intro member
      exact ⟨⟨element, subset member⟩, member, rfl⟩
  simpa only [Iso.setImage, source_eq] using
    isomorphism.indep_image_iff' (Subtype.val ⁻¹' selected)

noncomputable def Iso.setEquiv (isomorphism : Iso matroid other) (selected : Set Label)
    (subset : selected ⊆ matroid.E) : selected ≃ isomorphism.setImage selected := by
  let mapping := fun element : selected =>
    (⟨(isomorphism.toEquiv ⟨element.val, subset element.property⟩).val,
      ⟨isomorphism.toEquiv ⟨element.val, subset element.property⟩,
        ⟨⟨element.val, subset element.property⟩, element.property, rfl⟩, rfl⟩⟩ :
      isomorphism.setImage selected)
  apply Equiv.ofBijective mapping
  constructor
  · intro first second equality
    apply Subtype.ext
    have ground_eq :
        isomorphism.toEquiv ⟨first.val, subset first.property⟩ =
          isomorphism.toEquiv ⟨second.val, subset second.property⟩ :=
      Subtype.ext (congrArg
        (fun element : isomorphism.setImage selected => element.val) equality)
    exact congrArg (fun element : matroid.E => element.val)
      (isomorphism.toEquiv.injective ground_eq)
  · rintro ⟨element, original, ⟨source, member, rfl⟩, rfl⟩
    exact ⟨⟨source.val, member⟩, rfl⟩

@[simp] theorem Iso.setEquiv_apply (isomorphism : Iso matroid other) (selected : Set Label)
    (subset : selected ⊆ matroid.E) (element : selected) :
    (isomorphism.setEquiv selected subset element).val =
      (isomorphism.toEquiv ⟨element.val, subset element.property⟩).val := rfl

noncomputable def Iso.restrict (isomorphism : Iso matroid other) (selected : Set Label)
    (subset : selected ⊆ matroid.E) :
    Iso (matroid.restrict selected) (other.restrict (isomorphism.setImage selected)) where
  toEquiv := isomorphism.setEquiv selected subset
  indep_image_iff' := by
    change ∀ chosen : Set selected,
      (matroid.restrict selected).Indep (Subtype.val '' chosen) ↔
        (other.restrict (isomorphism.setImage selected)).Indep
          (Subtype.val '' (isomorphism.setEquiv selected subset '' chosen))
    intro chosen
    have source_subset : Subtype.val '' chosen ⊆ matroid.E := by
      rintro _ ⟨element, _, rfl⟩
      exact subset element.property
    have image_eq : Subtype.val '' (isomorphism.setEquiv selected subset '' chosen) =
        isomorphism.setImage (Subtype.val '' chosen) := by
      ext element
      constructor
      · rintro ⟨_, ⟨original, member, rfl⟩, rfl⟩
        exact ⟨isomorphism.toEquiv ⟨original.val, subset original.property⟩,
          ⟨⟨original.val, subset original.property⟩, ⟨original, member, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨original, ⟨source, member, source_eq⟩, rfl⟩, rfl⟩
        refine ⟨isomorphism.setEquiv selected subset source, ⟨source, member, rfl⟩, ?_⟩
        rw [Iso.setEquiv_apply]
        apply congrArg (fun element : matroid.E => (isomorphism.toEquiv element).val)
        exact Subtype.ext source_eq
    rw [restrict_indep_iff, restrict_indep_iff, image_eq]
    have source_contained : Subtype.val '' chosen ⊆ selected := by
      rintro _ ⟨element, _, rfl⟩
      exact element.property
    have target_contained : isomorphism.setImage (Subtype.val '' chosen) ⊆
        isomorphism.setImage selected := by
      exact Set.image_mono (Set.image_mono (Set.preimage_mono source_contained))
    rw [and_iff_left source_contained, and_iff_left target_contained]
    exact isomorphism.indep_setImage_iff source_subset

end Matroid
