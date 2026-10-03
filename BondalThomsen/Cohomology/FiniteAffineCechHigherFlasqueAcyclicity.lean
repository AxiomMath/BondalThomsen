module

public import BondalThomsen.Cohomology.FiniteAffineCechFlasqueAcyclicity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open BondalThomsen.FiniteAffineCechHigherComparison BondalThomsen.FiniteAffineCechDerivedIso
open BondalThomsen.FiniteAffineCechFlasqueAcyclicity

namespace BondalThomsen.FiniteAffineCechHigherFlasqueAcyclicity

universe u

noncomputable section

variable {scheme : Scheme.{u}} {Index : Type u}

theorem cechCoordinate_ext (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ) {first second : (schemeCechComplex opens coefficient).X degree}
    (coordinates : ∀ tuple, cechCoordinate opens coefficient degree first tuple =
      cechCoordinate opens coefficient degree second tuple) : first = second := by
  apply (productElementsEquiv (fun tuple : Fin (degree + 1) → Index =>
    coefficient.presheaf.obj (op (cechIntersection opens degree tuple)))).injective
  funext tuple
  exact coordinates tuple

def cechOfSections (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ)
    (sections : ∀ tuple : Fin (degree + 1) → Index,
      coefficient.presheaf.obj (op (cechIntersection opens degree tuple))) :
    (schemeCechComplex opens coefficient).X degree :=
  (productElementsEquiv (fun tuple : Fin (degree + 1) → Index =>
    coefficient.presheaf.obj (op (cechIntersection opens degree tuple)))).symm sections

theorem cechOfSections_coordinate (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (degree : ℕ)
    (sections : ∀ tuple : Fin (degree + 1) → Index,
      coefficient.presheaf.obj (op (cechIntersection opens degree tuple)))
    (tuple : Fin (degree + 1) → Index) :
    cechCoordinate opens coefficient degree
      (cechOfSections opens coefficient degree sections) tuple = sections tuple := by
  exact congrFun ((productElementsEquiv _).apply_symm_apply sections) tuple

theorem cechIntersection_le_entry (opens : Index → scheme.Opens) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) (entry : Fin (degree + 1)) :
    cechIntersection opens degree tuple ≤ opens (tuple entry) :=
  leOfHom (Limits.Pi.π (opens ∘ tuple) entry)

theorem cechIntersection_le_cons (opens : Index → scheme.Opens) (anchor : Index)
    (dominates : ∀ index, opens index ≤ opens anchor) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    cechIntersection opens degree tuple ≤
      cechIntersection opens (degree + 1) (Fin.cons anchor tuple) := by
  have intersection_eq : cechIntersection opens (degree + 1) (Fin.cons anchor tuple) =
      ⨅ entry : Fin ((degree + 1) + 1),
        opens ((Fin.cons anchor tuple : Fin ((degree + 1) + 1) → Index) entry) := by
    exact productOpens_eq_iInf (opens ∘ Fin.cons anchor tuple)
  rw [intersection_eq]
  apply le_iInf
  intro entry
  refine Fin.cases ?_ (fun tail => ?_) entry
  · exact (cechIntersection_le_entry opens degree tuple 0).trans (dominates (tuple 0))
  · exact cechIntersection_le_entry opens degree tuple tail

def cechAnchorContraction (opens : Index → scheme.Opens) (anchor : Index)
    (dominates : ∀ index, opens index ≤ opens anchor) (coefficient : scheme.Modules)
    (degree : ℕ) (cochain : (schemeCechComplex opens coefficient).X (degree + 1)) :
    (schemeCechComplex opens coefficient).X degree :=
  cechOfSections opens coefficient degree (fun tuple =>
    coefficient.presheaf.map
      (homOfLE (cechIntersection_le_cons opens anchor dominates degree tuple)).op
        (cechCoordinate opens coefficient (degree + 1) cochain (Fin.cons anchor tuple)))

theorem sectionMap_comp (coefficient : scheme.Modules) {small middle large : scheme.Opens}
    (first : small ⟶ middle) (second : middle ⟶ large)
    (section_value : coefficient.presheaf.obj (op large)) :
    coefficient.presheaf.map first.op (coefficient.presheaf.map second.op section_value) =
      coefficient.presheaf.map (first ≫ second).op section_value := by
  rw [← ConcreteCategory.comp_apply, ← coefficient.presheaf.map_comp]
  rfl

theorem cechCoordinate_restriction_of_tuple_eq (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X degree)
    (first second : Fin (degree + 1) → Index) (tuple_eq : first = second)
    (smaller : scheme.Opens)
    (to_first : smaller ⟶ cechIntersection opens degree first)
    (to_second : smaller ⟶ cechIntersection opens degree second) :
    coefficient.presheaf.map to_first.op (cechCoordinate opens coefficient degree cochain first) =
      coefficient.presheaf.map to_second.op
        (cechCoordinate opens coefficient degree cochain second) := by
  subst second
  have arrow_eq : to_first = to_second := Subsingleton.elim _ _
  rw [arrow_eq]

theorem cechIntersection_region_le_cons (opens : Index → scheme.Opens) (anchor : Index)
    (region : scheme.Opens) (in_anchor : region ≤ opens anchor) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    region ⊓ cechIntersection opens degree tuple ≤
      cechIntersection opens (degree + 1) (Fin.cons anchor tuple) := by
  have intersection_eq : cechIntersection opens (degree + 1) (Fin.cons anchor tuple) =
      ⨅ entry : Fin ((degree + 1) + 1),
        opens ((Fin.cons anchor tuple : Fin ((degree + 1) + 1) → Index) entry) :=
    productOpens_eq_iInf (opens ∘ Fin.cons anchor tuple)
  rw [intersection_eq]
  apply le_iInf
  intro entry
  refine Fin.cases ?_ (fun tail => ?_) entry
  · exact inf_le_left.trans in_anchor
  · exact inf_le_right.trans (cechIntersection_le_entry opens degree tuple tail)

def cechRestrictedCoordinate (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ) (cochain : (schemeCechComplex opens coefficient).X degree)
    (region : scheme.Opens) (tuple : Fin (degree + 1) → Index) :
    coefficient.presheaf.obj (op (region ⊓ cechIntersection opens degree tuple)) :=
  sectionRestriction coefficient inf_le_right
    (cechCoordinate opens coefficient degree cochain tuple)

def cechLocalAnchorValue (opens : Index → scheme.Opens) (anchor : Index)
    (coefficient : scheme.Modules) (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X (degree + 1))
    (tuple : Fin (degree + 1) → Index) :
    coefficient.presheaf.obj (op (opens anchor ⊓ cechIntersection opens degree tuple)) :=
  sectionRestriction coefficient
    (cechIntersection_region_le_cons opens anchor (opens anchor) le_rfl degree tuple)
    (cechCoordinate opens coefficient (degree + 1) cochain (Fin.cons anchor tuple))

theorem cechRestrictedCoordinate_d (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X degree) (region : scheme.Opens)
    (tuple : Fin (degree + 2) → Index) :
    cechRestrictedCoordinate opens coefficient (degree + 1)
      ((schemeCechComplex opens coefficient).d degree (degree + 1) cochain) region tuple =
      ∑ face : Fin (degree + 2), (-1 : ℤ) ^ face.val •
        sectionRestriction coefficient
          (show region ⊓ cechIntersection opens (degree + 1) tuple ≤
            cechIntersection opens degree (tuple ∘ face.succAbove) from
            inf_le_right.trans (leOfHom (Limits.Pi.lift (fun entry =>
              Limits.Pi.π (opens ∘ tuple) (face.succAbove entry)))))
          (cechCoordinate opens coefficient degree cochain (tuple ∘ face.succAbove)) := by
  dsimp only [cechRestrictedCoordinate]
  rw [cechDifferential_component, map_sum]
  apply Finset.sum_congr rfl
  intro face _
  rw [map_zsmul]
  congr 1
  exact sectionMap_comp coefficient (homOfLE inf_le_right)
    (Limits.Pi.lift (fun entry => Limits.Pi.π (opens ∘ tuple) (face.succAbove entry))) _

theorem cechLocalAnchor_cycle_coboundary (opens : Index → scheme.Opens) (anchor : Index)
    (coefficient : scheme.Modules) (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X (degree + 1))
    (cycle : (schemeCechComplex opens coefficient).d (degree + 1) (degree + 2) cochain = 0)
    (preimage : (schemeCechComplex opens coefficient).X degree)
    (local_values : ∀ tuple, cechRestrictedCoordinate opens coefficient degree preimage
      (opens anchor) tuple = cechLocalAnchorValue opens anchor coefficient degree cochain tuple)
    (tuple : Fin (degree + 2) → Index) :
    cechRestrictedCoordinate opens coefficient (degree + 1)
      ((schemeCechComplex opens coefficient).d degree (degree + 1) preimage)
        (opens anchor) tuple =
      cechRestrictedCoordinate opens coefficient (degree + 1) cochain (opens anchor) tuple := by
  let smaller := opens anchor ⊓ cechIntersection opens (degree + 1) tuple
  let to_anchor : smaller ⟶ cechIntersection opens (degree + 2) (Fin.cons anchor tuple) :=
    homOfLE (cechIntersection_region_le_cons opens anchor (opens anchor) le_rfl
      (degree + 1) tuple)
  have zero_component : cechCoordinate opens coefficient (degree + 2)
      ((schemeCechComplex opens coefficient).d (degree + 1) (degree + 2) cochain)
        (Fin.cons anchor tuple) = 0 := by
    rw [cycle]
    exact (Limits.Pi.π (fun tuple : Fin (degree + 3) → Index =>
      coefficient.presheaf.obj (op (cechIntersection opens (degree + 2) tuple))) _).hom.map_zero
  have relation := congrArg (fun value => coefficient.presheaf.map to_anchor.op value)
    (cechDifferential_component opens coefficient (degree + 1) cochain (Fin.cons anchor tuple))
  rw [zero_component, map_zero, map_sum] at relation
  simp_rw [map_zsmul] at relation
  have zero_face : coefficient.presheaf.map to_anchor.op
      (coefficient.presheaf.map
        (Limits.Pi.lift (fun entry : Fin (degree + 2) =>
          Limits.Pi.π (opens ∘ Fin.cons anchor tuple)
            ((0 : Fin (degree + 3)).succAbove entry))).op
        (cechCoordinate opens coefficient (degree + 1) cochain
          (Fin.cons anchor tuple ∘ (0 : Fin (degree + 3)).succAbove))) =
      cechRestrictedCoordinate opens coefficient (degree + 1) cochain (opens anchor) tuple := by
    let to_face : cechIntersection opens (degree + 2) (Fin.cons anchor tuple) ⟶
        cechIntersection opens (degree + 1)
          (Fin.cons anchor tuple ∘ (0 : Fin (degree + 3)).succAbove) :=
      Limits.Pi.lift (fun entry => Limits.Pi.π (opens ∘ Fin.cons anchor tuple)
        ((0 : Fin (degree + 3)).succAbove entry))
    have evaluated := sectionMap_comp coefficient to_anchor to_face
      (cechCoordinate opens coefficient (degree + 1) cochain
        (Fin.cons anchor tuple ∘ (0 : Fin (degree + 3)).succAbove))
    exact evaluated.trans (cechCoordinate_restriction_of_tuple_eq opens coefficient
      (degree + 1) cochain _ tuple (Fin.cons_comp_succ _ _) smaller
        (to_anchor ≫ to_face) (homOfLE inf_le_right))
  have successor_face (face : Fin (degree + 2)) : coefficient.presheaf.map to_anchor.op
      (coefficient.presheaf.map
        (Limits.Pi.lift (fun entry : Fin (degree + 2) =>
          Limits.Pi.π (opens ∘ Fin.cons anchor tuple) (face.succ.succAbove entry))).op
        (cechCoordinate opens coefficient (degree + 1) cochain
          (Fin.cons anchor tuple ∘ face.succ.succAbove))) =
      sectionRestriction coefficient
        (show smaller ≤ cechIntersection opens degree (tuple ∘ face.succAbove) from
          inf_le_right.trans (leOfHom (Limits.Pi.lift (fun entry =>
            Limits.Pi.π (opens ∘ tuple) (face.succAbove entry)))))
        (cechCoordinate opens coefficient degree preimage (tuple ∘ face.succAbove)) := by
    let face_tuple := tuple ∘ face.succAbove
    let smaller_to_local : smaller ⟶ opens anchor ⊓ cechIntersection opens degree face_tuple :=
      homOfLE (le_inf inf_le_left (inf_le_right.trans (leOfHom (Limits.Pi.lift
        (fun entry => Limits.Pi.π (opens ∘ tuple) (face.succAbove entry))))))
    let to_anchor_face : cechIntersection opens (degree + 2) (Fin.cons anchor tuple) ⟶
        cechIntersection opens (degree + 1) (Fin.cons anchor tuple ∘ face.succ.succAbove) :=
      Limits.Pi.lift (fun entry =>
        Limits.Pi.π (opens ∘ Fin.cons anchor tuple) (face.succ.succAbove entry))
    let local_to_anchor : opens anchor ⊓ cechIntersection opens degree face_tuple ⟶
        cechIntersection opens (degree + 1) (Fin.cons anchor face_tuple) :=
      homOfLE (cechIntersection_region_le_cons opens anchor (opens anchor) le_rfl degree face_tuple)
    have local_relation := congrArg
      (fun value => coefficient.presheaf.map smaller_to_local.op value) (local_values face_tuple)
    change coefficient.presheaf.map smaller_to_local.op
      (coefficient.presheaf.map (homOfLE inf_le_right).op
        (cechCoordinate opens coefficient degree preimage face_tuple)) =
      coefficient.presheaf.map smaller_to_local.op
        (coefficient.presheaf.map local_to_anchor.op
          (cechCoordinate opens coefficient (degree + 1) cochain
            (Fin.cons anchor face_tuple))) at local_relation
    have first_eval := sectionMap_comp coefficient to_anchor to_anchor_face
      (cechCoordinate opens coefficient (degree + 1) cochain
        (Fin.cons anchor tuple ∘ face.succ.succAbove))
    have anchor_eval := sectionMap_comp coefficient smaller_to_local local_to_anchor
      (cechCoordinate opens coefficient (degree + 1) cochain (Fin.cons anchor face_tuple))
    have preimage_eval := sectionMap_comp coefficient smaller_to_local (homOfLE inf_le_right)
      (cechCoordinate opens coefficient degree preimage face_tuple)
    exact first_eval.trans ((cechCoordinate_restriction_of_tuple_eq opens coefficient
      (degree + 1) cochain _ _ (Fin.cons_comp_succ_succAbove _ _ _) smaller
        (to_anchor ≫ to_anchor_face) (smaller_to_local ≫ local_to_anchor)).trans
          (anchor_eval.symm.trans (local_relation.symm.trans preimage_eval)))
  let summands := fun face : Fin (degree + 3) => (-1 : ℤ) ^ face.val •
    coefficient.presheaf.map to_anchor.op
      (coefficient.presheaf.map (Limits.Pi.lift (fun entry : Fin (degree + 2) =>
        Limits.Pi.π (opens ∘ Fin.cons anchor tuple) (face.succAbove entry))).op
        (cechCoordinate opens coefficient (degree + 1) cochain
          (Fin.cons anchor tuple ∘ face.succAbove)))
  have split_sum : ∑ face, summands face = summands 0 +
      ∑ face : Fin (degree + 2), summands face.succ := Fin.sum_univ_succ summands
  change 0 = ∑ face, summands face at relation
  rw [split_sum] at relation
  dsimp only [summands] at relation
  simp only [Fin.val_zero, pow_zero, one_zsmul, zero_face, Fin.val_succ, pow_succ,
    mul_neg_one, neg_zsmul, successor_face] at relation
  rw [Finset.sum_neg_distrib] at relation
  rw [← sub_eq_add_neg] at relation
  rw [cechRestrictedCoordinate_d]
  exact (sub_eq_zero.mp relation.symm).symm

theorem flasqueSectionExtension_with_zero (coefficient : scheme.Modules)
    [coefficient.presheaf.IsFlasque] {new_region old_region larger : scheme.Opens}
    (new_le : new_region ≤ larger) (old_le : old_region ≤ larger)
    (section_value : coefficient.presheaf.obj (op new_region))
    (zero_overlap : sectionRestriction coefficient inf_le_left section_value =
      (0 : coefficient.presheaf.obj (op (new_region ⊓ old_region)))) :
    ∃ extension : coefficient.presheaf.obj (op larger),
      sectionRestriction coefficient new_le extension = section_value ∧
        sectionRestriction coefficient old_le extension = 0 := by
  let family : Fin 2 → scheme.Opens := ![new_region, old_region]
  let sections : ∀ entry, coefficient.presheaf.obj (op (family entry)) :=
    fun entry => Fin.cases section_value (fun _ => 0) entry
  have compatible : TopCat.Presheaf.IsCompatible coefficient.presheaf family sections := by
    intro first second
    fin_cases first <;> fin_cases second
    · rfl
    · change sectionRestriction coefficient inf_le_left section_value =
        sectionRestriction coefficient inf_le_right (0 : coefficient.presheaf.obj (op old_region))
      rw [map_zero]
      exact zero_overlap
    · change sectionRestriction coefficient inf_le_left (0 : coefficient.presheaf.obj (op old_region)) =
        sectionRestriction coefficient inf_le_right section_value
      rw [map_zero]
      have reversed := congrArg (sectionRestriction coefficient
        (show old_region ⊓ new_region ≤ new_region ⊓ old_region from
          le_inf inf_le_right inf_le_left)) zero_overlap
      rw [sectionRestriction_comp, map_zero] at reversed
      exact reversed.symm
    · rfl
  obtain ⟨glued_section, glued, _⟩ := TopCat.Sheaf.existsUnique_gluing
    (⟨coefficient.presheaf, coefficient.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} scheme)
    family sections compatible
  have union_le : iSup family ≤ larger := by
    apply iSup_le
    intro entry
    fin_cases entry
    · exact new_le
    · exact old_le
  obtain ⟨extension, extension_image⟩ :=
    flasqueSectionExtension coefficient union_le glued_section
  refine ⟨extension, ?_, ?_⟩
  · have gluing := glued 0
    change sectionRestriction coefficient (le_iSup family 0) glued_section = section_value at gluing
    rw [← extension_image, sectionRestriction_comp] at gluing
    exact gluing
  · have gluing := glued 1
    change sectionRestriction coefficient (le_iSup family 1) glued_section = 0 at gluing
    rw [← extension_image, sectionRestriction_comp] at gluing
    exact gluing

def CechVanishesOn (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ) (cochain : (schemeCechComplex opens coefficient).X degree)
    (region : scheme.Opens) : Prop :=
  ∀ tuple, cechRestrictedCoordinate opens coefficient degree cochain region tuple = 0

theorem cechLocalAnchorValue_zero_overlap (opens : Index → scheme.Opens) (anchor : Index)
    (coefficient : scheme.Modules) (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X (degree + 1))
    (old_region : scheme.Opens) (vanishes : CechVanishesOn opens coefficient (degree + 1)
      cochain old_region) (tuple : Fin (degree + 1) → Index) :
    sectionRestriction coefficient inf_le_left
      (cechLocalAnchorValue opens anchor coefficient degree cochain tuple) =
      (0 : coefficient.presheaf.obj (op
        ((opens anchor ⊓ cechIntersection opens degree tuple) ⊓
          (old_region ⊓ cechIntersection opens degree tuple)))) := by
  let overlap := (opens anchor ⊓ cechIntersection opens degree tuple) ⊓
    (old_region ⊓ cechIntersection opens degree tuple)
  have to_old : overlap ≤ old_region := inf_le_right.trans inf_le_left
  have to_anchor_tuple : overlap ≤ cechIntersection opens (degree + 1) (Fin.cons anchor tuple) :=
    inf_le_left.trans (cechIntersection_region_le_cons opens anchor (opens anchor) le_rfl degree tuple)
  have restricted_zero := congrArg
    (sectionRestriction coefficient (le_inf to_old to_anchor_tuple))
      (vanishes (Fin.cons anchor tuple))
  dsimp only [cechRestrictedCoordinate] at restricted_zero
  rw [sectionRestriction_comp, map_zero] at restricted_zero
  dsimp only [cechLocalAnchorValue]
  rw [sectionRestriction_comp]
  exact restricted_zero

theorem cechLocalAnchor_extension_with_zero (opens : Index → scheme.Opens) (anchor : Index)
    (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque] (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X (degree + 1))
    (old_region : scheme.Opens)
    (vanishes : CechVanishesOn opens coefficient (degree + 1) cochain old_region) :
    ∃ preimage : (schemeCechComplex opens coefficient).X degree,
      (∀ tuple, cechRestrictedCoordinate opens coefficient degree preimage (opens anchor) tuple =
        cechLocalAnchorValue opens anchor coefficient degree cochain tuple) ∧
      CechVanishesOn opens coefficient degree preimage old_region := by
  classical
  have extensions (tuple : Fin (degree + 1) → Index) := flasqueSectionExtension_with_zero
    coefficient (larger := cechIntersection opens degree tuple) inf_le_right inf_le_right
      (cechLocalAnchorValue opens anchor coefficient degree cochain tuple)
        (cechLocalAnchorValue_zero_overlap opens anchor coefficient degree cochain old_region
          vanishes tuple)
  let sections := fun tuple => (extensions tuple).choose
  refine ⟨cechOfSections opens coefficient degree sections, ?_, ?_⟩
  · intro tuple
    dsimp only [cechRestrictedCoordinate]
    rw [cechOfSections_coordinate]
    exact (extensions tuple).choose_spec.1
  · intro tuple
    dsimp only [cechRestrictedCoordinate]
    rw [cechOfSections_coordinate]
    exact (extensions tuple).choose_spec.2

theorem cechRestrictedCoordinate_sub (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (degree : ℕ)
    (first second : (schemeCechComplex opens coefficient).X degree)
    (region : scheme.Opens) (tuple : Fin (degree + 1) → Index) :
    cechRestrictedCoordinate opens coefficient degree (first - second) region tuple =
      cechRestrictedCoordinate opens coefficient degree first region tuple -
        cechRestrictedCoordinate opens coefficient degree second region tuple := by
  have coordinate_sub :=
    (Limits.Pi.π (fun tuple : Fin (degree + 1) → Index =>
      coefficient.presheaf.obj (op (cechIntersection opens degree tuple))) tuple).hom.map_sub first second
  dsimp only [cechRestrictedCoordinate, cechCoordinate]
  rw [coordinate_sub, map_sub]

theorem cechVanishesOn_d (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ) (cochain : (schemeCechComplex opens coefficient).X degree)
    (region : scheme.Opens) (vanishes : CechVanishesOn opens coefficient degree cochain region) :
    CechVanishesOn opens coefficient (degree + 1)
      ((schemeCechComplex opens coefficient).d degree (degree + 1) cochain) region := by
  intro tuple
  rw [cechRestrictedCoordinate_d]
  apply Finset.sum_eq_zero
  intro face _
  have to_face : region ⊓ cechIntersection opens (degree + 1) tuple ≤
      region ⊓ cechIntersection opens degree (tuple ∘ face.succAbove) :=
    le_inf inf_le_left (inf_le_right.trans (leOfHom (Limits.Pi.lift
      (fun entry => Limits.Pi.π (opens ∘ tuple) (face.succAbove entry)))))
  have restricted_zero := congrArg (sectionRestriction coefficient to_face)
    (vanishes (tuple ∘ face.succAbove))
  dsimp only [cechRestrictedCoordinate] at restricted_zero
  rw [sectionRestriction_comp, map_zero] at restricted_zero
  rw [restricted_zero, smul_zero]

theorem cechVanishesOn_sup (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ) (cochain : (schemeCechComplex opens coefficient).X degree)
    (first second : scheme.Opens)
    (first_zero : CechVanishesOn opens coefficient degree cochain first)
    (second_zero : CechVanishesOn opens coefficient degree cochain second) :
    CechVanishesOn opens coefficient degree cochain (first ⊔ second) := by
  intro tuple
  let intersection := cechIntersection opens degree tuple
  let region := (first ⊔ second) ⊓ intersection
  let to_first : first ⊓ intersection ⟶ region :=
    homOfLE (inf_le_inf le_sup_left le_rfl)
  let to_second : second ⊓ intersection ⟶ region :=
    homOfLE (inf_le_inf le_sup_right le_rfl)
  have cover : region ≤ (first ⊓ intersection) ⊔ (second ⊓ intersection) := by
    exact (inf_sup_right first second intersection).le
  apply TopCat.Sheaf.eq_of_locally_eq₂
    (⟨coefficient.presheaf, coefficient.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} scheme)
      to_first to_second cover
  · change coefficient.presheaf.map to_first.op
      (sectionRestriction coefficient inf_le_right
        (cechCoordinate opens coefficient degree cochain tuple)) =
      coefficient.presheaf.map to_first.op 0
    rw [map_zero]
    exact (sectionMap_comp coefficient to_first (homOfLE inf_le_right) _).trans
      (first_zero tuple)
  · change coefficient.presheaf.map to_second.op
      (sectionRestriction coefficient inf_le_right
        (cechCoordinate opens coefficient degree cochain tuple)) =
      coefficient.presheaf.map to_second.op 0
    rw [map_zero]
    exact (sectionMap_comp coefficient to_second (homOfLE inf_le_right) _).trans
      (second_zero tuple)

theorem standardCech_cycle_local_correction (opens : Index → scheme.Opens) (anchor : Index)
    (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque] (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X (degree + 1))
    (cycle : (schemeCechComplex opens coefficient).d (degree + 1) (degree + 2) cochain = 0)
    (old_region : scheme.Opens)
    (vanishes : CechVanishesOn opens coefficient (degree + 1) cochain old_region) :
    ∃ correction : (schemeCechComplex opens coefficient).X degree,
      CechVanishesOn opens coefficient (degree + 1)
        (cochain - (schemeCechComplex opens coefficient).d degree (degree + 1) correction)
          (old_region ⊔ opens anchor) := by
  obtain ⟨correction, local_values, old_zero⟩ :=
    cechLocalAnchor_extension_with_zero opens anchor coefficient degree cochain old_region vanishes
  refine ⟨correction, cechVanishesOn_sup opens coefficient (degree + 1) _ _ _ ?_ ?_⟩
  · intro tuple
    rw [cechRestrictedCoordinate_sub, vanishes tuple,
      cechVanishesOn_d opens coefficient degree correction old_region old_zero tuple, sub_self]
  · intro tuple
    rw [cechRestrictedCoordinate_sub,
      cechLocalAnchor_cycle_coboundary opens anchor coefficient degree cochain cycle
        correction local_values tuple, sub_self]

theorem cechVanishesOn_bot (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ) (cochain : (schemeCechComplex opens coefficient).X degree) :
    CechVanishesOn opens coefficient degree cochain ⊥ := by
  intro tuple
  let empty_family : Empty → scheme.Opens := fun entry => nomatch entry
  have cover : (⊥ : scheme.Opens) ⊓ cechIntersection opens degree tuple ≤ iSup empty_family := by
    simp
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨coefficient.presheaf, coefficient.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} scheme)
      empty_family _ (fun entry => nomatch entry) cover
  intro entry
  exact nomatch entry

theorem cechVanishesOn_supFamily_eq_zero (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X degree)
    (vanishes : CechVanishesOn opens coefficient degree cochain (iSup opens)) : cochain = 0 := by
  apply cechCoordinate_ext opens coefficient degree
  intro tuple
  have covered : cechIntersection opens degree tuple ≤ iSup opens :=
    (cechIntersection_le_entry opens degree tuple 0).trans (le_iSup opens (tuple 0))
  have to_region : cechIntersection opens degree tuple ≤
      iSup opens ⊓ cechIntersection opens degree tuple := le_inf covered le_rfl
  have restricted_zero := congrArg (sectionRestriction coefficient to_region) (vanishes tuple)
  dsimp only [cechRestrictedCoordinate] at restricted_zero
  rw [sectionRestriction_comp, sectionRestriction_refl, map_zero] at restricted_zero
  have zero_coordinate :=
    (Limits.Pi.π (fun tuple : Fin (degree + 1) → Index =>
      coefficient.presheaf.obj (op (cechIntersection opens degree tuple))) tuple).hom.map_zero
  exact restricted_zero.trans zero_coordinate.symm

def finiteOpenUnion (opens : Index → scheme.Opens) (indices : Finset Index) : scheme.Opens :=
  ⨆ index : indices, opens index.val

theorem finiteOpenUnion_empty (opens : Index → scheme.Opens) : finiteOpenUnion opens ∅ = ⊥ := by
  simp [finiteOpenUnion]

theorem finiteOpenUnion_insert [DecidableEq Index] (opens : Index → scheme.Opens) (anchor : Index)
    (indices : Finset Index) :
    finiteOpenUnion opens (insert anchor indices) = finiteOpenUnion opens indices ⊔ opens anchor := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro index
    rcases Finset.mem_insert.mp index.property with new_index | old_index
    · have open_eq : opens index.val = opens anchor := congrArg opens new_index
      exact open_eq.le.trans le_sup_right
    · exact (le_iSup (fun index : indices => opens index.val) ⟨index.val, old_index⟩).trans le_sup_left
  · apply sup_le
    · apply iSup_le
      intro index
      exact le_iSup (fun index : (insert anchor indices : Finset Index) => opens index.val)
        ⟨index.val, Finset.mem_insert_of_mem index.property⟩
    · exact le_iSup (fun index : (insert anchor indices : Finset Index) => opens index.val)
        ⟨anchor, Finset.mem_insert_self _ _⟩

theorem standardCech_cycle_finite_correction (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque] (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X (degree + 1))
    (cycle : (schemeCechComplex opens coefficient).d (degree + 1) (degree + 2) cochain = 0)
    (indices : Finset Index) :
    ∃ preimage : (schemeCechComplex opens coefficient).X degree,
      CechVanishesOn opens coefficient (degree + 1)
        (cochain - (schemeCechComplex opens coefficient).d degree (degree + 1) preimage)
          (finiteOpenUnion opens indices) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    rw [finiteOpenUnion_empty]
    exact cechVanishesOn_bot opens coefficient (degree + 1) _
  | @insert anchor indices not_mem induction_hypothesis =>
    obtain ⟨previous, previous_zero⟩ := induction_hypothesis
    let residual := cochain - (schemeCechComplex opens coefficient).d degree (degree + 1) previous
    have residual_cycle : (schemeCechComplex opens coefficient).d (degree + 1) (degree + 2)
        residual = 0 := by
      change (schemeCechComplex opens coefficient).d (degree + 1) (degree + 2)
        (cochain - (schemeCechComplex opens coefficient).d degree (degree + 1) previous) = 0
      rw [map_sub, cycle, ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
      change 0 - (0 :
        (schemeCechComplex opens coefficient).X degree ⟶
          (schemeCechComplex opens coefficient).X (degree + 2)).hom previous = 0
      have zero_eval : (0 :
          (schemeCechComplex opens coefficient).X degree ⟶
            (schemeCechComplex opens coefficient).X (degree + 2)).hom previous = 0 := rfl
      rw [zero_eval, sub_self]
    obtain ⟨correction, corrected_zero⟩ := standardCech_cycle_local_correction opens anchor
      coefficient degree residual residual_cycle (finiteOpenUnion opens indices) previous_zero
    refine ⟨previous + correction, ?_⟩
    rw [finiteOpenUnion_insert]
    have residual_eq : cochain - (schemeCechComplex opens coefficient).d degree (degree + 1)
        (previous + correction) = residual -
          (schemeCechComplex opens coefficient).d degree (degree + 1) correction := by
      rw [map_add]
      dsimp only [residual]
      abel
    rw [residual_eq]
    exact corrected_zero

theorem standardCech_positive_cycle_isBoundary [Finite Index]
    (opens : Index → scheme.Opens) (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque]
    (degree : ℕ) (cochain : (schemeCechComplex opens coefficient).X (degree + 1))
    (cycle : (schemeCechComplex opens coefficient).d (degree + 1) (degree + 2) cochain = 0) :
    ∃ preimage : (schemeCechComplex opens coefficient).X degree,
      (schemeCechComplex opens coefficient).d degree (degree + 1) preimage = cochain := by
  classical
  let := Fintype.ofFinite Index
  obtain ⟨preimage, vanishes⟩ := standardCech_cycle_finite_correction opens coefficient degree
    cochain cycle Finset.univ
  have union_eq : finiteOpenUnion opens Finset.univ = iSup opens := by
    apply le_antisymm
    · exact iSup_le (fun index => le_iSup opens index.val)
    · exact iSup_le (fun index => le_iSup (fun index : (Finset.univ : Finset Index) =>
        opens index.val) ⟨index, Finset.mem_univ _⟩)
  rw [union_eq] at vanishes
  have residual_zero := cechVanishesOn_supFamily_eq_zero opens coefficient (degree + 1) _ vanishes
  exact ⟨preimage, (sub_eq_zero.mp residual_zero).symm⟩

theorem standardCech_exactAt_positive [Finite Index] (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque] (degree : ℕ) :
    (schemeCechComplex opens coefficient).ExactAt (degree + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ degree (degree + 1) (degree + 2)
    (by simp) (by simp)).mpr
  apply (ShortComplex.ab_exact_iff _).mpr
  exact standardCech_positive_cycle_isBoundary opens coefficient degree

theorem standardCech_homology_positive_isZero [Finite Index] (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque] (degree : ℕ) :
    IsZero ((schemeCechComplex opens coefficient).homology (degree + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (standardCech_exactAt_positive opens coefficient degree)

end

end BondalThomsen.FiniteAffineCechHigherFlasqueAcyclicity

