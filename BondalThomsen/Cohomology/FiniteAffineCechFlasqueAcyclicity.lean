module

public import BondalThomsen.Cohomology.FiniteAffineCechDerivedIso
public import Mathlib.Topology.Sheaves.Flasque

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open BondalThomsen.FiniteAffineCechHigherComparison BondalThomsen.FiniteAffineCechDerivedIso
open BondalThomsen.QuasicoherentFlasqueTowerConstruction
open BondalThomsen.FiniteAffineCoverQuasicoherentExtensions
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.FiniteAffineCechFlasqueAcyclicity

universe u

noncomputable section

variable {scheme : Scheme.{u}} {Index : Type u}

def sectionRestriction (coefficient : scheme.Modules) {smaller larger : scheme.Opens}
    (inclusion : smaller ≤ larger) :
    coefficient.presheaf.obj (op larger) →+ coefficient.presheaf.obj (op smaller) :=
  (coefficient.presheaf.map (homOfLE inclusion).op).hom

theorem sectionRestriction_comp (coefficient : scheme.Modules)
    {small middle large : scheme.Opens} (first : small ≤ middle) (second : middle ≤ large)
    (section_value : coefficient.presheaf.obj (op large)) :
    sectionRestriction coefficient first (sectionRestriction coefficient second section_value) =
      sectionRestriction coefficient (first.trans second) section_value := by
  change coefficient.presheaf.map (homOfLE first).op
      (coefficient.presheaf.map (homOfLE second).op section_value) = _
  rw [← ConcreteCategory.comp_apply, ← coefficient.presheaf.map_comp]
  rfl

theorem sectionRestriction_refl (coefficient : scheme.Modules) (open_set : scheme.Opens)
    (section_value : coefficient.presheaf.obj (op open_set)) :
    sectionRestriction coefficient (le_refl open_set) section_value = section_value := by
  change coefficient.presheaf.map (homOfLE (le_refl open_set)).op section_value = _
  change coefficient.presheaf.map (𝟙 (op open_set)) section_value = _
  rw [coefficient.presheaf.map_id]
  rfl

theorem flasqueSectionExtension (coefficient : scheme.Modules)
    [coefficient.presheaf.IsFlasque] {smaller larger : scheme.Opens}
    (inclusion : smaller ≤ larger) (section_value : coefficient.presheaf.obj (op smaller)) :
    ∃ extension : coefficient.presheaf.obj (op larger),
      sectionRestriction coefficient inclusion extension = section_value :=
  (AddCommGrpCat.epi_iff_surjective (coefficient.presheaf.map (homOfLE inclusion).op)).mp
    inferInstance section_value

structure SectionOneCocycle (opens : Index → scheme.Opens) (coefficient : scheme.Modules) where
  value : ∀ first second, coefficient.presheaf.obj (op (opens first ⊓ opens second))
  cocycle : ∀ first second third,
    sectionRestriction coefficient
        (show (opens first ⊓ opens second) ⊓ opens third ≤ opens second ⊓ opens third from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) (value second third) -
      sectionRestriction coefficient
        (show (opens first ⊓ opens second) ⊓ opens third ≤ opens first ⊓ opens third from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right) (value first third) +
      sectionRestriction coefficient inf_le_left (value first second) = 0

namespace SectionOneCocycle

variable {opens : Index → scheme.Opens} {coefficient : scheme.Modules}

theorem diagonal (cocycle : SectionOneCocycle opens coefficient) (index : Index) :
    cocycle.value index index = 0 := by
  have relation := cocycle.cocycle index index index
  have intersection : (opens index ⊓ opens index) ⊓ opens index =
      opens index ⊓ opens index := by simp
  have restriction_injective : Function.Injective
      (sectionRestriction coefficient (show (opens index ⊓ opens index) ⊓ opens index ≤
        opens index ⊓ opens index from inf_le_left)) := by
    change Function.Injective (coefficient.presheaf.map (homOfLE _).op)
    let : IsIso (homOfLE (show (opens index ⊓ opens index) ⊓ opens index ≤
        opens index ⊓ opens index from inf_le_left)) := by
      exact ⟨⟨eqToHom intersection.symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    exact (ConcreteCategory.bijective_of_isIso _).injective
  apply restriction_injective
  simpa only [sub_self, zero_add, map_zero] using relation

theorem antisymmetric (cocycle : SectionOneCocycle opens coefficient) (first second : Index) :
    sectionRestriction coefficient (show opens first ⊓ opens second ≤
      opens second ⊓ opens first from le_inf inf_le_right inf_le_left)
      (cocycle.value second first) = -cocycle.value first second := by
  have relation := cocycle.cocycle first second first
  rw [cocycle.diagonal, map_zero, sub_zero] at relation
  have triple : (opens first ⊓ opens second) ⊓ opens first = opens first ⊓ opens second :=
    inf_eq_left.mpr inf_le_left
  have transported := congrArg (sectionRestriction coefficient (show opens first ⊓ opens second ≤
    (opens first ⊓ opens second) ⊓ opens first from le_inf le_rfl inf_le_left)) relation
  simp only [map_add, map_zero, sectionRestriction_comp,
    sectionRestriction_refl] at transported
  exact eq_neg_of_add_eq_zero_left transported

end SectionOneCocycle

namespace SectionOneCocycle

variable {opens : Index → scheme.Opens} {coefficient : scheme.Modules}

theorem restriction_triangle (cocycle : SectionOneCocycle opens coefficient)
    (first second third : Index) (smaller : scheme.Opens)
    (to_first : smaller ≤ opens first) (to_second : smaller ≤ opens second)
    (to_third : smaller ≤ opens third) :
    sectionRestriction coefficient (le_inf to_second to_third) (cocycle.value second third) -
      sectionRestriction coefficient (le_inf to_first to_third) (cocycle.value first third) +
      sectionRestriction coefficient (le_inf to_first to_second) (cocycle.value first second) = 0 := by
  have relation := cocycle.cocycle first second third
  have restricted := congrArg (sectionRestriction coefficient
    (le_inf (le_inf to_first to_second) to_third)) relation
  simpa only [map_add, map_sub, map_zero, sectionRestriction_comp] using restricted

theorem exists_coboundary_on_finset [coefficient.presheaf.IsFlasque]
    (cocycle : SectionOneCocycle opens coefficient) (indices : Finset Index) :
    ∃ sections : ∀ index, coefficient.presheaf.obj (op (opens index)),
      ∀ first ∈ indices, ∀ second ∈ indices,
        sectionRestriction coefficient inf_le_right (sections second) -
          sectionRestriction coefficient inf_le_left (sections first) =
            cocycle.value first second := by
  classical
  induction indices using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert added indices not_mem induction_hypothesis =>
    obtain ⟨previous, previous_coboundary⟩ := induction_hypothesis
    let overlaps : indices → scheme.Opens := fun index => opens index.val ⊓ opens added
    let local_sections : ∀ index : indices, coefficient.presheaf.obj (op (overlaps index)) :=
      fun index => sectionRestriction coefficient inf_le_left (previous index.val) +
        cocycle.value index.val added
    have compatible : TopCat.Presheaf.IsCompatible coefficient.presheaf overlaps local_sections := by
      intro first second
      let intersection := overlaps first ⊓ overlaps second
      have to_first : intersection ≤ opens first.val := inf_le_left.trans inf_le_left
      have to_second : intersection ≤ opens second.val := inf_le_right.trans inf_le_left
      have to_added : intersection ≤ opens added := inf_le_left.trans inf_le_right
      have old_relation := previous_coboundary first.val first.property second.val second.property
      have old_restricted := congrArg
        (sectionRestriction coefficient (le_inf to_first to_second)) old_relation
      simp only [map_sub, sectionRestriction_comp] at old_restricted
      have triangle := cocycle.restriction_triangle first.val second.val added intersection
        to_first to_second to_added
      change sectionRestriction coefficient inf_le_left (local_sections first) =
        sectionRestriction coefficient inf_le_right (local_sections second)
      dsimp only [local_sections]
      rw [map_add, map_add, sectionRestriction_comp, sectionRestriction_comp]
      change sectionRestriction coefficient to_first (previous first.val) +
          sectionRestriction coefficient (le_inf to_first to_added)
            (cocycle.value first.val added) =
        sectionRestriction coefficient to_second (previous second.val) +
          sectionRestriction coefficient (le_inf to_second to_added)
            (cocycle.value second.val added)
      rw [← old_restricted] at triangle
      apply sub_eq_zero.mp
      have negated := congrArg Neg.neg triangle
      convert negated using 1 <;> abel
    obtain ⟨glued_section, glued, _⟩ := TopCat.Sheaf.existsUnique_gluing
      (⟨coefficient.presheaf, coefficient.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} scheme)
      overlaps local_sections compatible
    obtain ⟨new_section, extension_image⟩ := flasqueSectionExtension coefficient
      (show iSup overlaps ≤ opens added from iSup_le (fun _ => inf_le_right)) glued_section
    have new_restriction (index : indices) :
        sectionRestriction coefficient inf_le_right new_section = local_sections index := by
      have gluing := glued index
      change sectionRestriction coefficient (le_iSup overlaps index) glued_section = _ at gluing
      rw [← extension_image, sectionRestriction_comp] at gluing
      exact gluing
    let sections := Function.update previous added new_section
    refine ⟨sections, ?_⟩
    intro first first_mem second second_mem
    rcases Finset.mem_insert.mp first_mem with first_new | first_old
    · subst first
      rcases Finset.mem_insert.mp second_mem with second_new | second_old
      · subst second
        simp only [cocycle.diagonal]
        exact sub_self _
      · have second_ne : second ≠ added := fun equality => not_mem (equality ▸ second_old)
        have relation := new_restriction ⟨second, second_old⟩
        have to_overlap : opens added ⊓ opens second ≤ opens second ⊓ opens added :=
          le_inf inf_le_right inf_le_left
        have restricted := congrArg (sectionRestriction coefficient to_overlap) relation
        simp only [local_sections, map_add, sectionRestriction_comp] at restricted
        have reverse := cocycle.antisymmetric added second
        dsimp only [sections]
        simp only [Function.update_self, Function.update_of_ne second_ne]
        rw [reverse] at restricted
        apply sub_eq_iff_eq_add'.mpr
        rw [restricted]
        abel
    · rcases Finset.mem_insert.mp second_mem with second_new | second_old
      · subst second
        have first_ne : first ≠ added := fun equality => not_mem (equality ▸ first_old)
        have relation := new_restriction ⟨first, first_old⟩
        dsimp only [sections]
        simp only [Function.update_self, Function.update_of_ne first_ne]
        dsimp only [local_sections] at relation
        exact sub_eq_iff_eq_add'.mpr relation
      · have first_ne : first ≠ added := fun equality => not_mem (equality ▸ first_old)
        have second_ne : second ≠ added := fun equality => not_mem (equality ▸ second_old)
        dsimp only [sections]
        simp only [Function.update_of_ne first_ne, Function.update_of_ne second_ne]
        exact previous_coboundary first first_old second second_old

theorem exists_coboundary [Finite Index] [coefficient.presheaf.IsFlasque]
    (cocycle : SectionOneCocycle opens coefficient) :
    ∃ sections : ∀ index, coefficient.presheaf.obj (op (opens index)),
      ∀ first second,
        sectionRestriction coefficient inf_le_right (sections second) -
          sectionRestriction coefficient inf_le_left (sections first) =
            cocycle.value first second := by
  let := Fintype.ofFinite Index
  obtain ⟨sections, coboundary⟩ := cocycle.exists_coboundary_on_finset Finset.univ
  exact ⟨sections, fun first second => coboundary first (Finset.mem_univ _)
    second (Finset.mem_univ _)⟩

end SectionOneCocycle

def cechCoordinate (opens : Index → scheme.Opens) (coefficient : scheme.Modules) (degree : ℕ)
    (cochain : (schemeCechComplex opens coefficient).X degree)
    (tuple : Fin (degree + 1) → Index) :
    coefficient.presheaf.obj (op (cechIntersection opens degree tuple)) :=
  Limits.Pi.π (fun tuple : Fin (degree + 1) → Index =>
    coefficient.presheaf.obj (op (cechIntersection opens degree tuple))) tuple cochain

def cechOneCoordinate (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (cochain : (schemeCechComplex opens coefficient).X 1) (first second : Index) :
    coefficient.presheaf.obj (op (opens first ⊓ opens second)) :=
  coefficient.presheaf.map (eqToHom
    (cechIntersection_one opens ![first, second]).symm).op
      (cechCoordinate opens coefficient 1 cochain ![first, second])

theorem cechOneCoordinate_restriction (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (cochain : (schemeCechComplex opens coefficient).X 1)
    (tuple : Fin 2 → Index) (smaller : scheme.Opens)
    (to_intersection : smaller ⟶ cechIntersection opens 1 tuple)
    (to_pair : smaller ⟶ opens (tuple 0) ⊓ opens (tuple 1)) :
    coefficient.presheaf.map to_intersection.op (cechCoordinate opens coefficient 1 cochain tuple) =
      coefficient.presheaf.map to_pair.op
        (cechOneCoordinate opens coefficient cochain (tuple 0) (tuple 1)) := by
  obtain ⟨first, second, tuple_eq⟩ : ∃ first second, tuple = ![first, second] := by
    refine ⟨tuple 0, tuple 1, ?_⟩
    funext entry
    fin_cases entry <;> rfl
  subst tuple
  dsimp only [cechOneCoordinate]
  have same_map : coefficient.presheaf.map to_intersection.op =
      coefficient.presheaf.map (eqToHom
        (cechIntersection_one opens ![first, second]).symm).op ≫
          coefficient.presheaf.map to_pair.op := by
    rw [← coefficient.presheaf.map_comp]
    rfl
  rw [same_map]
  rfl

theorem cechOneCoordinate_restriction_of_tuple_eq (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (cochain : (schemeCechComplex opens coefficient).X 1)
    (tuple : Fin 2 → Index) (first second : Index) (tuple_eq : tuple = ![first, second])
    (smaller : scheme.Opens) (to_intersection : smaller ⟶ cechIntersection opens 1 tuple)
    (to_pair : smaller ⟶ opens first ⊓ opens second) :
    coefficient.presheaf.map to_intersection.op (cechCoordinate opens coefficient 1 cochain tuple) =
      coefficient.presheaf.map to_pair.op
        (cechOneCoordinate opens coefficient cochain first second) := by
  subst tuple
  exact cechOneCoordinate_restriction opens coefficient cochain _ _ _ _

theorem sectionRestriction_transport (coefficient : scheme.Modules)
    {categorical literal larger : scheme.Opens} (intersection_eq : categorical = literal)
    (to_larger : categorical ⟶ larger) (inclusion : literal ≤ larger)
    (section_value : coefficient.presheaf.obj (op larger)) :
    coefficient.presheaf.map (eqToHom intersection_eq.symm).op
      (coefficient.presheaf.map to_larger.op section_value) =
        sectionRestriction coefficient inclusion section_value := by
  rw [← ConcreteCategory.comp_apply, ← coefficient.presheaf.map_comp]
  rfl

theorem cechIntersection_two (opens : Index → scheme.Opens) (tuple : Fin 3 → Index) :
    cechIntersection opens 2 tuple = (opens (tuple 0) ⊓ opens (tuple 1)) ⊓ opens (tuple 2) := by
  rw [cechIntersection, productOpens_eq_iInf]
  apply le_antisymm
  · exact le_inf (le_inf (iInf_le _ 0) (iInf_le _ 1)) (iInf_le _ 2)
  · apply le_iInf
    intro index
    fin_cases index
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right

theorem cechDifferential_component (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ) (cochain : (schemeCechComplex opens coefficient).X degree)
    (tuple : Fin (degree + 2) → Index) :
    cechCoordinate opens coefficient (degree + 1)
      ((schemeCechComplex opens coefficient).d degree (degree + 1) cochain) tuple =
    ∑ face : Fin (degree + 2), (-1 : ℤ) ^ face.val •
      coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin (degree + 1) =>
        Limits.Pi.π (opens ∘ tuple) (face.succAbove index))).op
          (cechCoordinate opens coefficient degree cochain (tuple ∘ face.succAbove)) := by
  have differential : (schemeCechComplex opens coefficient).d degree (degree + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk Index opens).cech).obj
          coefficient.presheaf) degree := by
    dsimp only [schemeCechComplex, schemeCechComplexFunctor, Functor.comp_obj,
      cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
      AlgebraicTopology.alternatingCofaceMapComplex_obj,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d]
    rfl
  have component : (schemeCechComplex opens coefficient).d degree (degree + 1) ≫
      Limits.Pi.π (fun tuple : Fin (degree + 2) → Index =>
        coefficient.presheaf.obj (op (cechIntersection opens (degree + 1) tuple))) tuple =
      ∑ face : Fin (degree + 2), (-1 : ℤ) ^ face.val •
        (Limits.Pi.π (fun tuple : Fin (degree + 1) → Index =>
          coefficient.presheaf.obj (op (cechIntersection opens degree tuple)))
            (tuple ∘ face.succAbove) ≫
          coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin (degree + 1) =>
            Limits.Pi.π (opens ∘ tuple) (face.succAbove index))).op) := by
    rw [differential]
    dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change (∑ face : Fin (degree + 2), (-1 : ℤ) ^ face.val •
      Limits.Pi.lift (fun tuple : Fin (degree + 2) → Index =>
        Limits.Pi.π (fun tuple : Fin (degree + 1) → Index =>
          coefficient.presheaf.obj (op (∏ᶜ (opens ∘ tuple))))
            (tuple ∘ face.succAbove) ≫
          coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin (degree + 1) =>
            Limits.Pi.π (opens ∘ tuple) (face.succAbove index))).op)) ≫
        Limits.Pi.π (fun tuple : Fin (degree + 2) → Index =>
          coefficient.presheaf.obj (op (∏ᶜ (opens ∘ tuple)))) tuple = _
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Limits.Pi.lift_comp_π]
    rfl
  let evaluation : ((schemeCechComplex opens coefficient).X degree ⟶
      coefficient.presheaf.obj (op (cechIntersection opens (degree + 1) tuple))) →+
        coefficient.presheaf.obj (op (cechIntersection opens (degree + 1) tuple)) :=
    { toFun := fun arrow => arrow cochain
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have evaluated := congrArg evaluation component
  rw [map_sum] at evaluated
  simp only [map_zsmul] at evaluated
  exact evaluated

theorem cechCoordinate_zero (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (degree : ℕ) (tuple : Fin (degree + 1) → Index) :
    cechCoordinate opens coefficient degree 0 tuple = 0 := by
  exact (Limits.Pi.π (fun tuple : Fin (degree + 1) → Index =>
    coefficient.presheaf.obj (op (cechIntersection opens degree tuple))) tuple).hom.map_zero

def standardOneCocycle (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (cochain : (schemeCechComplex opens coefficient).X 1)
    (cycle : (schemeCechComplex opens coefficient).d 1 2 cochain = 0) :
    SectionOneCocycle opens coefficient where
  value := cechOneCoordinate opens coefficient cochain
  cocycle := by
    intro first second third
    let tuple : Fin 3 → Index := ![first, second, third]
    have local_zero := congrArg (fun value =>
      cechCoordinate opens coefficient 2 value tuple) cycle
    rw [cechDifferential_component, cechCoordinate_zero, Fin.sum_univ_three] at local_zero
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      neg_one_zsmul, one_zsmul, Int.reduceNeg, Int.reducePow] at local_zero
    let canonical := cechIntersection opens 2 tuple
    let literal := (opens first ⊓ opens second) ⊓ opens third
    have intersection_eq : canonical = literal := cechIntersection_two opens tuple
    let to_second_third : canonical ⟶ opens second ⊓ opens third := homOfLE
      (intersection_eq.le.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    let to_first_third : canonical ⟶ opens first ⊓ opens third := homOfLE
      (intersection_eq.le.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    let to_first_second : canonical ⟶ opens first ⊓ opens second := homOfLE
      (intersection_eq.le.trans inf_le_left)
    have face_zero : tuple ∘ (0 : Fin 3).succAbove = ![second, third] := by
      funext index
      fin_cases index <;> rfl
    have face_one : tuple ∘ (1 : Fin 3).succAbove = ![first, third] := by
      funext index
      fin_cases index
      · rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (by decide)]
        rfl
      · rw [Function.comp_apply, Fin.succAbove_of_le_castSucc _ _ (by decide)]
        rfl
    have face_two : tuple ∘ (2 : Fin 3).succAbove = ![first, second] := by
      funext index
      fin_cases index <;>
        rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (by decide)] <;> rfl
    have restriction_zero := cechOneCoordinate_restriction_of_tuple_eq opens coefficient cochain
      (tuple ∘ (0 : Fin 3).succAbove) second third face_zero canonical
      (Limits.Pi.lift (fun index : Fin 2 =>
        Limits.Pi.π (opens ∘ tuple) ((0 : Fin 3).succAbove index)))
      to_second_third
    have restriction_one := cechOneCoordinate_restriction_of_tuple_eq opens coefficient cochain
      (tuple ∘ (1 : Fin 3).succAbove) first third face_one canonical
      (Limits.Pi.lift (fun index : Fin 2 =>
        Limits.Pi.π (opens ∘ tuple) ((1 : Fin 3).succAbove index)))
      to_first_third
    have restriction_two := cechOneCoordinate_restriction_of_tuple_eq opens coefficient cochain
      (tuple ∘ (2 : Fin 3).succAbove) first second face_two canonical
      (Limits.Pi.lift (fun index : Fin 2 =>
        Limits.Pi.π (opens ∘ tuple) ((2 : Fin 3).succAbove index)))
      to_first_second
    have actual_relation :
        coefficient.presheaf.map to_second_third.op
            (cechOneCoordinate opens coefficient cochain second third) -
        coefficient.presheaf.map to_first_third.op
            (cechOneCoordinate opens coefficient cochain first third) +
        coefficient.presheaf.map to_first_second.op
            (cechOneCoordinate opens coefficient cochain first second) = 0 := by
      rw [← restriction_zero, ← restriction_one, ← restriction_two]
      dsimp only [canonical]
      rw [sub_eq_add_neg]
      exact local_zero
    have transported := congrArg (fun value => coefficient.presheaf.map
      (eqToHom intersection_eq.symm).op value) actual_relation
    simp only [map_add, map_sub, map_zero] at transported
    rw [sectionRestriction_transport coefficient intersection_eq to_second_third
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      sectionRestriction_transport coefficient intersection_eq to_first_third
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right),
      sectionRestriction_transport coefficient intersection_eq to_first_second inf_le_left] at transported
    exact transported

def cechZeroOfSections (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (sections : ∀ index, coefficient.presheaf.obj (op (opens index))) :
    (schemeCechComplex opens coefficient).X 0 :=
  (productElementsEquiv (fun tuple : Fin 1 → Index =>
    coefficient.presheaf.obj (op (cechIntersection opens 0 tuple)))).symm
      (fun tuple => coefficient.presheaf.map (eqToHom (cechIntersection_zero opens tuple)).op
        (sections (tuple 0)))

theorem cechZeroOfSections_coordinate (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (sections : ∀ index, coefficient.presheaf.obj (op (opens index))) (index : Index) :
    cechZeroCoordinate opens coefficient (cechZeroOfSections opens coefficient sections) index =
      sections index := by
  have projection := congrFun (AddEquiv.apply_symm_apply
    (productElementsEquiv (fun tuple : Fin 1 → Index =>
      coefficient.presheaf.obj (op (cechIntersection opens 0 tuple))))
    (fun tuple => coefficient.presheaf.map (eqToHom (cechIntersection_zero opens tuple)).op
      (sections (tuple 0)))) (fun _ => index)
  rw [productElementsEquiv_apply] at projection
  dsimp only [cechZeroCoordinate, cechZeroOfSections]
  rw [projection, ← ConcreteCategory.comp_apply, ← coefficient.presheaf.map_comp]
  simp only [← op_comp, eqToHom_trans, eqToHom_refl, op_id, coefficient.presheaf.map_id]
  rfl

theorem cechOneCoordinate_ext (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    {first_cochain second_cochain : (schemeCechComplex opens coefficient).X 1}
    (same_coordinates : ∀ first second,
      cechOneCoordinate opens coefficient first_cochain first second =
        cechOneCoordinate opens coefficient second_cochain first second) :
    first_cochain = second_cochain := by
  apply (productElementsEquiv (fun tuple : Fin 2 → Index =>
    coefficient.presheaf.obj (op (cechIntersection opens 1 tuple)))).injective
  funext tuple
  obtain ⟨first, second, tuple_eq⟩ : ∃ first second, tuple = ![first, second] := by
    refine ⟨tuple 0, tuple 1, ?_⟩
    funext index
    fin_cases index <;> rfl
  subst tuple
  rw [productElementsEquiv_apply, productElementsEquiv_apply]
  apply (ConcreteCategory.bijective_of_isIso (coefficient.presheaf.map
    (eqToHom (cechIntersection_one opens ![first, second]).symm).op)).injective
  exact same_coordinates first second

theorem cechOneCoordinate_d_zero (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (cochain : (schemeCechComplex opens coefficient).X 0) (first second : Index) :
    cechOneCoordinate opens coefficient
        ((schemeCechComplex opens coefficient).d 0 1 cochain) first second =
      sectionRestriction coefficient inf_le_right (cechZeroCoordinate opens coefficient cochain second) -
        sectionRestriction coefficient inf_le_left (cechZeroCoordinate opens coefficient cochain first) := by
  let tuple : Fin 2 → Index := ![first, second]
  let canonical := cechIntersection opens 1 tuple
  have intersection_eq : canonical = opens first ⊓ opens second := cechIntersection_one opens tuple
  let to_first : canonical ⟶ opens first := homOfLE (intersection_eq.le.trans inf_le_left)
  let to_second : canonical ⟶ opens second := homOfLE (intersection_eq.le.trans inf_le_right)
  have face_zero : tuple ∘ (0 : Fin 2).succAbove = fun _ => second := by
    funext index
    fin_cases index
    rfl
  have face_one : tuple ∘ (1 : Fin 2).succAbove = fun _ => first := by
    funext index
    fin_cases index
    rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (by decide)]
    rfl
  have restriction_zero := cechZeroCoordinate_restriction opens coefficient cochain
    (tuple ∘ (0 : Fin 2).succAbove) canonical
    (Limits.Pi.lift (fun index : Fin 1 =>
      Limits.Pi.π (opens ∘ tuple) ((0 : Fin 2).succAbove index)))
    (Limits.Pi.lift (fun index : Fin 1 =>
      Limits.Pi.π (opens ∘ tuple) ((0 : Fin 2).succAbove index)) ≫
        eqToHom (cechIntersection_zero opens (tuple ∘ (0 : Fin 2).succAbove)))
  have restriction_one := cechZeroCoordinate_restriction opens coefficient cochain
    (tuple ∘ (1 : Fin 2).succAbove) canonical
    (Limits.Pi.lift (fun index : Fin 1 =>
      Limits.Pi.π (opens ∘ tuple) ((1 : Fin 2).succAbove index)))
    (Limits.Pi.lift (fun index : Fin 1 =>
      Limits.Pi.π (opens ∘ tuple) ((1 : Fin 2).succAbove index)) ≫
        eqToHom (cechIntersection_zero opens (tuple ∘ (1 : Fin 2).succAbove)))
  have face_zero_index : (tuple ∘ (0 : Fin 2).succAbove) 0 = second := rfl
  have face_one_index : (tuple ∘ (1 : Fin 2).succAbove) 0 = first := by
    rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (by decide)]
    rfl
  simp only at restriction_zero
  simp only at restriction_one
  have difference := cechDifferential_component opens coefficient 0 cochain tuple
  rw [Fin.sum_univ_two] at difference
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul] at difference
  have canonical_difference : cechCoordinate opens coefficient 1
      ((schemeCechComplex opens coefficient).d 0 1 cochain) tuple =
    coefficient.presheaf.map to_second.op (cechZeroCoordinate opens coefficient cochain second) -
      coefficient.presheaf.map to_first.op (cechZeroCoordinate opens coefficient cochain first) := by
    have second_restriction : coefficient.presheaf.map to_second.op
        (cechZeroCoordinate opens coefficient cochain second) =
      coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin 1 =>
        Limits.Pi.π (opens ∘ tuple) ((0 : Fin 2).succAbove index))).op
          (cechCoordinate opens coefficient 0 cochain (tuple ∘ (0 : Fin 2).succAbove)) := by
      exact restriction_zero.symm
    have first_restriction : coefficient.presheaf.map to_first.op
        (cechZeroCoordinate opens coefficient cochain first) =
      coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin 1 =>
        Limits.Pi.π (opens ∘ tuple) ((1 : Fin 2).succAbove index))).op
          (cechCoordinate opens coefficient 0 cochain (tuple ∘ (1 : Fin 2).succAbove)) := by
      exact restriction_one.symm
    rw [second_restriction, first_restriction, sub_eq_add_neg]
    exact difference
  have transported := congrArg (fun value => coefficient.presheaf.map
    (eqToHom intersection_eq.symm).op value) canonical_difference
  rw [map_sub, sectionRestriction_transport coefficient intersection_eq to_second inf_le_right,
    sectionRestriction_transport coefficient intersection_eq to_first inf_le_left] at transported
  exact transported

theorem standardCech_one_cycle_isBoundary [Finite Index]
    (opens : Index → scheme.Opens) (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque]
    (cochain : (schemeCechComplex opens coefficient).X 1)
    (cycle : (schemeCechComplex opens coefficient).d 1 2 cochain = 0) :
    ∃ preimage : (schemeCechComplex opens coefficient).X 0,
      (schemeCechComplex opens coefficient).d 0 1 preimage = cochain := by
  obtain ⟨sections, coboundary⟩ := (standardOneCocycle opens coefficient cochain cycle).exists_coboundary
  refine ⟨cechZeroOfSections opens coefficient sections, ?_⟩
  apply cechOneCoordinate_ext opens coefficient
  intro first second
  rw [cechOneCoordinate_d_zero, cechZeroOfSections_coordinate, cechZeroOfSections_coordinate]
  exact coboundary first second

theorem standardCech_exactAt_one [Finite Index] (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque] :
    (schemeCechComplex opens coefficient).ExactAt 1 := by
  apply (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mpr
  apply (ShortComplex.ab_exact_iff _).mpr
  exact standardCech_one_cycle_isBoundary opens coefficient

theorem standardCech_homology_one_isZero [Finite Index] (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) [coefficient.presheaf.IsFlasque] :
    IsZero ((schemeCechComplex opens coefficient).homology 1) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (standardCech_exactAt_one opens coefficient)

theorem noetherianQuasicoherentFlasqueTower_middle_isFlasque [IsLocallyNoetherian scheme]
    [scheme.IsSeparated] (cover : Scheme.AffineOpenCover.{u} scheme) [Finite cover.I₀]
    (coefficient : scheme.Modules) [coefficient.IsQuasicoherent] (stage : ℕ) :
    ((noetherianQuasicoherentFlasqueResolutionTower cover coefficient).middle stage).presheaf.IsFlasque := by
  let : Finite cover.openCover.I₀ := inferInstanceAs (Finite cover.I₀)
  let (index : cover.openCover.I₀) : IsAffineHom (cover.openCover.f index) :=
    affineSource_isAffineHom _
  exact flasqueResolutionTower_middle_isFlasque cover.openCover coefficient
    (fun current quasicoherent =>
      letI := quasicoherent
      noetherianLocalFlasqueEmbedding cover current) stage

end

end BondalThomsen.FiniteAffineCechFlasqueAcyclicity

