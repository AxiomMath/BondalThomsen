module

public import BondalThomsen.ProjectiveBundle.DivisorClasses
public import BondalThomsen.Matroid.ColumnPermutationRigidity
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Finsupp.Basic

@[expose] public section

namespace BondalThomsen.ProjectiveBundle

open Module

variable {rows baseDimension columns : ℕ}

def augmentedRayColumn (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (row : Fin rows) (column : Option (Fin columns)) : ℤ := column.elim 0 (matrix row)

def baseRayClassVector (row : Fin rows) : (Fin rows ⊕ Unit) → ℤ := Pi.single (.inl row) 1

def fiberRayClassVector (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (column : Option (Fin columns)) : (Fin rows ⊕ Unit) → ℤ :=
  Sum.elim (fun row => -augmentedRayColumn matrix row column) (fun _ => 1)

section Coordinates

variable (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)

@[simp] theorem raySingle_apply_label (label other : RayLabel rows baseDimension columns) :
    Finsupp.single (labelRay matrix base_positive fiber_positive label) (1 : ℤ)
      (labelRay matrix base_positive fiber_positive other) = if label = other then 1 else 0 := by
  classical
  simp only [Finsupp.single_apply, (labelRay_bijective matrix base_positive fiber_positive).1.eq_iff]

theorem divisorClassEquiv_single_base (row : Fin rows) (position : Option (Fin baseDimension)) :
    divisorClassEquiv matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).invariantRayDivisorClass
        (Finsupp.single (labelRay matrix base_positive fiber_positive (.inl (row, position))) 1)) =
      baseRayClassVector row := by
  classical
  rw [divisorClassEquiv_mk]
  ext coordinate
  cases coordinate with
  | inl other =>
    rw [residualCoordinates_base]
    cases position with
    | none => simp [raySingle_apply_label, baseRayClassVector, Pi.single_apply, eq_comm]
    | some position =>
      by_cases same : row = other
      · subst other
        simp [raySingle_apply_label, baseRayClassVector, eq_comm]
      · simp [raySingle_apply_label, baseRayClassVector, same,
          Ne.symm same]
  | inr fiber_index =>
    cases fiber_index
    rw [residualCoordinates_fiber]
    simp [raySingle_apply_label, baseRayClassVector]

theorem divisorClassEquiv_single_fiber (column : Option (Fin columns)) :
    divisorClassEquiv matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).invariantRayDivisorClass
        (Finsupp.single (labelRay matrix base_positive fiber_positive (.inr column)) 1)) =
      fiberRayClassVector matrix column := by
  classical
  rw [divisorClassEquiv_mk]
  ext coordinate
  cases coordinate with
  | inl row =>
    rw [residualCoordinates_base]
    cases column <;> simp [raySingle_apply_label, fiberRayClassVector, augmentedRayColumn]
  | inr fiber_index =>
    cases fiber_index
    rw [residualCoordinates_fiber]
    cases column <;> simp [raySingle_apply_label, fiberRayClassVector]

end Coordinates

section Transport

variable (first second : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)

noncomputable def rayDivisorClassMap
    (rays : (fan (baseDimension := baseDimension) second).Ray ≃
      (fan (baseDimension := baseDimension) first).Ray)
    (principal_compatible : (fan (baseDimension := baseDimension) second).principalRayDivisor.range ≤
      AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
        (fan (baseDimension := baseDimension) first).principalRayDivisor.range) :
    (fan (baseDimension := baseDimension) second).InvariantRayDivisorClass →+
      (fan (baseDimension := baseDimension) first).InvariantRayDivisorClass :=
  QuotientAddGroup.map _ _ (Finsupp.domCongr rays).toAddMonoidHom principal_compatible

@[simp] theorem rayDivisorClassMap_single
    (rays : (fan (baseDimension := baseDimension) second).Ray ≃
      (fan (baseDimension := baseDimension) first).Ray)
    (principal_compatible : (fan (baseDimension := baseDimension) second).principalRayDivisor.range ≤
      AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
        (fan (baseDimension := baseDimension) first).principalRayDivisor.range)
    (ray : (fan (baseDimension := baseDimension) second).Ray) :
    rayDivisorClassMap first second rays principal_compatible
      ((fan (baseDimension := baseDimension) second).invariantRayDivisorClass (Finsupp.single ray 1)) =
        (fan (baseDimension := baseDimension) first).invariantRayDivisorClass
          (Finsupp.single (rays ray) 1) := by
  change QuotientAddGroup.map _ _ _ _ (QuotientAddGroup.mk _) = _
  rw [QuotientAddGroup.map_mk]
  change (fan (baseDimension := baseDimension) first).invariantRayDivisorClass
    ((Finsupp.domCongr rays) (Finsupp.single ray 1)) = _
  rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]

noncomputable def rayClassCoordinateMap
    (rays : (fan (baseDimension := baseDimension) second).Ray ≃
      (fan (baseDimension := baseDimension) first).Ray)
    (principal_compatible : (fan (baseDimension := baseDimension) second).principalRayDivisor.range ≤
      AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
        (fan (baseDimension := baseDimension) first).principalRayDivisor.range) :
    ((Fin rows ⊕ Unit) → ℤ) →+ ((Fin rows ⊕ Unit) → ℤ) :=
  (divisorClassEquiv first base_positive fiber_positive).toAddMonoidHom.comp
    ((rayDivisorClassMap first second rays principal_compatible).comp
      (divisorClassEquiv second base_positive fiber_positive).symm.toAddMonoidHom)

def distinguishedClassAction (permutation : Equiv.Perm (Fin rows))
    (translation : Fin rows → ℤ) :
    ((Fin rows ⊕ Unit) → ℤ) →+ ((Fin rows ⊕ Unit) → ℤ) where
  toFun vector := Sum.elim
    (fun row => vector (.inl (permutation.symm row)) + vector (.inr ()) * translation row)
    (fun _ => vector (.inr ()))
  map_zero' := by ext coordinate; cases coordinate <;> simp
  map_add' first_vector second_vector := by
    ext coordinate
    cases coordinate <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]; ring

theorem rayClassCoordinateMap_eq_distinguishedClassAction
    (rays : (fan (baseDimension := baseDimension) second).Ray ≃
      (fan (baseDimension := baseDimension) first).Ray)
    (principal_compatible : (fan (baseDimension := baseDimension) second).principalRayDivisor.range ≤
      AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
        (fan (baseDimension := baseDimension) first).principalRayDivisor.range)
    (permutation : Equiv.Perm (Fin rows)) (translation : Fin rows → ℤ)
    (base_classes : ∀ row, rayClassCoordinateMap first second base_positive fiber_positive
      rays principal_compatible (baseRayClassVector row) = baseRayClassVector (permutation row))
    (fiber_class : rayClassCoordinateMap first second base_positive fiber_positive rays principal_compatible
      (Pi.single (.inr ()) 1) = Sum.elim translation (fun _ => 1)) :
    rayClassCoordinateMap first second base_positive fiber_positive rays principal_compatible =
      distinguishedClassAction permutation translation := by
  classical
  apply AddMonoidHom.toIntLinearMap_injective
  apply (Pi.basisFun ℤ (Fin rows ⊕ Unit)).ext
  intro coordinate
  simp only [Pi.basisFun_apply, AddMonoidHom.coe_toIntLinearMap]
  cases coordinate with
  | inl row =>
    rw [show Pi.single (.inl row) (1 : ℤ) = baseRayClassVector row from rfl, base_classes]
    ext target
    cases target <;>
      simp [distinguishedClassAction, baseRayClassVector, Pi.single_apply,
        ← permutation.symm_apply_eq, eq_comm]
  | inr fiber_index =>
    cases fiber_index
    rw [fiber_class]
    ext target
    cases target <;> simp [distinguishedClassAction]

theorem rayClassCoordinateMap_single
    (rays : (fan (baseDimension := baseDimension) second).Ray ≃
      (fan (baseDimension := baseDimension) first).Ray)
    (principal_compatible : (fan (baseDimension := baseDimension) second).principalRayDivisor.range ≤
      AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
        (fan (baseDimension := baseDimension) first).principalRayDivisor.range)
    (ray : (fan (baseDimension := baseDimension) second).Ray) :
    rayClassCoordinateMap first second base_positive fiber_positive rays principal_compatible
      (divisorClassEquiv second base_positive fiber_positive
        ((fan (baseDimension := baseDimension) second).invariantRayDivisorClass (Finsupp.single ray 1))) =
      divisorClassEquiv first base_positive fiber_positive
        ((fan (baseDimension := baseDimension) first).invariantRayDivisorClass (Finsupp.single (rays ray) 1)) := by
  change divisorClassEquiv first base_positive fiber_positive
    (rayDivisorClassMap first second rays principal_compatible
      ((divisorClassEquiv second base_positive fiber_positive).symm
        ((divisorClassEquiv second base_positive fiber_positive) _))) = _
  rw [AddEquiv.symm_apply_apply, rayDivisorClassMap_single]

theorem single_ray_class_fiber_degree (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (label : RayLabel rows baseDimension columns) :
    divisorClassEquiv matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).invariantRayDivisorClass
        (Finsupp.single (labelRay matrix base_positive fiber_positive label) 1)) (.inr ()) =
      Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1) label := by
  classical
  cases label with
  | inl label =>
    rw [divisorClassEquiv_single_base]
    simp [baseRayClassVector]
  | inr column => rw [divisorClassEquiv_single_fiber]; rfl

theorem exists_fiber_ray_permutation
    (rays : (fan (baseDimension := baseDimension) second).Ray ≃
      (fan (baseDimension := baseDimension) first).Ray)
    (principal_compatible : (fan (baseDimension := baseDimension) second).principalRayDivisor.range ≤
      AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
        (fan (baseDimension := baseDimension) first).principalRayDivisor.range)
    (permutation : Equiv.Perm (Fin rows)) (translation : Fin rows → ℤ)
    (action : rayClassCoordinateMap first second base_positive fiber_positive rays principal_compatible =
      distinguishedClassAction permutation translation) :
    ∃ columns_permutation : Equiv.Perm (Option (Fin columns)), ∀ column,
      rays (labelRay second base_positive fiber_positive (.inr column)) =
        labelRay first base_positive fiber_positive (.inr (columns_permutation column)) := by
  classical
  let labels := ((rayEquiv second base_positive fiber_positive).trans rays).trans
    (rayEquiv first base_positive fiber_positive).symm
  have label_image : ∀ label,
      rays (labelRay second base_positive fiber_positive label) =
        labelRay first base_positive fiber_positive (labels label) := by
    intro label
    exact ((rayEquiv first base_positive fiber_positive).apply_symm_apply _).symm
  have degree_preserved : ∀ label,
      Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1) (labels label) =
        Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1) label := by
    intro label
    have mapped := rayClassCoordinateMap_single first second base_positive fiber_positive rays
      principal_compatible (labelRay second base_positive fiber_positive label)
    rw [action, label_image] at mapped
    have degree := congrFun mapped (.inr ())
    change divisorClassEquiv second base_positive fiber_positive
      ((fan (baseDimension := baseDimension) second).invariantRayDivisorClass
        (Finsupp.single (labelRay second base_positive fiber_positive label) 1)) (.inr ()) = _ at degree
    rw [single_ray_class_fiber_degree, single_ray_class_fiber_degree] at degree
    exact degree.symm
  let fiber_map : Option (Fin columns) → Option (Fin columns) := fun column =>
    Sum.elim (fun _ => none) id (labels (.inr column))
  have fiber_image : ∀ column, labels (.inr column) = .inr (fiber_map column) := by
    intro column
    have degree := degree_preserved (.inr column)
    cases image : labels (.inr column) with
    | inl label => simp only [image, Sum.elim_inl, Sum.elim_inr] at degree; omega
    | inr target => simp only [fiber_map, image, Sum.elim_inr, id_eq]
  have fiber_injective : Function.Injective fiber_map := by
    intro first_column second_column same
    have same_labels : labels (.inr first_column) = labels (.inr second_column) := by
      rw [fiber_image, fiber_image, same]
    exact Sum.inr.inj (labels.injective same_labels)
  have fiber_surjective : Function.Surjective fiber_map := by
    intro target
    obtain ⟨label, image⟩ := labels.surjective (.inr target)
    have degree := degree_preserved label
    rw [image] at degree
    cases label with
    | inl label => simp only [Sum.elim_inl, Sum.elim_inr] at degree; omega
    | inr column =>
      refine ⟨column, ?_⟩
      rw [fiber_image] at image
      exact Sum.inr.inj image
  let columns_permutation := Equiv.ofBijective fiber_map ⟨fiber_injective, fiber_surjective⟩
  refine ⟨columns_permutation, ?_⟩
  intro column
  rw [label_image, fiber_image]
  rfl

theorem augmentedRayColumn_matching_of_ray_classes
    (rays : (fan (baseDimension := baseDimension) second).Ray ≃
      (fan (baseDimension := baseDimension) first).Ray)
    (principal_compatible : (fan (baseDimension := baseDimension) second).principalRayDivisor.range ≤
      AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
        (fan (baseDimension := baseDimension) first).principalRayDivisor.range)
    (permutation : Equiv.Perm (Fin rows)) (translation : Fin rows → ℤ)
    (base_classes : ∀ row, rayClassCoordinateMap first second base_positive fiber_positive
      rays principal_compatible (baseRayClassVector row) = baseRayClassVector (permutation row))
    (fiber_class : rayClassCoordinateMap first second base_positive fiber_positive rays principal_compatible
      (Pi.single (.inr ()) 1) = Sum.elim translation (fun _ => 1)) :
    ∃ columns_permutation : Equiv.Perm (Option (Fin columns)),
      (∀ column, rays (labelRay second base_positive fiber_positive (.inr column)) =
        labelRay first base_positive fiber_positive (.inr (columns_permutation column))) ∧
      ∀ row column, augmentedRayColumn second row column =
        augmentedRayColumn first (permutation row) (columns_permutation column) +
          translation (permutation row) := by
  have action := rayClassCoordinateMap_eq_distinguishedClassAction first second
    base_positive fiber_positive rays principal_compatible permutation translation base_classes fiber_class
  obtain ⟨columns_permutation, ray_images⟩ := exists_fiber_ray_permutation first second
    base_positive fiber_positive rays principal_compatible permutation translation action
  refine ⟨columns_permutation, ray_images, ?_⟩
  intro row column
  have mapped := rayClassCoordinateMap_single first second base_positive fiber_positive rays
    principal_compatible (labelRay second base_positive fiber_positive (.inr column))
  rw [action, ray_images, divisorClassEquiv_single_fiber, divisorClassEquiv_single_fiber] at mapped
  have entry := congrFun mapped (.inl (permutation row))
  change -augmentedRayColumn second (permutation.symm (permutation row)) column +
    1 * translation (permutation row) =
      -augmentedRayColumn first (permutation row) (columns_permutation column) at entry
  rw [Equiv.symm_apply_apply, one_mul] at entry
  omega

theorem augmentedRayColumn_permutation_of_ray_classes
    (first_nonnegative : ∀ row column, 0 ≤ first row column)
    (second_nonnegative : ∀ row column, 0 ≤ second row column)
    (rays : (fan (baseDimension := baseDimension) second).Ray ≃
      (fan (baseDimension := baseDimension) first).Ray)
    (principal_compatible : (fan (baseDimension := baseDimension) second).principalRayDivisor.range ≤
      AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
        (fan (baseDimension := baseDimension) first).principalRayDivisor.range)
    (permutation : Equiv.Perm (Fin rows)) (translation : Fin rows → ℤ)
    (base_classes : ∀ row, rayClassCoordinateMap first second base_positive fiber_positive
      rays principal_compatible (baseRayClassVector row) = baseRayClassVector (permutation row))
    (fiber_class : rayClassCoordinateMap first second base_positive fiber_positive rays principal_compatible
      (Pi.single (.inr ()) 1) = Sum.elim translation (fun _ => 1)) :
    translation = 0 ∧ ∃ columns_permutation : Equiv.Perm (Option (Fin columns)),
      (∀ column, rays (labelRay second base_positive fiber_positive (.inr column)) =
        labelRay first base_positive fiber_positive (.inr (columns_permutation column))) ∧
      ∀ row column, augmentedRayColumn second row column =
        augmentedRayColumn first (permutation row) (columns_permutation column) := by
  obtain ⟨columns_permutation, ray_images, matching⟩ :=
    augmentedRayColumn_matching_of_ray_classes first second base_positive fiber_positive
      rays principal_compatible permutation translation base_classes fiber_class
  have first_aug_nonnegative : ∀ row column, 0 ≤ augmentedRayColumn first row column := by
    intro row column; cases column <;> simp [augmentedRayColumn, first_nonnegative]
  have second_aug_nonnegative : ∀ row column, 0 ≤ augmentedRayColumn second row column := by
    intro row column; cases column <;> simp [augmentedRayColumn, second_nonnegative]
  have translation_zero := BondalThomsen.zero_column_translation_eq_zero
    (augmentedRayColumn first) (augmentedRayColumn second) first_aug_nonnegative second_aug_nonnegative
    ⟨none, fun _ => rfl⟩ ⟨none, fun _ => rfl⟩ permutation columns_permutation
    (fun row => translation (permutation row)) matching
  have zero : translation = 0 := by
    funext row
    have value := congrFun translation_zero (permutation.symm row)
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using value
  refine ⟨zero, columns_permutation, ray_images, ?_⟩
  intro row column
  simpa only [zero, Pi.zero_apply, add_zero] using matching row column

end Transport

section FixedWeight

variable {ones : ℕ}

theorem augmentedPermutationEquivalent_of_actual_ray_classes
    (first second : BondalThomsen.FixedWeightMatrix rows columns ones)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (rays : (fan (baseDimension := baseDimension) (fixedWeightTwist second)).Ray ≃
      (fan (baseDimension := baseDimension) (fixedWeightTwist first)).Ray)
    (principal_compatible :
      (fan (baseDimension := baseDimension) (fixedWeightTwist second)).principalRayDivisor.range ≤
        AddSubgroup.comap (Finsupp.domCongr rays).toAddMonoidHom
          (fan (baseDimension := baseDimension) (fixedWeightTwist first)).principalRayDivisor.range)
    (permutation : Equiv.Perm (Fin rows)) (translation : Fin rows → ℤ)
    (base_classes : ∀ row, rayClassCoordinateMap (fixedWeightTwist first)
      (fixedWeightTwist second) base_positive fiber_positive rays principal_compatible
        (baseRayClassVector row) = baseRayClassVector (permutation row))
    (fiber_class : rayClassCoordinateMap (fixedWeightTwist first)
      (fixedWeightTwist second) base_positive fiber_positive rays principal_compatible
        (Pi.single (.inr ()) 1) = Sum.elim translation (fun _ => 1)) :
    BondalThomsen.AugmentedPermutationEquivalent first second := by
  have first_nonnegative := fixedWeightTwist_nonnegative first
  have second_nonnegative := fixedWeightTwist_nonnegative second
  obtain ⟨_, columns_permutation, _, matching⟩ :=
    augmentedRayColumn_permutation_of_ray_classes (fixedWeightTwist first)
      (fixedWeightTwist second) base_positive fiber_positive first_nonnegative
        second_nonnegative rays principal_compatible permutation translation base_classes fiber_class
  refine ⟨permutation, columns_permutation, ?_⟩
  ext row column
  have adapter : ∀ matrix : BondalThomsen.FixedWeightMatrix rows columns ones, ∀ row column,
      augmentedRayColumn (fixedWeightTwist matrix) row column =
        BondalThomsen.augmentedColumnMatrix matrix row column := by
    intro matrix row column
    cases column <;> rfl
  simpa only [adapter, Matrix.submatrix_apply] using matching row column

end FixedWeight

end BondalThomsen.ProjectiveBundle
