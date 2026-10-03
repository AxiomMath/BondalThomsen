module

public import BondalThomsen.Rarity.Counting
public import BondalThomsen.DeepFan.Coordinates
public import BondalThomsen.Matroid.ColumnPermutationRigidity
public import BondalThomsen.Ports.TauCeti.Algebra.Module.Primitive
public import Mathlib.LinearAlgebra.Basis.Prod

@[expose] public section

namespace BondalThomsen.ProjectiveBundle

open Finset Module

variable {rows baseDimension columns : ℕ}

abbrev Coordinate (rows baseDimension columns : ℕ) :=
  (Fin rows × Fin baseDimension) ⊕ Fin columns

abbrev Lattice (rows baseDimension columns : ℕ) :=
  Coordinate rows baseDimension columns → ℤ

noncomputable def standardBasis (rows baseDimension columns : ℕ) :
    Basis (Coordinate rows baseDimension columns) ℤ (Lattice rows baseDimension columns) :=
  Pi.basisFun ℤ _

def basePositive (factor : Fin rows) (position : Fin baseDimension) :
    Lattice rows baseDimension columns := Pi.single (.inl (factor, position)) 1

def baseNegative (matrix : Matrix (Fin rows) (Fin columns) ℤ) (factor : Fin rows) :
    Lattice rows baseDimension columns :=
  Sum.elim (fun coordinate => if coordinate.1 = factor then -1 else 0)
    (fun column => matrix factor column)

def fiberPositive (column : Fin columns) : Lattice rows baseDimension columns :=
  Pi.single (.inr column) 1

def fiberNegative : Lattice rows baseDimension columns :=
  Sum.elim (fun _ => 0) (fun _ => -1)

def rowTwist (matrix : Matrix (Fin rows) (Fin columns) ℤ) (factor : Fin rows) :
    Lattice rows baseDimension columns := Sum.elim (fun _ => 0) (matrix factor)

theorem base_ray_relation (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (factor : Fin rows) :
    baseNegative (baseDimension := baseDimension) matrix factor +
      ∑ position : Fin baseDimension, basePositive factor position = rowTwist matrix factor := by
  ext coordinate
  cases coordinate with
  | inl coordinate =>
    rcases coordinate with ⟨other_factor, position⟩
    by_cases same : other_factor = factor
    · subst other_factor
      simp [baseNegative, basePositive, rowTwist, Pi.single_apply]
    · simp [baseNegative, basePositive, rowTwist, same]
  | inr column => simp [baseNegative, basePositive, rowTwist]

theorem fiber_ray_relation :
    (fiberNegative : Lattice rows baseDimension columns) +
      ∑ column : Fin columns, fiberPositive column = 0 := by
  ext coordinate
  cases coordinate with
  | inl coordinate => simp [fiberNegative, fiberPositive]
  | inr column => simp [fiberNegative, fiberPositive, Pi.single_apply]

theorem rowTwist_eq_sum (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (factor : Fin rows) :
    (rowTwist matrix factor : Lattice rows baseDimension columns) =
      ∑ column : Fin columns, matrix factor column • fiberPositive column := by
  ext coordinate
  cases coordinate with
  | inl coordinate => simp [rowTwist, fiberPositive]
  | inr column => simp [rowTwist, fiberPositive, Pi.single_apply]

theorem basePositive_isPrimitive (factor : Fin rows) (position : Fin baseDimension) :
    TauCeti.IsPrimitive (basePositive factor position : Lattice rows baseDimension columns) := by
  simpa [standardBasis, Pi.basisFun_apply, basePositive] using
    (standardBasis rows baseDimension columns).isPrimitive (.inl (factor, position))

theorem fiberPositive_isPrimitive (column : Fin columns) :
    TauCeti.IsPrimitive (fiberPositive column : Lattice rows baseDimension columns) := by
  simpa [standardBasis, Pi.basisFun_apply, fiberPositive] using
    (standardBasis rows baseDimension columns).isPrimitive (.inr column)

theorem baseNegative_isPrimitive (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (factor : Fin rows) (positive : 0 < baseDimension) :
    TauCeti.IsPrimitive (baseNegative matrix factor : Lattice rows baseDimension columns) := by
  apply TauCeti.isPrimitive_def.mpr
  refine ⟨-(LinearMap.proj (.inl (factor, ⟨0, positive⟩))), ?_⟩
  simp [baseNegative]

theorem fiberNegative_isPrimitive (positive : 0 < columns) :
    TauCeti.IsPrimitive (fiberNegative : Lattice rows baseDimension columns) := by
  apply TauCeti.isPrimitive_def.mpr
  refine ⟨-(LinearMap.proj (.inr (⟨0, positive⟩ : Fin columns))), ?_⟩
  simp [fiberNegative]

def projectiveSwitch {Index : Type*} [DecidableEq Index] (removed : Option Index) :
    (Index → ℤ) ≃ₗ[ℤ] (Index → ℤ) :=
  match removed with
  | none => LinearEquiv.refl ℤ _
  | some selected => LinearEquiv.ofInvolutive
      { toFun := fun vector index =>
          if index = selected then -vector selected else vector index - vector selected
        map_add' := by
          intro first second
          ext index
          by_cases same : index = selected <;> simp [same] <;> ring
        map_smul' := by
          intro scalar vector
          ext index
          by_cases same : index = selected <;> simp [same]; ring }
      (by
        intro vector
        ext index
        by_cases same : index = selected <;> simp [same])

@[simp] theorem projectiveSwitch_none {Index : Type*} [DecidableEq Index]
    (vector : Index → ℤ) : projectiveSwitch none vector = vector := rfl

@[simp] theorem projectiveSwitch_involutive {Index : Type*} [DecidableEq Index]
    (removed : Option Index) (vector : Index → ℤ) :
    projectiveSwitch removed (projectiveSwitch removed vector) = vector := by
  cases removed with
  | none => rfl
  | some selected =>
    ext index
    by_cases same : index = selected <;> simp [projectiveSwitch, same]

theorem projectiveSwitch_single_other {Index : Type*} [DecidableEq Index]
    (selected index : Index) (different : index ≠ selected) :
    projectiveSwitch (some selected) (Pi.single index 1) = Pi.single index 1 := by
  ext coordinate
  by_cases same : coordinate = selected
  · subst coordinate
    simp [projectiveSwitch, Ne.symm different]
  · simp [projectiveSwitch, Pi.single_apply, same, Ne.symm different]

structure ConeChoice (rows baseDimension columns : ℕ) where
  base : Fin rows → Option (Fin baseDimension)
  fiber : Option (Fin columns)

def blockSwitch (choice : ConeChoice rows baseDimension columns) :
    Lattice rows baseDimension columns ≃ₗ[ℤ] Lattice rows baseDimension columns :=
  LinearEquiv.ofInvolutive
    { toFun := fun vector => Sum.elim
        (fun coordinate => projectiveSwitch (choice.base coordinate.1)
          (fun position => vector (.inl (coordinate.1, position))) coordinate.2)
        (fun column => projectiveSwitch choice.fiber (fun column => vector (.inr column)) column)
      map_add' := by
        intro first second
        ext coordinate
        cases coordinate with
        | inl coordinate => exact congrFun (map_add (projectiveSwitch _) _ _) coordinate.2
        | inr column => exact congrFun (map_add (projectiveSwitch _) _ _) column
      map_smul' := by
        intro scalar vector
        ext coordinate
        cases coordinate with
        | inl coordinate => exact congrFun (map_smul (projectiveSwitch _) scalar _) coordinate.2
        | inr column => exact congrFun (map_smul (projectiveSwitch _) scalar _) column }
    (by
      intro vector
      ext coordinate
      cases coordinate with
      | inl coordinate =>
        exact congrFun (projectiveSwitch_involutive (choice.base coordinate.1)
          (fun position => vector (.inl (coordinate.1, position)))) coordinate.2
      | inr column =>
        exact congrFun (projectiveSwitch_involutive choice.fiber
          (fun column => vector (.inr column))) column)

def selectedBaseCoordinate (choice : ConeChoice rows baseDimension columns)
    (vector : Lattice rows baseDimension columns) (factor : Fin rows) : ℤ :=
  match choice.base factor with
  | none => 0
  | some position => vector (.inl (factor, position))

def twistShear (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    Lattice rows baseDimension columns ≃ₗ[ℤ] Lattice rows baseDimension columns where
  toFun vector := Sum.elim (fun coordinate => vector (.inl coordinate))
    (fun column => vector (.inr column) -
      ∑ factor : Fin rows, selectedBaseCoordinate choice vector factor * matrix factor column)
  invFun vector := Sum.elim (fun coordinate => vector (.inl coordinate))
    (fun column => vector (.inr column) +
      ∑ factor : Fin rows, selectedBaseCoordinate choice vector factor * matrix factor column)
  left_inv vector := by
    ext coordinate
    cases coordinate with
    | inl coordinate => rfl
    | inr column => simp [selectedBaseCoordinate]
  right_inv vector := by
    ext coordinate
    cases coordinate with
    | inl coordinate => rfl
    | inr column => simp [selectedBaseCoordinate]
  map_add' first second := by
    ext coordinate
    cases coordinate with
    | inl coordinate => rfl
    | inr column =>
      simp only [Sum.elim_inr, Pi.add_apply]
      have coordinate_add : ∀ factor, selectedBaseCoordinate choice (first + second) factor =
          selectedBaseCoordinate choice first factor + selectedBaseCoordinate choice second factor := by
        intro factor
        cases selected_eq : choice.base factor <;> simp [selectedBaseCoordinate, selected_eq]
      simp only [coordinate_add, add_mul, Finset.sum_add_distrib]
      ring
  map_smul' scalar vector := by
    ext coordinate
    cases coordinate with
    | inl coordinate => rfl
    | inr column =>
      simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
      have coordinate_smul : ∀ factor, selectedBaseCoordinate choice (scalar • vector) factor =
          scalar * selectedBaseCoordinate choice vector factor := by
        intro factor
        cases selected_eq : choice.base factor <;>
          simp [selectedBaseCoordinate, selected_eq]
      simp only [coordinate_smul, mul_assoc, ← Finset.mul_sum, RingHom.id_apply]
      ring

def coneEquiv (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    Lattice rows baseDimension columns ≃ₗ[ℤ] Lattice rows baseDimension columns :=
  (blockSwitch choice).trans (twistShear matrix choice)

noncomputable def coneBasis (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    Basis (Coordinate rows baseDimension columns) ℤ (Lattice rows baseDimension columns) :=
  (standardBasis rows baseDimension columns).map (coneEquiv matrix choice)

@[simp] theorem blockSwitch_base_coordinate (choice : ConeChoice rows baseDimension columns)
    (vector : Lattice rows baseDimension columns) (factor : Fin rows)
    (position : Fin baseDimension) :
    blockSwitch choice vector (.inl (factor, position)) =
      projectiveSwitch (choice.base factor)
        (fun position => vector (.inl (factor, position))) position := rfl

@[simp] theorem blockSwitch_fiber_coordinate (choice : ConeChoice rows baseDimension columns)
    (vector : Lattice rows baseDimension columns) (column : Fin columns) :
    blockSwitch choice vector (.inr column) =
      projectiveSwitch choice.fiber (fun column => vector (.inr column)) column := rfl

theorem blockSwitch_base_selected (choice : ConeChoice rows baseDimension columns)
    (factor : Fin rows) (position : Fin baseDimension)
    (selected : choice.base factor = some position) :
    blockSwitch choice (basePositive factor position) = baseNegative 0 factor := by
  ext coordinate
  cases coordinate with
  | inl coordinate =>
    rcases coordinate with ⟨other_factor, other_position⟩
    by_cases same_factor : other_factor = factor
    · subst other_factor
      simp [basePositive, baseNegative, selected, projectiveSwitch, Pi.single_apply]
    · cases other_selected : choice.base other_factor <;>
        simp [basePositive, baseNegative, other_selected, projectiveSwitch, same_factor]
  | inr column =>
    change projectiveSwitch choice.fiber (fun column =>
      basePositive factor position (.inr column)) column = 0
    have zero_eq : (fun column => basePositive (columns := columns) factor position (.inr column)) =
        (0 : Fin columns → ℤ) := by ext column; simp [basePositive]
    rw [zero_eq, map_zero]
    rfl

theorem blockSwitch_base_unselected (choice : ConeChoice rows baseDimension columns)
    (factor : Fin rows) (position : Fin baseDimension)
    (unselected : choice.base factor ≠ some position) :
    blockSwitch choice (basePositive factor position) = basePositive factor position := by
  ext coordinate
  cases coordinate with
  | inl coordinate =>
    rcases coordinate with ⟨other_factor, other_position⟩
    by_cases same_factor : other_factor = factor
    · subst other_factor
      cases selected : choice.base factor with
      | none => simp [basePositive, selected, projectiveSwitch, Pi.single_apply]
      | some selected_position =>
        have distinct : position ≠ selected_position := by
          intro equality
          subst selected_position
          exact unselected selected
        simp [basePositive, selected, projectiveSwitch, Pi.single_apply, Ne.symm distinct]
        intro same
        subst other_position
        exact Ne.symm distinct
    · cases other_selected : choice.base other_factor <;>
        simp [basePositive, other_selected, projectiveSwitch, same_factor]
  | inr column =>
    change projectiveSwitch choice.fiber (fun column =>
      basePositive factor position (.inr column)) column = basePositive factor position (.inr column)
    have zero_eq : (fun column => basePositive (columns := columns) factor position (.inr column)) =
        (0 : Fin columns → ℤ) := by ext column; simp [basePositive]
    rw [zero_eq, map_zero]
    simp [basePositive]

theorem twistShear_base_negative (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (factor : Fin rows)
    (position : Fin baseDimension) (selected : choice.base factor = some position) :
    twistShear matrix choice (baseNegative 0 factor) = baseNegative matrix factor := by
  ext coordinate
  cases coordinate with
  | inl coordinate => rfl
  | inr column =>
    have coefficients : ∀ other_factor,
        selectedBaseCoordinate choice (baseNegative 0 factor) other_factor =
          if other_factor = factor then -1 else 0 := by
      intro other_factor
      by_cases same_factor : other_factor = factor
      · subst other_factor
        simp [selectedBaseCoordinate, baseNegative, selected]
      · cases other_selected : choice.base other_factor <;>
          simp [selectedBaseCoordinate, baseNegative, other_selected, same_factor]
    change 0 - ∑ other_factor,
      selectedBaseCoordinate choice (baseNegative 0 factor) other_factor * matrix other_factor column = _
    simp only [coefficients]
    simp [baseNegative]

theorem twistShear_base_positive (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (factor : Fin rows)
    (position : Fin baseDimension) (unselected : choice.base factor ≠ some position) :
    twistShear matrix choice (basePositive factor position) = basePositive factor position := by
  ext coordinate
  cases coordinate with
  | inl coordinate => rfl
  | inr column =>
    have coefficients : ∀ other_factor,
        selectedBaseCoordinate choice (basePositive factor position) other_factor = 0 := by
      intro other_factor
      cases other_selected : choice.base other_factor with
      | none => simp [selectedBaseCoordinate, other_selected]
      | some other_position =>
        by_cases same_factor : other_factor = factor
        · subst other_factor
          have distinct : other_position ≠ position := by
            intro equality
            subst other_position
            exact unselected other_selected
          simp [selectedBaseCoordinate, basePositive, other_selected, distinct]
        · simp [selectedBaseCoordinate, basePositive, other_selected, same_factor]
    simp [twistShear, coefficients]

theorem coneBasis_base_selected (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (factor : Fin rows)
    (position : Fin baseDimension) (selected : choice.base factor = some position) :
    coneBasis matrix choice (.inl (factor, position)) = baseNegative matrix factor := by
  rw [coneBasis, Basis.map_apply, standardBasis, Pi.basisFun_apply]
  change twistShear matrix choice (blockSwitch choice (basePositive factor position)) = _
  rw [blockSwitch_base_selected choice factor position selected]
  exact twistShear_base_negative matrix choice factor position selected

theorem coneBasis_base_unselected (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (factor : Fin rows)
    (position : Fin baseDimension) (unselected : choice.base factor ≠ some position) :
    coneBasis matrix choice (.inl (factor, position)) = basePositive factor position := by
  rw [coneBasis, Basis.map_apply, standardBasis, Pi.basisFun_apply]
  change twistShear matrix choice (blockSwitch choice (basePositive factor position)) = _
  rw [blockSwitch_base_unselected choice factor position unselected]
  exact twistShear_base_positive matrix choice factor position unselected

theorem blockSwitch_fiber_selected (choice : ConeChoice rows baseDimension columns)
    (column : Fin columns) (selected : choice.fiber = some column) :
    blockSwitch choice (fiberPositive column) = fiberNegative := by
  ext coordinate
  cases coordinate with
  | inl coordinate =>
    have zero_eq : (fun position => fiberPositive (rows := rows) (baseDimension := baseDimension)
        column (.inl (coordinate.1, position))) = (0 : Fin baseDimension → ℤ) := by
      ext position
      simp [fiberPositive]
    change projectiveSwitch (choice.base coordinate.1)
      (fun position => fiberPositive column (.inl (coordinate.1, position))) coordinate.2 = 0
    rw [zero_eq, map_zero]
    rfl
  | inr other_column =>
    simp [selected, fiberPositive, fiberNegative, projectiveSwitch, Pi.single_apply]

theorem blockSwitch_fiber_unselected (choice : ConeChoice rows baseDimension columns)
    (column : Fin columns) (unselected : choice.fiber ≠ some column) :
    blockSwitch choice (fiberPositive column) = fiberPositive column := by
  ext coordinate
  cases coordinate with
  | inl coordinate =>
    have zero_eq : (fun position => fiberPositive (rows := rows) (baseDimension := baseDimension)
        column (.inl (coordinate.1, position))) = (0 : Fin baseDimension → ℤ) := by
      ext position
      simp [fiberPositive]
    change projectiveSwitch (choice.base coordinate.1)
      (fun position => fiberPositive column (.inl (coordinate.1, position))) coordinate.2 =
        fiberPositive column (.inl coordinate)
    rw [zero_eq, map_zero]
    simp [fiberPositive]
  | inr other_column =>
    cases selected : choice.fiber with
    | none => simp [selected, fiberPositive, projectiveSwitch]
    | some selected_column =>
      have distinct : column ≠ selected_column := by
        intro equality
        subst selected_column
        exact unselected selected
      have restriction_eq : (fun coordinate =>
          fiberPositive (rows := rows) (baseDimension := baseDimension) column (.inr coordinate)) =
            Pi.single column 1 := by
        ext coordinate
        simp [fiberPositive, Pi.single_apply]
      rw [blockSwitch_fiber_coordinate, restriction_eq]
      rw [selected, projectiveSwitch_single_other selected_column column distinct]
      simp [fiberPositive, Pi.single_apply]

theorem twistShear_fiberPositive (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (column : Fin columns) :
    twistShear matrix choice (fiberPositive column) = fiberPositive column := by
  ext coordinate
  cases coordinate with
  | inl coordinate => rfl
  | inr coordinate =>
    have coefficients : ∀ factor,
        selectedBaseCoordinate choice (fiberPositive column) factor = 0 := by
      intro factor
      cases selected : choice.base factor <;>
        simp [selectedBaseCoordinate, fiberPositive, selected]
    change fiberPositive column (.inr coordinate) - ∑ factor,
      selectedBaseCoordinate choice (fiberPositive column) factor * matrix factor coordinate = _
    simp [coefficients]

theorem twistShear_fiberNegative (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    twistShear matrix choice fiberNegative = fiberNegative := by
  ext coordinate
  cases coordinate with
  | inl coordinate => rfl
  | inr column =>
    have coefficients : ∀ factor,
        selectedBaseCoordinate choice (fiberNegative : Lattice rows baseDimension columns) factor = 0 := by
      intro factor
      cases selected : choice.base factor <;> simp [selectedBaseCoordinate, fiberNegative, selected]
    change (-1 : ℤ) - ∑ factor,
      selectedBaseCoordinate choice fiberNegative factor * matrix factor column = -1
    simp [coefficients]

theorem coneBasis_fiber_selected (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (column : Fin columns)
    (selected : choice.fiber = some column) :
    coneBasis matrix choice (.inr column) = fiberNegative := by
  rw [coneBasis, Basis.map_apply, standardBasis, Pi.basisFun_apply]
  change twistShear matrix choice (blockSwitch choice (fiberPositive column)) = _
  rw [blockSwitch_fiber_selected choice column selected]
  exact twistShear_fiberNegative matrix choice

theorem coneBasis_fiber_unselected (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (column : Fin columns)
    (unselected : choice.fiber ≠ some column) :
    coneBasis matrix choice (.inr column) = fiberPositive column := by
  rw [coneBasis, Basis.map_apply, standardBasis, Pi.basisFun_apply]
  change twistShear matrix choice (blockSwitch choice (fiberPositive column)) = _
  rw [blockSwitch_fiber_unselected choice column unselected]
  exact twistShear_fiberPositive matrix choice column

abbrev RayLabel (rows baseDimension columns : ℕ) :=
  (Fin rows × Option (Fin baseDimension)) ⊕ Option (Fin columns)

def rayVector (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    RayLabel rows baseDimension columns → Lattice rows baseDimension columns :=
  Sum.elim
    (fun label => label.2.elim (baseNegative matrix label.1) (basePositive label.1))
    (fun label => label.elim fiberNegative fiberPositive)

theorem rayVector_isPrimitive (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (label : RayLabel rows baseDimension columns) :
    TauCeti.IsPrimitive (rayVector matrix label) := by
  cases label with
  | inl label =>
    rcases label with ⟨factor, position⟩
    cases position with
    | none => exact baseNegative_isPrimitive matrix factor base_positive
    | some position => exact basePositive_isPrimitive factor position
  | inr column =>
    cases column with
    | none => exact fiberNegative_isPrimitive fiber_positive
    | some column => exact fiberPositive_isPrimitive column

def referenceChoice (rows baseDimension columns : ℕ) : ConeChoice rows baseDimension columns :=
  ⟨fun _ => none, none⟩

abbrev fixedWeightTwist {ones : ℕ} (matrix : FixedWeightMatrix rows columns ones) :
    Matrix (Fin rows) (Fin columns) ℤ :=
  fun factor column => BondalThomsen.augmentedColumnMatrix matrix factor (some column)

theorem fixedWeightTwist_nonnegative {ones : ℕ}
    (matrix : FixedWeightMatrix rows columns ones) (factor : Fin rows) (column : Fin columns) :
    0 ≤ fixedWeightTwist matrix factor column :=
  BondalThomsen.augmentedColumnMatrix_nonnegative matrix factor (some column)

theorem fixedWeightTwist_row_sum {ones : ℕ}
    (matrix : FixedWeightMatrix rows columns ones) (factor : Fin rows) :
    ∑ column : Fin columns, fixedWeightTwist matrix factor column = (ones : ℤ) := by
  change (∑ column : Fin columns, if column ∈ (matrix factor).val then (1 : ℤ) else 0) = _
  rw [Finset.sum_boole]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact_mod_cast fixedWeightMatrix_row_card matrix factor

end BondalThomsen.ProjectiveBundle
