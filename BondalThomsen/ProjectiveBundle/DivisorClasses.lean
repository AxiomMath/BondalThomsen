module

public import BondalThomsen.ProjectiveBundle.FanRays
public import BondalThomsen.ProjectiveBundle.FanPrimitive
public import BondalThomsen.Toric.Divisor.DivisorArithmetic
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

namespace BondalThomsen.ProjectiveBundle

open Module

variable {rows baseDimension columns : ℕ}

def divisorBasisLabel (coordinate : Coordinate rows baseDimension columns) :
    RayLabel rows baseDimension columns :=
  Sum.elim (fun coordinate => .inl (coordinate.1, some coordinate.2))
    (fun column => .inr (some column)) coordinate

def residualRayLabel (coordinate : Fin rows ⊕ Unit) : RayLabel rows baseDimension columns :=
  Sum.elim (fun factor => .inl (factor, none)) (fun _ => .inr none) coordinate

theorem rayVector_divisorBasisLabel (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (coordinate : Coordinate rows baseDimension columns) :
    rayVector matrix (divisorBasisLabel coordinate) =
      standardBasis rows baseDimension columns coordinate := by
  cases coordinate <;>
    simp [divisorBasisLabel, rayVector, standardBasis, Pi.basisFun_apply,
      basePositive, fiberPositive]

section Divisors

variable (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)

noncomputable def divisorBasisCoefficients :
    (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor →+
      (Coordinate rows baseDimension columns → ℤ) where
  toFun divisor coordinate := divisor
    (labelRay matrix base_positive fiber_positive (divisorBasisLabel coordinate))
  map_zero' := by ext coordinate; rfl
  map_add' first second := by ext coordinate; rfl

noncomputable def eliminationCharacter :
    (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor →+
      (Lattice rows baseDimension columns →+ ℤ) :=
  { toFun := fun divisor =>
      ((standardBasis rows baseDimension columns).constr ℤ
        (divisorBasisCoefficients matrix base_positive fiber_positive divisor)).toAddMonoidHom
    map_zero' := by
      apply AddMonoidHom.toIntLinearMap_injective
      apply (standardBasis rows baseDimension columns).ext
      intro coordinate
      simp [divisorBasisCoefficients]
    map_add' := by
      intro first second
      apply AddMonoidHom.toIntLinearMap_injective
      apply (standardBasis rows baseDimension columns).ext
      intro coordinate
      simp [divisorBasisCoefficients] }

@[simp] theorem eliminationCharacter_basis
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor)
    (coordinate : Coordinate rows baseDimension columns) :
    eliminationCharacter matrix base_positive fiber_positive divisor
        (standardBasis rows baseDimension columns coordinate) =
      divisor (labelRay matrix base_positive fiber_positive (divisorBasisLabel coordinate)) := by
  change ((standardBasis rows baseDimension columns).constr ℤ _)
    (standardBasis rows baseDimension columns coordinate) = _
  rw [Basis.constr_basis]
  rfl

@[simp] theorem eliminationCharacter_principal
    (character : Lattice rows baseDimension columns →+ ℤ) :
    eliminationCharacter matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).principalRayDivisor character) = character := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply (standardBasis rows baseDimension columns).ext
  intro coordinate
  change eliminationCharacter matrix base_positive fiber_positive _
    (standardBasis rows baseDimension columns coordinate) = character _
  rw [eliminationCharacter_basis]
  change character (rayVector matrix (divisorBasisLabel coordinate)) = _
  rw [rayVector_divisorBasisLabel]

noncomputable def normalizedDivisor :
    (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor →+
      (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor :=
  AddMonoidHom.id _ - ((fan (baseDimension := baseDimension) matrix).principalRayDivisor).comp
    (eliminationCharacter matrix base_positive fiber_positive)

@[simp] theorem normalizedDivisor_basis
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor)
    (coordinate : Coordinate rows baseDimension columns) :
    normalizedDivisor matrix base_positive fiber_positive divisor
      (labelRay matrix base_positive fiber_positive (divisorBasisLabel coordinate)) = 0 := by
  change divisor _ - eliminationCharacter matrix base_positive fiber_positive divisor
    (rayVector matrix (divisorBasisLabel coordinate)) = 0
  rw [rayVector_divisorBasisLabel, eliminationCharacter_basis, sub_self]

@[simp] theorem normalizedDivisor_principal
    (character : Lattice rows baseDimension columns →+ ℤ) :
    normalizedDivisor matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).principalRayDivisor character) = 0 := by
  change _ - (fan (baseDimension := baseDimension) matrix).principalRayDivisor
    (eliminationCharacter matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).principalRayDivisor character)) = 0
  rw [eliminationCharacter_principal]
  exact sub_self _

noncomputable def residualCoordinates :
    (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor →+
      ((Fin rows ⊕ Unit) → ℤ) where
  toFun divisor coordinate := normalizedDivisor matrix base_positive fiber_positive divisor
    (labelRay matrix base_positive fiber_positive (residualRayLabel coordinate))
  map_zero' := by ext coordinate; simp
  map_add' first second := by ext coordinate; simp

noncomputable def residualRepresentative :
    ((Fin rows ⊕ Unit) → ℤ) →+
      (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor where
  toFun coefficients := (fan (baseDimension := baseDimension) matrix).invariantDivisorOfCoefficients
    (fun ray => Sum.elim
      (fun label : Fin rows × Option (Fin baseDimension) =>
        label.2.elim (coefficients (.inl label.1)) (fun _ => 0))
      (fun label : Option (Fin columns) => label.elim (coefficients (.inr ())) (fun _ => 0))
      ((rayEquiv matrix base_positive fiber_positive).symm ray))
  map_zero' := by
    ext ray
    simp only [TauCeti.Toric.Fan.invariantDivisorOfCoefficients_apply]
    rcases (rayEquiv matrix base_positive fiber_positive).symm ray with label | label
    · rcases label with ⟨factor, position⟩; cases position <;> rfl
    · cases label <;> rfl
  map_add' first second := by
    ext ray
    simp only [TauCeti.Toric.Fan.invariantDivisorOfCoefficients_apply, Finsupp.add_apply]
    rcases (rayEquiv matrix base_positive fiber_positive).symm ray with label | label
    · rcases label with ⟨factor, position⟩; cases position <;> rfl
    · cases label <;> rfl

@[simp] theorem residualRepresentative_basis (coefficients : (Fin rows ⊕ Unit) → ℤ)
    (coordinate : Coordinate rows baseDimension columns) :
    residualRepresentative matrix base_positive fiber_positive coefficients
      (labelRay matrix base_positive fiber_positive (divisorBasisLabel coordinate)) = 0 := by
  change Sum.elim _ _ ((rayEquiv matrix base_positive fiber_positive).symm
    ((rayEquiv matrix base_positive fiber_positive) (divisorBasisLabel coordinate))) = 0
  rw [Equiv.symm_apply_apply]
  cases coordinate <;> rfl

@[simp] theorem residualRepresentative_residual (coefficients : (Fin rows ⊕ Unit) → ℤ)
    (coordinate : Fin rows ⊕ Unit) :
    residualRepresentative matrix base_positive fiber_positive coefficients
      (labelRay matrix base_positive fiber_positive (residualRayLabel coordinate)) =
        coefficients coordinate := by
  change Sum.elim _ _ ((rayEquiv matrix base_positive fiber_positive).symm
    ((rayEquiv matrix base_positive fiber_positive) (residualRayLabel coordinate))) = _
  rw [Equiv.symm_apply_apply]
  cases coordinate with
  | inl factor => rfl
  | inr fiber_index => cases fiber_index; rfl

@[simp] theorem eliminationCharacter_residualRepresentative
    (coefficients : (Fin rows ⊕ Unit) → ℤ) :
    eliminationCharacter matrix base_positive fiber_positive
      (residualRepresentative matrix base_positive fiber_positive coefficients) = 0 := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply (standardBasis rows baseDimension columns).ext
  intro coordinate
  change eliminationCharacter matrix base_positive fiber_positive _
    (standardBasis rows baseDimension columns coordinate) = 0
  rw [eliminationCharacter_basis, residualRepresentative_basis]

@[simp] theorem normalizedDivisor_residualRepresentative
    (coefficients : (Fin rows ⊕ Unit) → ℤ) :
    normalizedDivisor matrix base_positive fiber_positive
      (residualRepresentative matrix base_positive fiber_positive coefficients) =
        residualRepresentative matrix base_positive fiber_positive coefficients := by
  change _ - (fan (baseDimension := baseDimension) matrix).principalRayDivisor
    (eliminationCharacter matrix base_positive fiber_positive _) = _
  rw [eliminationCharacter_residualRepresentative, map_zero, sub_zero]
  rfl

@[simp] theorem residualCoordinates_residualRepresentative
    (coefficients : (Fin rows ⊕ Unit) → ℤ) :
    residualCoordinates matrix base_positive fiber_positive
      (residualRepresentative matrix base_positive fiber_positive coefficients) = coefficients := by
  ext coordinate
  change normalizedDivisor matrix base_positive fiber_positive _ _ = _
  rw [normalizedDivisor_residualRepresentative, residualRepresentative_residual]

theorem normalizedDivisor_eq_residualRepresentative
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    normalizedDivisor matrix base_positive fiber_positive divisor =
      residualRepresentative matrix base_positive fiber_positive
        (residualCoordinates matrix base_positive fiber_positive divisor) := by
  ext ray
  obtain ⟨label, rfl⟩ := (labelRay_bijective matrix base_positive fiber_positive).2 ray
  cases label with
  | inl label =>
    rcases label with ⟨factor, position⟩
    cases position with
    | none =>
      change _ = residualRepresentative matrix base_positive fiber_positive _
        (labelRay matrix base_positive fiber_positive (residualRayLabel (.inl factor)))
      rw [residualRepresentative_residual]
      rfl
    | some position =>
      change normalizedDivisor matrix base_positive fiber_positive divisor
        (labelRay matrix base_positive fiber_positive (divisorBasisLabel (.inl (factor, position)))) =
          residualRepresentative matrix base_positive fiber_positive _
            (labelRay matrix base_positive fiber_positive (divisorBasisLabel (.inl (factor, position))))
      rw [normalizedDivisor_basis, residualRepresentative_basis]
  | inr position =>
    cases position with
    | none =>
      change _ = residualRepresentative matrix base_positive fiber_positive _
        (labelRay matrix base_positive fiber_positive (residualRayLabel (.inr ())))
      rw [residualRepresentative_residual]
      rfl
    | some column =>
      change normalizedDivisor matrix base_positive fiber_positive divisor
        (labelRay matrix base_positive fiber_positive (divisorBasisLabel (.inr column))) =
          residualRepresentative matrix base_positive fiber_positive _
            (labelRay matrix base_positive fiber_positive (divisorBasisLabel (.inr column)))
      rw [normalizedDivisor_basis, residualRepresentative_basis]

theorem principalRayDivisor_range_eq_residualCoordinates_ker :
    (fan (baseDimension := baseDimension) matrix).principalRayDivisor.range =
      (residualCoordinates matrix base_positive fiber_positive).ker := by
  ext divisor
  constructor
  · rintro ⟨character, rfl⟩
    change residualCoordinates matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).principalRayDivisor character) = 0
    ext coordinate
    change normalizedDivisor matrix base_positive fiber_positive _ _ = 0
    rw [normalizedDivisor_principal]
    rfl
  · intro zero
    change residualCoordinates matrix base_positive fiber_positive divisor = 0 at zero
    have normalized_zero : normalizedDivisor matrix base_positive fiber_positive divisor = 0 := by
      rw [normalizedDivisor_eq_residualRepresentative, zero, map_zero]
    refine ⟨eliminationCharacter matrix base_positive fiber_positive divisor, ?_⟩
    change divisor - (fan (baseDimension := baseDimension) matrix).principalRayDivisor
      (eliminationCharacter matrix base_positive fiber_positive divisor) = 0 at normalized_zero
    exact (sub_eq_zero.mp normalized_zero).symm

noncomputable def divisorClassEquiv :
    (fan (baseDimension := baseDimension) matrix).InvariantRayDivisorClass ≃+
      ((Fin rows ⊕ Unit) → ℤ) :=
  QuotientAddGroup.liftEquiv (fan (baseDimension := baseDimension) matrix).principalRayDivisor.range
    (fun coefficients => ⟨residualRepresentative matrix base_positive fiber_positive coefficients,
      residualCoordinates_residualRepresentative matrix base_positive fiber_positive coefficients⟩)
    (principalRayDivisor_range_eq_residualCoordinates_ker matrix base_positive fiber_positive)

@[simp] theorem divisorClassEquiv_mk
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    divisorClassEquiv matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).invariantRayDivisorClass divisor) =
        residualCoordinates matrix base_positive fiber_positive divisor := rfl

@[simp] theorem divisorClassEquiv_mk_residualRepresentative
    (coefficients : (Fin rows ⊕ Unit) → ℤ) :
    divisorClassEquiv matrix base_positive fiber_positive
      ((fan (baseDimension := baseDimension) matrix).invariantRayDivisorClass
        (residualRepresentative matrix base_positive fiber_positive coefficients)) = coefficients := by
  rw [divisorClassEquiv_mk, residualCoordinates_residualRepresentative]

theorem residualCoordinates_base
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor)
    (factor : Fin rows) :
    residualCoordinates matrix base_positive fiber_positive divisor (.inl factor) =
      divisor (labelRay matrix base_positive fiber_positive (.inl (factor, none))) +
        (∑ position : Fin baseDimension,
          divisor (labelRay matrix base_positive fiber_positive (.inl (factor, some position)))) -
        ∑ column : Fin columns, matrix factor column *
          divisor (labelRay matrix base_positive fiber_positive (.inr (some column))) := by
  let character := eliminationCharacter matrix base_positive fiber_positive divisor
  have relation_values := congrArg character (base_ray_relation matrix factor)
  rw [map_add, map_sum, rowTwist_eq_sum, map_sum] at relation_values
  have base_values : ∀ position : Fin baseDimension, character (basePositive factor position) =
      divisor (labelRay matrix base_positive fiber_positive (.inl (factor, some position))) := by
    intro position
    simpa only [character, standardBasis, Pi.basisFun_apply, basePositive, divisorBasisLabel,
      Sum.elim_inl] using
      eliminationCharacter_basis matrix base_positive fiber_positive divisor (.inl (factor, position))
  have fiber_values : ∀ column : Fin columns, character (fiberPositive column) =
      divisor (labelRay matrix base_positive fiber_positive (.inr (some column))) := by
    intro column
    simpa only [character, standardBasis, Pi.basisFun_apply, fiberPositive, divisorBasisLabel,
      Sum.elim_inr] using eliminationCharacter_basis matrix base_positive fiber_positive divisor (.inr column)
  have twist_values : ∀ column : Fin columns, character (matrix factor column • fiberPositive column) =
      matrix factor column * divisor (labelRay matrix base_positive fiber_positive (.inr (some column))) := by
    intro column
    change character.toIntLinearMap (matrix factor column • fiberPositive column) = _
    rw [map_smul]
    simpa only [smul_eq_mul, AddMonoidHom.coe_toIntLinearMap] using
      congrArg (fun value : ℤ => matrix factor column * value) (fiber_values column)
  simp only [base_values, twist_values] at relation_values
  change divisor (labelRay matrix base_positive fiber_positive (.inl (factor, none))) -
    character (baseNegative matrix factor) = _
  linarith

theorem residualCoordinates_fiber
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    residualCoordinates matrix base_positive fiber_positive divisor (.inr ()) =
      divisor (labelRay matrix base_positive fiber_positive (.inr none)) +
        ∑ column : Fin columns,
          divisor (labelRay matrix base_positive fiber_positive (.inr (some column))) := by
  let character := eliminationCharacter matrix base_positive fiber_positive divisor
  have relation_values := congrArg character (fiber_ray_relation
    (rows := rows) (baseDimension := baseDimension) (columns := columns))
  rw [map_add, map_sum, map_zero] at relation_values
  have fiber_values : ∀ column : Fin columns, character (fiberPositive column) =
      divisor (labelRay matrix base_positive fiber_positive (.inr (some column))) := by
    intro column
    simpa only [character, standardBasis, Pi.basisFun_apply, fiberPositive, divisorBasisLabel,
      Sum.elim_inr] using eliminationCharacter_basis matrix base_positive fiber_positive divisor (.inr column)
  simp only [fiber_values] at relation_values
  change divisor (labelRay matrix base_positive fiber_positive (.inr none)) -
    character fiberNegative = _
  linarith

end Divisors

end BondalThomsen.ProjectiveBundle
