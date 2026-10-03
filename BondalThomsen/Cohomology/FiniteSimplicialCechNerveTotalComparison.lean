module

public import BondalThomsen.Cohomology.FiniteSimplicialCechNerveComparison
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.Algebra.Homology.ShortComplex.Ab

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits
open BondalThomsen.FiniteSimplicialCechNerveComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

namespace BondalThomsen.FiniteSimplicialCechNerveTotalComparison

variable {Row Column : Type}

local instance nonnegativeCochainTensorSigns :
    ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun degree : ℕ => (-1 : ℤˣ) ^ degree) (pow_add (-1 : ℤˣ))
  rel_add first second third related := by dsimp at related ⊢; omega
  add_rel first second third related := by dsimp at related ⊢; omega
  ε'_succ := by
    rintro degree _next rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one]

local instance nonnegativeTotalSymmetry : TotalComplexShapeSymmetry
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  symm first second := Nat.add_comm second first
  σ first second := (-1 : ℤˣ) ^ (first * second)
  σ_ε₁ := by
    rintro degree _next rfl other
    change (-1 : ℤˣ) ^ (degree * other) * 1 =
      (-1 : ℤˣ) ^ other * (-1 : ℤˣ) ^ ((degree + 1) * other)
    rw [mul_one, Nat.add_mul, Nat.one_mul, pow_add, mul_left_comm,
      Int.units_mul_self, mul_one]
  σ_ε₂ := by
    rintro degree other _next rfl
    change (-1 : ℤˣ) ^ (degree * other) * (-1 : ℤˣ) ^ degree =
      1 * (-1 : ℤˣ) ^ (degree * (other + 1))
    rw [one_mul, Nat.mul_add, Nat.mul_one, pow_add]

end BondalThomsen.FiniteSimplicialCechNerveTotalComparison
