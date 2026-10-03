module

public import BondalThomsen.DeepFan.CriterionConverse
public import BondalThomsen.Fan.PrimitiveNefArithmetic
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace TauCeti.Toric.Fan

open Finset

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {fan : TauCeti.Toric.Fan embedding}
    {left right : Finset fan.Ray}

noncomputable def PrimitiveLatticeRelation.divisorPairing
    (relation : PrimitiveLatticeRelation fan left right) : fan.InvariantRayDivisor →+ ℤ where
  toFun := relation.divisorIntersection
  map_zero' := by simp [PrimitiveLatticeRelation.divisorIntersection]
  map_add' first second := by
    simp only [PrimitiveLatticeRelation.divisorIntersection, Finsupp.add_apply,
      mul_add, Finset.sum_add_distrib]
    abel

@[simp] theorem PrimitiveLatticeRelation.divisorPairing_principal
    (relation : PrimitiveLatticeRelation fan left right) (character : Lattice →+ ℤ) :
    relation.divisorPairing (fan.principalRayDivisor character) = 0 := by
  change (∑ ray : left, character ray.val.val) -
    (∑ ray : right, (relation.coefficients ray : ℤ) * character ray.val.val) = 0
  have paired := congrArg character relation.lattice_eq
  simp only [map_sum, map_zsmul, zsmul_eq_mul] at paired
  exact sub_eq_zero.mpr paired

noncomputable def PrimitiveLatticeRelation.classPairing
    (relation : PrimitiveLatticeRelation fan left right) : fan.InvariantRayDivisorClass →+ ℤ :=
  QuotientAddGroup.lift fan.principalRayDivisor.range relation.divisorPairing (by
    rintro divisor ⟨character, rfl⟩
    exact relation.divisorPairing_principal character)

@[simp] theorem PrimitiveLatticeRelation.classPairing_mk
    (relation : PrimitiveLatticeRelation fan left right) (divisor : fan.InvariantRayDivisor) :
    relation.classPairing (fan.invariantRayDivisorClass divisor) =
      relation.divisorIntersection divisor := rfl

theorem PrimitiveLatticeRelation.classPairing_negative_floor
    (relation : PrimitiveLatticeRelation fan left right) (pairing : Lattice →+ ℚ) :
    relation.classPairing (-fan.floorRayDivisorClass pairing) =
      BondalThomsen.primitiveIntersection (fun ray : left => (pairing ray.val.val : ℝ))
        (fun ray : right => (pairing ray.val.val : ℝ)) relation.coefficients := by
  rw [map_neg]
  change -relation.divisorIntersection (fan.floorRayDivisor pairing) = _
  rw [BondalThomsen.primitiveIntersection_ratCast]
  simp only [PrimitiveLatticeRelation.divisorIntersection, floorRayDivisor_apply]
  ring

theorem PrimitiveLatticeRelation.classPairing_negative_floor_nonnegative
    (relation : PrimitiveLatticeRelation fan left right)
    (small : ∑ ray, relation.coefficients ray ≤ 1) (pairing : Lattice →+ ℚ) :
    0 ≤ relation.classPairing (-fan.floorRayDivisorClass pairing) := by
  rw [relation.classPairing_negative_floor]
  exact BondalThomsen.primitiveIntersection_pairing_nonnegative pairing
    (fun ray : left => ray.val.val) (fun ray : right => ray.val.val)
    relation.coefficients (by simpa only [Nat.cast_smul_eq_nsmul] using relation.lattice_eq)
    small

end TauCeti.Toric.Fan
