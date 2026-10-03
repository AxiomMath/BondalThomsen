module

public import BondalThomsen.Fan.PrimitiveArithmetic
public import Mathlib.Data.Rat.Floor

@[expose] public section

namespace BondalThomsen

open Finset

variable {Left Right : Type*} [Fintype Left] [Fintype Right]

theorem primitiveIntersection_ratCast (left_values : Left → ℚ)
    (right_values : Right → ℚ) (coefficients : Right → ℕ) :
    primitiveIntersection (fun index => (left_values index : ℝ))
      (fun index => (right_values index : ℝ)) coefficients =
      -(∑ index, ⌊left_values index⌋) +
        ∑ index, (coefficients index : ℤ) * ⌊right_values index⌋ := by
  simp only [primitiveIntersection, Rat.floor_cast]

theorem primitiveRelation_ratCast_iff (left_values : Left → ℚ)
    (right_values : Right → ℚ) (coefficients : Right → ℕ) :
    (∑ index, (left_values index : ℝ) =
      ∑ index, (coefficients index : ℝ) * (right_values index : ℝ)) ↔
    (∑ index, left_values index =
      ∑ index, (coefficients index : ℚ) * right_values index) := by
  constructor <;> intro relation <;> exact_mod_cast relation

theorem primitiveIntersection_rat_nonnegative (left_values : Left → ℚ)
    (right_values : Right → ℚ) (coefficients : Right → ℕ)
    (relation : ∑ index, left_values index =
      ∑ index, (coefficients index : ℚ) * right_values index)
    (small_right : ∑ index, coefficients index ≤ 1) :
    0 ≤ primitiveIntersection (fun index => (left_values index : ℝ))
      (fun index => (right_values index : ℝ)) coefficients :=
  primitiveIntersection_nonnegative _ _ coefficients
    ((primitiveRelation_ratCast_iff left_values right_values coefficients).mpr relation)
    small_right

section Pairing

variable {Lattice : Type*} [AddCommMonoid Lattice]

theorem primitiveRelation_pairing (pairing : Lattice →+ ℚ)
    (left_vectors : Left → Lattice) (right_vectors : Right → Lattice)
    (coefficients : Right → ℕ)
    (relation : ∑ index, left_vectors index =
      ∑ index, coefficients index • right_vectors index) :
    ∑ index, pairing (left_vectors index) =
      ∑ index, (coefficients index : ℚ) * pairing (right_vectors index) := by
  have paired := congrArg pairing relation
  simpa only [map_sum, map_nsmul, nsmul_eq_mul] using paired

theorem primitiveIntersection_pairing_nonnegative (pairing : Lattice →+ ℚ)
    (left_vectors : Left → Lattice) (right_vectors : Right → Lattice)
    (coefficients : Right → ℕ)
    (relation : ∑ index, left_vectors index =
      ∑ index, coefficients index • right_vectors index)
    (small_right : ∑ index, coefficients index ≤ 1) :
    0 ≤ primitiveIntersection (fun index => (pairing (left_vectors index) : ℝ))
      (fun index => (pairing (right_vectors index) : ℝ)) coefficients :=
  primitiveIntersection_rat_nonnegative _ _ coefficients
    (primitiveRelation_pairing pairing left_vectors right_vectors coefficients relation)
    small_right

end Pairing

end BondalThomsen
