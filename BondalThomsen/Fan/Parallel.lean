module

public import BondalThomsen.Fan.Directions
public import BondalThomsen.Fan.PrimitiveParallel
public import BondalThomsen.Matroid.RepresentedSimplification
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open Module Submodule Set
open scoped TensorProduct

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def rayRep (fan : TauCeti.Toric.Fan embedding) :
    fan.rayMatroid.Rep ℚ (ℚ ⊗[ℤ] Lattice) :=
  Matroid.repOfRays (Field := ℚ) (fun ray : fan.Ray => (1 : ℚ) ⊗ₜ[ℤ] ray.val)

@[simp] theorem rayRep_apply (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    fan.rayRep ray = (1 : ℚ) ⊗ₜ[ℤ] ray.val := rfl

theorem rayRep_ne_zero (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    fan.rayRep ray ≠ 0 := by
  let := fan.lattice.free
  have tensor_injective := Module.Flat.tensorProduct_mk_injective ℤ Lattice ℚ
  simpa only [rayRep_apply, TensorProduct.mk_apply, map_zero] using
    tensor_injective.ne ray.property.1.ne_zero

theorem rayMatroid_isNonloop (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    fan.rayMatroid.IsNonloop ray :=
  (fan.rayRep.ne_zero_iff_isNonloop ray).mp (fan.rayRep_ne_zero ray)

theorem rayMatroid_parallel_iff_direction_eq (fan : TauCeti.Toric.Fan embedding)
    (first second : fan.Ray) :
    fan.rayMatroid.Parallel first second ↔ fan.rayDirection first = fan.rayDirection second := by
  let := fan.lattice.free
  let := fan.lattice.finite
  rw [fan.rayRep.parallel_iff_span_eq]
  rw [and_iff_right (fan.rayRep_ne_zero first), and_iff_right (fan.rayRep_ne_zero second)]
  simp only [rayRep_apply]
  exact (first.property.1.rational_span_eq_iff second.property.1).trans
    (TauCeti.Slope.mk_eq_mk_iff first.property.1 second.property.1).symm

noncomputable def simplificationDirectionEquiv (fan : TauCeti.Toric.Fan embedding)
    {smaller : Matroid fan.Ray} (simplification : smaller.IsSimplification fan.rayMatroid) :
    smaller.E ≃ fan.rayDirections := by
  let to_direction := fun element : smaller.E => fan.toRayDirection element.val
  apply Equiv.ofBijective to_direction
  constructor
  · intro first second equality
    apply Subtype.ext
    apply simplification.eq_of_parallel first.property second.property
    exact (fan.rayMatroid_parallel_iff_direction_eq first.val second.val).mpr
      (congrArg Subtype.val equality)
  · intro direction
    obtain ⟨ray, ray_direction⟩ := direction.property
    obtain ⟨representative, ⟨member, parallel⟩, _⟩ :=
      simplification.exists_unique (fan.rayMatroid_isNonloop ray)
    refine ⟨⟨representative, member⟩, ?_⟩
    apply Subtype.ext
    exact ((fan.rayMatroid_parallel_iff_direction_eq ray representative).mp parallel).symm.trans
      ray_direction

theorem simplification_ground_card_eq_directions (fan : TauCeti.Toric.Fan embedding)
    {smaller : Matroid fan.Ray} (simplification : smaller.IsSimplification fan.rayMatroid) :
    Nat.card smaller.E = Nat.card fan.rayDirections :=
  Nat.card_congr (fan.simplificationDirectionEquiv simplification)

theorem ray_count_le_twice_simplification (fan : TauCeti.Toric.Fan embedding)
    {smaller : Matroid fan.Ray} (simplification : smaller.IsSimplification fan.rayMatroid) :
    Nat.card fan.Ray ≤ 2 * Nat.card smaller.E := by
  rw [fan.simplification_ground_card_eq_directions simplification]
  exact fan.ray_count_le_twice_directions

end TauCeti.Toric.Fan
