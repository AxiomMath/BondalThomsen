module

public import BondalThomsen.Fan.Basic
public import BondalThomsen.Rarity.Counting
public import BondalThomsen.Ports.PrimitiveDirections

@[expose] public section

open Set Finset BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

namespace TauCeti.Toric.Fan

variable (fan : TauCeti.Toric.Fan embedding)

def rayDirection (ray : fan.Ray) : TauCeti.Slope Lattice :=
  TauCeti.Slope.mk ray.val ray.property.1

def rayDirections : Set (TauCeti.Slope Lattice) := Set.range fan.rayDirection

instance finiteRayDirections : Finite fan.rayDirections := (Set.finite_range _).to_subtype

def toRayDirection (ray : fan.Ray) : fan.rayDirections :=
  ⟨fan.rayDirection ray, ⟨ray, rfl⟩⟩

theorem rayDirection_fiber_card_le_two [Fintype fan.Ray]
    [direction_decidable : DecidableEq fan.rayDirections]
    (direction : fan.rayDirections) :
    (Finset.univ.filter (fun ray => fan.toRayDirection ray = direction)).card ≤ 2 := by
  classical
  let : DecidablePred (fun ray : fan.Ray => fan.toRayDirection ray = direction) :=
    fun ray => direction_decidable (fan.toRayDirection ray) direction
  let fiber := univ.filter (fun ray => fan.toRayDirection ray = direction)
  obtain ⟨representative, representative_direction⟩ := direction.property
  have vectors_subset : fiber.image Subtype.val ⊆ {representative.val, -representative.val} := by
    intro vector member
    obtain ⟨ray, in_fiber, rfl⟩ := mem_image.mp member
    have in_direction : fan.toRayDirection ray = direction := by
      exact (@Finset.mem_filter fan.Ray (fun ray => fan.toRayDirection ray = direction)
        (fun ray => direction_decidable (fan.toRayDirection ray) direction)
        Finset.univ ray).mp in_fiber |>.2
    have same_direction : fan.rayDirection ray = fan.rayDirection representative :=
      (congrArg Subtype.val in_direction).trans representative_direction.symm
    have same := (TauCeti.Slope.mk_eq_mk_iff ray.property.1 representative.property.1).mp
      same_direction
    simpa only [Finset.mem_insert, Finset.mem_singleton] using same
  calc
    fiber.card = (fiber.image Subtype.val).card :=
      (card_image_of_injective fiber Subtype.val_injective).symm
    _ ≤ ({representative.val, -representative.val} : Finset Lattice).card :=
      card_le_card vectors_subset
    _ ≤ 2 := Finset.card_le_two

theorem ray_count_le_twice_directions : Nat.card fan.Ray ≤ 2 * Nat.card fan.rayDirections := by
  classical
  let : Fintype fan.Ray := Fintype.ofFinite _
  let : Fintype fan.rayDirections := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using finite_fiber_count fan.toRayDirection 2
    fan.rayDirection_fiber_card_le_two

end TauCeti.Toric.Fan
