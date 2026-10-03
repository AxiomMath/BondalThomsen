module

public import BondalThomsen.Fan.Basic
public import BondalThomsen.FloorClasses.FloorPerturbation
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

abbrev InvariantRayDivisor (fan : TauCeti.Toric.Fan embedding) := fan.Ray →₀ ℤ

noncomputable def invariantDivisorOfCoefficients (fan : TauCeti.Toric.Fan embedding)
    (coefficients : fan.Ray → ℤ) : fan.InvariantRayDivisor :=
  Finsupp.equivFunOnFinite.symm coefficients

@[simp] theorem invariantDivisorOfCoefficients_apply (fan : TauCeti.Toric.Fan embedding)
    (coefficients : fan.Ray → ℤ) (ray : fan.Ray) :
    fan.invariantDivisorOfCoefficients coefficients ray = coefficients ray := rfl

noncomputable def principalRayDivisor (fan : TauCeti.Toric.Fan embedding) :
    (Lattice →+ ℤ) →+ fan.InvariantRayDivisor where
  toFun character := fan.invariantDivisorOfCoefficients (fun ray => character ray.val)
  map_zero' := by ext ray; rfl
  map_add' first second := by ext ray; rfl

@[simp] theorem principalRayDivisor_apply (fan : TauCeti.Toric.Fan embedding)
    (character : Lattice →+ ℤ) (ray : fan.Ray) :
    fan.principalRayDivisor character ray = character ray.val := rfl

noncomputable def floorRayDivisor (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) : fan.InvariantRayDivisor :=
  fan.invariantDivisorOfCoefficients (fun ray => ⌊pairing ray.val⌋)

@[simp] theorem floorRayDivisor_apply (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) (ray : fan.Ray) :
    fan.floorRayDivisor pairing ray = ⌊pairing ray.val⌋ := rfl

theorem floorRayDivisor_add_integral (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) (character : Lattice →+ ℤ) :
    fan.floorRayDivisor (pairing + (Int.castAddHom ℚ).comp character) =
      fan.floorRayDivisor pairing + fan.principalRayDivisor character := by
  ext ray
  simp [Int.floor_add_intCast]

abbrev InvariantRayDivisorClass (fan : TauCeti.Toric.Fan embedding) :=
  fan.InvariantRayDivisor ⧸ fan.principalRayDivisor.range

noncomputable def invariantRayDivisorClass (fan : TauCeti.Toric.Fan embedding) :
    fan.InvariantRayDivisor →+ fan.InvariantRayDivisorClass :=
  QuotientAddGroup.mk' fan.principalRayDivisor.range

@[simp] theorem invariantRayDivisorClass_principal (fan : TauCeti.Toric.Fan embedding)
    (character : Lattice →+ ℤ) :
    fan.invariantRayDivisorClass (fan.principalRayDivisor character) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨character, rfl⟩

noncomputable def floorRayDivisorClass (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) : fan.InvariantRayDivisorClass :=
  fan.invariantRayDivisorClass (fan.floorRayDivisor pairing)

theorem floorRayDivisorClass_add_integral (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) (character : Lattice →+ ℤ) :
    fan.floorRayDivisorClass (pairing + (Int.castAddHom ℚ).comp character) =
      fan.floorRayDivisorClass pairing := by
  unfold floorRayDivisorClass
  rw [floorRayDivisor_add_integral, map_add, invariantRayDivisorClass_principal, add_zero]

theorem exists_floorRayDivisor_difference (fan : TauCeti.Toric.Fan embedding)
    (pairing direction : Lattice →+ ℚ) (prescribed : Set fan.Ray)
    [DecidablePred (fun ray => ray ∈ prescribed)]
    (prescribed_integral : ∀ ray ∈ prescribed, Int.fract (pairing ray.val) = 0)
    (prescribed_direction : ∀ ray ∈ prescribed, direction ray.val = -1)
    (other_direction : ∀ ray ∉ prescribed, Int.fract (pairing ray.val) = 0 →
      0 ≤ direction ray.val) :
    ∃ parameter : ℚ, 0 < parameter ∧
      fan.floorRayDivisor (pairing + parameter • direction) - fan.floorRayDivisor pairing =
        fan.invariantDivisorOfCoefficients
          (fun ray => if ray ∈ prescribed then -1 else 0) := by
  classical
  let := Fintype.ofFinite fan.Ray
  obtain ⟨parameter, positive, formula⟩ := BondalThomsen.exists_prescribed_rational_floor_drop
    (fun ray : fan.Ray => pairing ray.val) (fun ray : fan.Ray => direction ray.val)
    prescribed prescribed_integral prescribed_direction other_direction
  refine ⟨parameter, positive, ?_⟩
  ext ray
  simpa only [Finsupp.sub_apply, floorRayDivisor_apply, invariantDivisorOfCoefficients_apply,
    AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] using formula ray

end TauCeti.Toric.Fan
