module

public import BondalThomsen.Fan.EffectiveRayDivisors
public import BondalThomsen.Fan.PrimitiveCollectionBoundary

@[expose] public section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem exists_two_distinct_floorRayDivisorClasses
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (pairing direction : Lattice →+ ℚ) (prescribed : Finset fan.Ray) [DecidableEq fan.Ray]
    (nonempty : prescribed.Nonempty)
    (prescribed_integral : ∀ ray ∈ prescribed, Int.fract (pairing ray.val) = 0)
    (prescribed_direction : ∀ ray ∈ prescribed, direction ray.val = -1)
    (other_direction : ∀ ray ∉ prescribed, Int.fract (pairing ray.val) = 0 →
      0 ≤ direction ray.val) :
    ∃ parameter : ℚ, 0 < parameter ∧
      fan.floorRayDivisor (pairing + parameter • direction) - fan.floorRayDivisor pairing =
        fan.invariantDivisorOfCoefficients
          (fun ray => if ray ∈ prescribed then -1 else 0) ∧
      fan.floorRayDivisorClass (pairing + parameter • direction) ≠
        fan.floorRayDivisorClass pairing := by
  classical
  obtain ⟨parameter, positive, difference⟩ := fan.exists_floorRayDivisor_difference
    pairing direction (prescribed : Set fan.Ray) prescribed_integral prescribed_direction
    other_direction
  simp only [Finset.mem_coe] at difference
  let effective := fan.invariantDivisorOfCoefficients
    (fun ray => if ray ∈ prescribed then 1 else 0)
  have negative : fan.invariantDivisorOfCoefficients
      (fun ray => if ray ∈ prescribed then -1 else 0) = -effective := by
    ext ray
    simp only [invariantDivisorOfCoefficients_apply, Finsupp.neg_apply, effective]
    split <;> norm_num
  have new_divisor : fan.floorRayDivisor (pairing + parameter • direction) =
      fan.floorRayDivisor pairing - effective := by
    rw [negative] at difference
    exact sub_eq_iff_eq_add.mp difference |>.trans (by abel)
  have nonnegative : ∀ ray, 0 ≤ effective ray := by
    intro ray
    change 0 ≤ if ray ∈ prescribed then (1 : ℤ) else 0
    split <;> norm_num
  have nonzero : effective ≠ 0 := by
    obtain ⟨ray, member⟩ := nonempty
    intro zero
    have value := congrArg (fun divisor : fan.InvariantRayDivisor => divisor ray) zero
    simp [effective, member] at value
  refine ⟨parameter, positive, difference, ?_⟩
  unfold floorRayDivisorClass
  rw [new_divisor]
  exact fan.invariantRayDivisorClass_sub_ne_of_nonnegative complete
    (fan.floorRayDivisor pairing) effective nonnegative nonzero

end TauCeti.Toric.Fan
