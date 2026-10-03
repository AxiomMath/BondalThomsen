module

public import BondalThomsen.Toric.Divisor.DivisorArithmetic
public import BondalThomsen.Fan.Polytope
public import BondalThomsen.Fan.PositiveSpanning

@[expose] public section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem character_eq_zero_of_nonnegative_rays (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (character : Lattice →+ ℤ)
    (nonnegative : ∀ ray : fan.Ray, 0 ≤ character ray.val) : character = 0 := by
  have functional_zero := BondalThomsen.linearFunctional_eq_zero_of_positive_spanning
    fan.rayGenerators (fan.hull_rayGenerators_eq_top complete)
    (-(fan.lattice.realCharacter character)) (by
      rintro point ⟨ray, rfl⟩
      simp only [LinearMap.neg_apply, fan.lattice.realCharacter_apply]
      exact neg_nonpos.mpr (by exact_mod_cast nonnegative ray))
  have extension_zero : fan.lattice.realCharacter character = 0 := by
    exact neg_eq_zero.mp functional_zero
  apply fan.lattice.realCharacter_injective
  simpa using extension_zero

theorem principalRayDivisor_eq_zero_of_nonnegative
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (character : Lattice →+ ℤ)
    (nonnegative : ∀ ray : fan.Ray, 0 ≤ fan.principalRayDivisor character ray) :
    fan.principalRayDivisor character = 0 := by
  rw [fan.character_eq_zero_of_nonnegative_rays complete character nonnegative, map_zero]

theorem invariantRayDivisor_eq_zero_of_nonnegative_class_zero
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (divisor : fan.InvariantRayDivisor)
    (nonnegative : ∀ ray, 0 ≤ divisor ray)
    (class_zero : fan.invariantRayDivisorClass divisor = 0) : divisor = 0 := by
  obtain ⟨character, equality⟩ := (QuotientAddGroup.eq_zero_iff _).mp class_zero
  rw [← equality]
  apply fan.principalRayDivisor_eq_zero_of_nonnegative complete character
  intro ray
  simpa only [equality] using nonnegative ray

theorem invariantRayDivisorClass_ne_zero_of_nonnegative
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (divisor : fan.InvariantRayDivisor)
    (nonnegative : ∀ ray, 0 ≤ divisor ray) (nonzero : divisor ≠ 0) :
    fan.invariantRayDivisorClass divisor ≠ 0 :=
  fun class_zero => nonzero
    (fan.invariantRayDivisor_eq_zero_of_nonnegative_class_zero complete divisor
      nonnegative class_zero)

theorem invariantRayDivisorClass_sub_ne_of_nonnegative
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (divisor effective : fan.InvariantRayDivisor)
    (nonnegative : ∀ ray, 0 ≤ effective ray) (nonzero : effective ≠ 0) :
    fan.invariantRayDivisorClass (divisor - effective) ≠
      fan.invariantRayDivisorClass divisor := by
  rw [map_sub]
  intro equality
  have class_zero : fan.invariantRayDivisorClass effective = 0 :=
    sub_eq_self.mp equality
  exact fan.invariantRayDivisorClass_ne_zero_of_nonnegative complete effective
    nonnegative nonzero class_zero

end TauCeti.Toric.Fan
