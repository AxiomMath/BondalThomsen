module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

namespace BondalThomsen

theorem finite_set_integer_scale (values : Set ℚ) (finite : values.Finite) :
    ∃ multiplier : ℤ, multiplier ≠ 0 ∧
      ∀ value ∈ values, ∃ integer : ℤ, (multiplier : ℚ) * value = (integer : ℚ) := by
  classical
  obtain ⟨multiplier, scaled⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors ℤ) finite.toFinset
  refine ⟨multiplier, mem_nonZeroDivisors_iff_ne_zero.mp multiplier.property, ?_⟩
  intro value member
  obtain ⟨integer, equality⟩ := scaled value (finite.mem_toFinset.mpr member)
  refine ⟨integer, ?_⟩
  simpa using equality.symm

end BondalThomsen
