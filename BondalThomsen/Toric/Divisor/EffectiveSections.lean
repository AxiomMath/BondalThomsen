module

public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Fan.EffectiveRayDivisors
public import BondalThomsen.Derived.InvertibleSheafExtCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem characterLaurentMonomial_zero_ne_zero (fan : Fan embedding) :
    fan.characterLaurentMonomial 𝕜 (0 : Lattice →+ ℤ) ≠ 0 := by
  classical
  intro equality
  have coefficient := congrArg
    (fun polynomial : fan.LaurentCharacterAlgebra 𝕜 =>
      polynomial.coeff (ofAdd (0 : Lattice →+ ℤ))) equality
  simp [characterLaurentMonomial] at coefficient

noncomputable def invariantDivisorEffectiveSection (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (effective : ∀ ray, 0 ≤ divisor ray) :
    Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, ⊤) :=
  fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor
    ⟨fan.characterLaurentMonomial 𝕜 0,
      (fan.characterLaurentMonomial_mem_global_iff 𝕜 divisor 0).mpr
        (fun ray => by simpa using neg_nonpos.mpr (effective ray))⟩

theorem invariantDivisorEffectiveSection_ne_zero (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (effective : ∀ ray, 0 ≤ divisor ray) :
    fan.invariantDivisorEffectiveSection 𝕜 complete regular divisor effective ≠ 0 := by
  intro equality
  have polynomial_zero :=
    (fan.globalDivisorLaurentToSheafSections_bijective 𝕜 complete regular divisor).1
      (equality.trans (map_zero _).symm)
  exact fan.characterLaurentMonomial_zero_ne_zero 𝕜
    (congrArg Subtype.val polynomial_zero)

end TauCeti.Toric.Fan
