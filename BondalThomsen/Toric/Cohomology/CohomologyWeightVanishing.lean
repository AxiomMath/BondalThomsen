module

public import BondalThomsen.Toric.Cohomology.CechWeightHomologyDirectSum

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Classical DirectSum

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def invariantDivisorCohomologyCharacterInclusion
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (degree : ℕ) (character : Lattice →+ ℤ) :
    ↑((fan.primitiveComplementComplex 𝕜 complete regular
      (divisor + fan.principalRayDivisor character)).homology degree) →+
        TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
          (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj degree :=
  (fan.invariantDivisorCohomologyWeightDirectSumEquiv 𝕜 complete regular divisor degree).symm.toAddMonoidHom.comp
    (DirectSum.of (fun character =>
      ↑((fan.primitiveComplementComplex 𝕜 complete regular
        (divisor + fan.principalRayDivisor character)).homology degree)) character)

theorem invariantDivisorCohomologyCharacterInclusion_injective
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (degree : ℕ) (character : Lattice →+ ℤ) :
    Function.Injective
      (fan.invariantDivisorCohomologyCharacterInclusion 𝕜 complete regular divisor degree character) :=
  (fan.invariantDivisorCohomologyWeightDirectSumEquiv 𝕜 complete regular divisor degree).symm.injective.comp
    (DirectSum.of_injective character)

theorem invariantDivisorCohomology_subsingleton_iff_all_character_homology
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (degree : ℕ) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj degree) ↔
      ∀ character : Lattice →+ ℤ, Subsingleton
        ↑((fan.primitiveComplementComplex 𝕜 complete regular
          (divisor + fan.principalRayDivisor character)).homology degree) := by
  constructor
  · intro vanishes character
    let := vanishes
    exact (fan.invariantDivisorCohomologyCharacterInclusion_injective 𝕜
      complete regular divisor degree character).subsingleton
  · intro vanish_weights
    let := vanish_weights
    exact (fan.invariantDivisorCohomologyWeightDirectSumEquiv 𝕜
      complete regular divisor degree).toEquiv.subsingleton

end TauCeti.Toric.Fan
