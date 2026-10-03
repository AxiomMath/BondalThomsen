module

public import BondalThomsen.Toric.Positivity.RealWallMori

@[expose] public section

set_option autoImplicit false

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem moriCone_eq_primitiveNumericalCone
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    letI : (fan.algebraicRealization 𝕜 regular).Over
        (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := ⟨fan.structureMap 𝕜 regular⟩
    BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) =
      fan.primitiveNumericalCone 𝕜 complete regular projective := by
  let : (fan.algebraicRealization 𝕜 regular).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := ⟨fan.structureMap 𝕜 regular⟩
  exact le_antisymm (fan.moriCone_le_primitiveNumericalCone 𝕜 complete regular projective)
    (fan.primitiveNumericalCone_le_moriCone 𝕜 complete regular projective)

end TauCeti.Toric.Fan

namespace BondalThomsen

theorem toricNefMoriCriterion_proved : ToricNefMoriCriterion 𝕜 := by
  intro Lattice Ambient _ _ _ _ embedding fan complete regular projective
  let : (fan.algebraicRealization 𝕜 regular).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := ⟨fan.structureMap 𝕜 regular⟩
  intro divisorClass
  exact fan.invariantClass_isNef_iff_extremalPrimitivePairings_of_moriCone_eq 𝕜
    complete regular projective
    (fan.moriCone_eq_primitiveNumericalCone 𝕜 complete regular projective) divisorClass

end BondalThomsen
