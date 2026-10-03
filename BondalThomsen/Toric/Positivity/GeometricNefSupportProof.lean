module

public import BondalThomsen.Toric.Positivity.WallConcavityGlobalization
public import BondalThomsen.Toric.Positivity.HigherWallGeometricNef
public import BondalThomsen.Classical.Demazure

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable {𝕜} in
noncomputable local instance geometricNefSupportBaseOver
    (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

theorem invariantDivisor_isNef_iff_raySupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) :
    AlgebraicGeometry.IsNef (baseField := 𝕜)
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ↔
      fan.HasRaySupportInequalities divisor := by
  constructor
  · intro nef
    exact fan.hasRaySupportInequalities_of_adjacentWallCartierInequalities
      complete regular divisor
      (fan.hasAdjacentWallCartierInequalities_of_isNef 𝕜 complete regular divisor nef)
  · exact fan.invariantDivisorSheaf_isNef_of_support 𝕜 complete regular divisor

end TauCeti.Toric.Fan

namespace BondalThomsen

theorem toricGeometricNefSupportCriterion_proved : ToricGeometricNefSupportCriterion 𝕜 := by
  intro Lattice Ambient additive normed normedSpace finiteDimensional embedding
    fan complete regular
  exact fun divisor => fan.invariantDivisor_isNef_iff_raySupport 𝕜 complete regular divisor

end BondalThomsen
