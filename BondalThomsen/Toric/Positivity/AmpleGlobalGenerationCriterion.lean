module

public import BondalThomsen.LineBundle.AmpleLineBundleGlobalGeneration
public import BondalThomsen.Toric.Positivity.SemiampleClassCriterion
public import BondalThomsen.LineBundle.AmpleLineBundleClassCriterion

@[expose] public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem invertibleSheafGloballyGenerated_of_isAmple
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular))
    (ample : IsAmple bundle.obj) : Nonempty bundle.obj.GeneratingSections :=
  (fan.invertibleSheafSemiample_iff_globallyGenerated 𝕜 complete regular bundle).mp
    (BondalThomsen.invertibleSheafSemiample_of_isAmple bundle ample)

theorem divisor_hasRaySupportInequalities_of_isAmple
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (ample : IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) :
    fan.HasRaySupportInequalities divisor :=
  (fan.invariantDivisorGloballyGenerated_iff_support 𝕜 complete regular divisor).mp
    (fan.invertibleSheafGloballyGenerated_of_isAmple 𝕜 complete regular _ ample)

end TauCeti.Toric.Fan
