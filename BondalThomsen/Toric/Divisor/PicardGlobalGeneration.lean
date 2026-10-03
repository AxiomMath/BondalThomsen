module

public import BondalThomsen.LineBundle.SchemePicardGlobalGeneration
public import BondalThomsen.Toric.Divisor.PicardEffectiveOrder
public import BondalThomsen.Toric.Positivity.GlobalGenerationCriterion

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem invertibleSheafGloballyGenerated_iff_representative_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular))
    (divisor : fan.InvariantRayDivisor)
    (isomorphism : bundle.obj ≅ (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) :
    Nonempty bundle.obj.GeneratingSections ↔ fan.HasRaySupportInequalities divisor :=
  (SheafOfModules.GeneratingSections.equivOfIso isomorphism).nonempty_congr.trans
    (fan.invariantDivisorGloballyGenerated_iff_support 𝕜 complete regular divisor)

end TauCeti.Toric.Fan
