module

public import BondalThomsen.Toric.Cohomology.NegativeSupportRelativeCohomology
public import BondalThomsen.Toric.Cohomology.CechNegativeSupportComparison
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryCechNonvanishing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open TauCeti.Toric
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology

open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def cechNegativeSupportAnchor (fan : Fan embedding)
    (complete : fan.IsComplete) : Fin (Nat.card fan.cones) :=
  (Finite.equivFin fan.cones) (Classical.choice (fan.completeFan_nonemptyCones complete))

noncomputable def cechCharacterNegativeChartComplex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) : CochainComplex AddCommGrpCat ℕ :=
  negativeComplex 𝕜 (fan.cechRayChartIncidence 𝕜 complete regular)
    (fan.cechCharacterNegativeRay divisor character)

noncomputable def cechCharacterNegativeConstantAugmentation (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) :
    AddCommGrpCat.of 𝕜 ⟶ (fan.cechCharacterNegativeChartComplex 𝕜 complete regular divisor character).homology 0 :=
  negativeConstantAugmentation 𝕜 (fan.cechRayChartIncidence 𝕜 complete regular)
    (fan.cechCharacterNegativeRay divisor character) (fan.cechNegativeSupportAnchor complete)

noncomputable def cechCharacterNegativeReducedCohomology (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) : ℕ → AddCommGrpCat
  | 0 => cokernel (fan.cechCharacterNegativeConstantAugmentation 𝕜 complete regular divisor character)
  | degree + 1 => (fan.cechCharacterNegativeChartComplex 𝕜 complete regular divisor character).homology
      (degree + 1)

noncomputable def cechCharacterScalarRelativeHomologyIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) :
    (fan.primitiveComplementComplex 𝕜 complete regular
        (divisor + fan.principalRayDivisor character)).homology degree ≅
      (fan.cechNegativeSupportComplex 𝕜 complete regular divisor character).homology degree :=
  HomologicalComplex.homologyMapIso
    (fan.cechCharacterNegativeSupportIso 𝕜 complete regular divisor character) degree

end TauCeti.Toric.Fan
