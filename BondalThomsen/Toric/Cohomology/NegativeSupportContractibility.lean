module

public import BondalThomsen.Cohomology.ConvexNerve.GlobalCarrierHomotopy
public import BondalThomsen.Toric.Cohomology.NefFirstCohomologyVanishing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open TauCeti.Toric CategoryTheory
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveGlobalCarrierHomotopy
open BondalThomsen.ToricCechNegativeSupportComparison
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] Classical.decEq

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def negativeChartActiveNerve (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) :=
  activeNerve (fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character)

theorem divisorForbiddenChartPatch_convex_of_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)
    (character : Lattice →+ ℤ) (chart : Fin (Nat.card fan.cones)) :
    Convex ℝ (fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character chart) :=
  (fan.divisorLocalCone 𝕜 complete regular chart).val.convex.inter
    (fan.divisorWeightForbiddenRegion_convex complete regular divisor support character)

theorem negativeChartActiveNerve_contractible_of_support_negativeRay (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)
    (character : Lattice →+ ℤ) (negative : ∃ ray : fan.Ray, fan.cechCharacterNegativeRay divisor character ray) :
    ContractibleSpace
      (AbstractSimplicialComplex.Realization (fan.negativeChartActiveNerve 𝕜 complete regular divisor character)) :=
  entireNerve_contractible (fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character)
    (fan.divisorWeightForbiddenRegion complete regular divisor character)
    (fan.divisorWeightForbiddenRegion_convex complete regular divisor support character)
    ((fan.divisorWeightForbiddenRegion_nonempty_iff_negativeRay complete regular divisor character).mpr negative)
    (fun _chart _point member => member.2)
    (fan.divisorForbiddenChartPatch_convex_of_support 𝕜 complete regular divisor support character)
    (fan.divisorForbiddenChartPatch_isClosed_in_region 𝕜 complete regular divisor character)
    (fan.divisorForbiddenChartPatch_cover 𝕜 complete regular divisor character)

end TauCeti.Toric.Fan
