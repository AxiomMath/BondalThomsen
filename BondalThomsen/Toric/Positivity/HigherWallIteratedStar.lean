module

public import BondalThomsen.Toric.Surface.WallRestrictionDescent
public import BondalThomsen.Fan.Interior

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance iteratedStarRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

variable {𝕜} in
local instance iteratedStarBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def RayStarChain (steps : ℕ) {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient} (fan : Fan embedding) : Type :=
  match steps with
  | 0 => PUnit
  | steps + 1 => Σ ray : fan.Ray, RayStarChain steps (fan.star ray)

def iteratedStarScheme (steps : ℕ) {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient} (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (chain : RayStarChain steps fan) : Scheme :=
  match steps with
  | 0 => fan.algebraicRealization 𝕜 regular
  | steps + 1 => iteratedStarScheme steps (fan.star chain.1)
      (fan.star_isComplete_of_isComplete complete chain.1)
      (fan.star_isRegular complete regular chain.1) chain.2

def iteratedStarLatticeRank (steps : ℕ) {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient} (fan : Fan embedding) (chain : RayStarChain steps fan) : ℕ :=
  match steps with
  | 0 => Module.finrank ℤ Lattice
  | steps + 1 => (fan.star chain.1).iteratedStarLatticeRank steps chain.2

theorem starLattice_finrank_add_one (fan : Fan embedding) (ray : fan.Ray) :
    Module.finrank ℤ (fan.StarLattice ray) + 1 = Module.finrank ℤ Lattice := by
  rw [← (fan.star ray).lattice.isBaseChange.finrank_eq,
    ← fan.lattice.isBaseChange.finrank_eq]
  exact fan.starAmbient_finrank_add_one ray

theorem iteratedStarLatticeRank_add_steps (steps : ℕ) {Lattice Ambient : Type}
    [AddCommGroup Lattice] [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}
    (fan : Fan embedding) (chain : RayStarChain steps fan) :
    fan.iteratedStarLatticeRank steps chain + steps = Module.finrank ℤ Lattice := by
  induction steps generalizing Lattice Ambient with
  | zero => simp [iteratedStarLatticeRank]
  | succ steps inductionHypothesis =>
    have smaller := inductionHypothesis (fan.star chain.1) chain.2
    have drop := fan.starLattice_finrank_add_one chain.1
    change (fan.star chain.1).iteratedStarLatticeRank steps chain.2 + (steps + 1) = _
    omega

def iteratedStarIntegralCurve (steps : ℕ) {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient} (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (chain : RayStarChain steps fan)
    (rankOne : fan.iteratedStarLatticeRank steps chain = 1) :
    IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular) :=
  match steps with
  | 0 => by
      letI := fan.lattice.free
      letI := fan.lattice.finite
      exact fan.rankOneIntegralCurve 𝕜 complete regular
        (Module.finBasisOfFinrankEq ℤ Lattice rankOne)
  | steps + 1 => by
      letI := fan.completeStarOrbitClosureMap_isClosedImmersion 𝕜 complete regular chain.1
      letI : (fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1).IsOver
          (Spec (CommRingCat.of 𝕜)) :=
        ⟨fan.starOrbitClosureMap_comp_structureMap 𝕜 regular chain.1
          (fan.star_isRegular complete regular chain.1)⟩
      exact ((fan.star chain.1).iteratedStarIntegralCurve steps
        (fan.star_isComplete_of_isComplete complete chain.1)
        (fan.star_isRegular complete regular chain.1) chain.2 rankOne).mapClosedImmersion
          (fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)

theorem iteratedStarChain_rank_one_iff (steps : ℕ) (fan : Fan embedding)
    (chain : RayStarChain steps fan) :
    fan.iteratedStarLatticeRank steps chain = 1 ↔ steps + 1 = Module.finrank ℤ Lattice := by
  have rank := fan.iteratedStarLatticeRank_add_steps steps chain
  omega

def iteratedStarCurveLineBundleDegree (steps : ℕ) (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (chain : RayStarChain steps fan)
    (rankOne : fan.iteratedStarLatticeRank steps chain = 1)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) : ℤ :=
  (fan.iteratedStarIntegralCurve 𝕜 steps complete regular chain rankOne).lineBundleDegree
    ((Scheme.Modules.pullback (fan.iteratedStarIntegralCurve 𝕜 steps complete regular chain rankOne).ι).obj
      bundle.obj)

end TauCeti.Toric.Fan
