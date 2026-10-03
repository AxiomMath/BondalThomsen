module

public import BondalThomsen.Toric.RankOne.GeometricNefCriterion
public import BondalThomsen.Toric.Scheme.ValuativeStarInduction
public import BondalThomsen.LineBundle.GeometricNefClosedImmersionPullback

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module TauCeti.AlgebraicGeometry Multiplicative

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable {𝕜} in
local instance wallBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

local instance wallRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

variable {𝕜} in
local instance surfaceStarMapClosed (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (ray : fan.Ray) :
    IsClosedImmersion (fan.completeStarOrbitClosureMap 𝕜 complete regular ray) :=
  fan.completeStarOrbitClosureMap_isClosedImmersion 𝕜 complete regular ray

variable {𝕜} in
local instance surfaceStarMapOver (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (ray : fan.Ray) :
    (fan.completeStarOrbitClosureMap 𝕜 complete regular ray).IsOver
      (Spec (CommRingCat.of 𝕜)) where
  comp_over := fan.starOrbitClosureMap_comp_structureMap 𝕜 regular ray
    (fan.star_isRegular complete regular ray)

def surfaceWallRestrictedLineBundle (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (ray : fan.Ray)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    InvertibleSheaf ((fan.star ray).algebraicRealization 𝕜
      (fan.star_isRegular complete regular ray)) :=
  (InvertibleSheaf.pullback (fan.completeStarOrbitClosureMap 𝕜 complete regular ray)).obj bundle

theorem surfaceWallRestrictedLineBundle_isNef (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (ray : fan.Ray)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular))
    (nef : AlgebraicGeometry.IsNef (baseField := 𝕜) bundle.obj) :
    AlgebraicGeometry.IsNef (baseField := 𝕜)
      (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray bundle).obj :=
  nef.pullback_of_isClosedImmersion (fan.completeStarOrbitClosureMap 𝕜 complete regular ray)

section AdjacentCartierCharacters

variable (fan : Fan embedding) {firstDimension secondDimension : ℕ}
    (first : Basis (Fin firstDimension) ℤ Lattice) (firstCone : fan.IsConeBasis first)
    (second : Basis (Fin secondDimension) ℤ Lattice) (secondCone : fan.IsConeBasis second)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray)
    (firstContains : embedding ray.val ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (first index))))
    (secondContains : embedding ray.val ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (second index))))

include firstContains secondContains

end AdjacentCartierCharacters

end TauCeti.Toric.Fan
