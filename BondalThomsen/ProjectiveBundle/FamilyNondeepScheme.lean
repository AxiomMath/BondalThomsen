module

public import BondalThomsen.ProjectiveBundle.SchemeAsymptoticLower
public import BondalThomsen.ProjectiveBundle.FanRays

@[expose] public section

open Classical AlgebraicGeometry CategoryTheory Module Filter Real

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ProjectiveBundle

noncomputable def parameterFan (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension)) :
    TauCeti.Toric.Fan
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension)) :=
  fan (baseDimension := familyWeight dimension) (fixedWeightTwist matrix)

noncomputable def parameterSchemeStructureMap (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension)) : parameterScheme 𝕜 dimension matrix ⟶ Spec (CommRingCat.of 𝕜) :=
  schemeStructureMap 𝕜 (baseDimension := familyWeight dimension) (fixedWeightTwist matrix)

theorem parameterFan_complete (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension)) : (parameterFan dimension matrix).IsComplete :=
  fan_isComplete (fixedWeightTwist matrix)

theorem parameterFan_regular (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension)) : (parameterFan dimension matrix).IsRegular :=
  fan_isRegular (fixedWeightTwist matrix)

theorem parameterSchemeStructureMap_smoothOfRelativeDimension (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension)) :
    SmoothOfRelativeDimension dimension (parameterSchemeStructureMap 𝕜 dimension matrix) := by
  have dimension_smooth := schemeStructureMap_smoothOfRelativeDimension 𝕜
    (baseDimension := familyWeight dimension) (fixedWeightTwist matrix)
  rw [family_dimension_eq] at dimension_smooth
  exact dimension_smooth

end BondalThomsen.ProjectiveBundle
