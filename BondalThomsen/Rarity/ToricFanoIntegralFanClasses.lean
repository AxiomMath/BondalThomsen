module

public import BondalThomsen.Rarity.IntegralFanClassRarity
public import BondalThomsen.Rarity.ToricFanoSchemeClasses

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set Filter Real
open BondalThomsen.ToricTransport BondalThomsen.ProjectiveBundle
open scoped Classical Topology

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BondalThomsen

def smoothProjectiveToricFanoIntegralFanClasses (dimension : ℕ) :
    Set (IntegralFanClass
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension))) :=
  {fanClass | ∃ fan : TauCeti.Toric.Fan
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension)),
    ∃ (complete : fan.IsComplete) (regular : fan.IsRegular),
      integralFanClass fan = fanClass ∧
      SmoothOfRelativeDimension dimension (fan.structureMap 𝕜 regular) ∧
      (∃ Index : Type, Finite Index ∧
        ∃ closedMap : fan.algebraicRealization 𝕜 regular ⟶
            Proj (MvPolynomial.homogeneousSubmodule Index 𝕜),
          IsClosedImmersion closedMap ∧
            closedMap ≫ polynomialProjStructureMap 𝕜 Index = fan.structureMap 𝕜 regular) ∧
      (letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete);
        SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹))}

namespace ProjectiveBundle

noncomputable def parameterLatticeDimensionBasis (dimension : ℕ) :
    Basis (Fin dimension) ℤ
      (ProjectiveBundle.Lattice (familyRows dimension) (familyWeight dimension) (familyColumns dimension)) :=
  (standardBasis (familyRows dimension) (familyWeight dimension) (familyColumns dimension)).reindex
    (Fintype.equivOfCardEq (by
      simp only [Coordinate, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      exact family_dimension_eq dimension))

theorem parameterFanClass_mem_smoothProjectiveToricFanoIntegralFanClasses
    (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension) (familyWeight dimension))
    (basePositive : 0 < familyWeight dimension) (fiberPositive : 0 < familyColumns dimension) :
    integralFanClass (parameterFan dimension matrix) ∈
      smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension := by
  refine ⟨parameterFan dimension matrix, parameterFan_complete dimension matrix,
    parameterFan_regular dimension matrix, rfl, ?_, ?_, ?_⟩
  · exact parameterSchemeStructureMap_smoothOfRelativeDimension 𝕜 dimension matrix
  · exact parameterScheme_projectiveClosedEmbedding 𝕜 dimension matrix basePositive fiberPositive
  · exact parameterScheme_inverseCanonicalClass_isAmple 𝕜 dimension matrix basePositive fiberPositive

theorem parameterFanClass_mem_smoothProjectiveToricFanoIntegralFanClasses_eventually :
    ∀ᶠ dimension : ℕ in atTop,
      ∀ matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
        (familyWeight dimension),
        integralFanClass (parameterFan dimension matrix) ∈
          smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension := by
  filter_upwards [family_parameter_bounds_eventually] with dimension bounds
  obtain ⟨logLarge, dimensionLarge⟩ := bounds
  obtain ⟨basePositive, weightLe, _, _, _, _, _, _⟩ :=
    family_parameter_bounds dimension logLarge dimensionLarge
  have fiberPositive : 0 < familyColumns dimension := by
    omega
  exact fun matrix => parameterFanClass_mem_smoothProjectiveToricFanoIntegralFanClasses 𝕜
    dimension matrix basePositive fiberPositive

end ProjectiveBundle

end BondalThomsen
