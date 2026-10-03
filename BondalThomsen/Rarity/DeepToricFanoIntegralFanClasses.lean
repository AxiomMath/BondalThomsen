module

public import BondalThomsen.Rarity.ToricFanoIntegralFanClasses
public import BondalThomsen.Toric.Positivity.ActualAmpleStrictSupportCriterion
public import BondalThomsen.Fan.PrimitiveRelationDegree

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set Filter Real
open BondalThomsen.ToricTransport BondalThomsen.ProjectiveBundle
open scoped Classical Topology

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BondalThomsen

def deepIntegralFanClasses (dimension : ℕ) :
    Set (IntegralFanClass
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension))) :=
  {fanClass | ∃ fan : TauCeti.Toric.Fan
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension)),
    fan.IsComplete ∧ fan.IsRegular ∧ fan.IsDeep dimension ∧ integralFanClass fan = fanClass}

theorem deepIntegralFanClasses_finite_and_card_le_tree_bound
    (dimension : ℕ) (positiveDimension : 0 < dimension) :
    (deepIntegralFanClasses dimension).Finite ∧
      Nat.card ↥(deepIntegralFanClasses dimension) ≤ 48 ^ (4 * dimension) := by
  classical
  choose fans complete regular deep realized using
    (fun fanClass : deepIntegralFanClasses dimension => fanClass.property)
  have rangeEquality : Set.range (fun fanClass => integralFanClass (fans fanClass)) =
      deepIntegralFanClasses dimension := by
    ext fanClass
    constructor
    · rintro ⟨presented, rfl⟩
      change integralFanClass (fans presented) ∈ deepIntegralFanClasses dimension
      rw [realized presented]
      exact presented.property
    · intro member
      exact ⟨⟨fanClass, member⟩, realized ⟨fanClass, member⟩⟩
  have bound := deep_integralFanFamilyClasses_card_le_tree_bound fans complete regular deep
    (parameterLatticeDimensionBasis dimension) positiveDimension
  rwa [rangeEquality] at bound

theorem deepIntegralFanClasses_finite (dimension : ℕ) : (deepIntegralFanClasses dimension).Finite := by
  classical
  choose fans complete regular deep realized using
    (fun fanClass : deepIntegralFanClasses dimension => fanClass.property)
  have rangeEquality : Set.range (fun fanClass => integralFanClass (fans fanClass)) =
      deepIntegralFanClasses dimension := by
    ext fanClass
    constructor
    · rintro ⟨presented, rfl⟩
      change integralFanClass (fans presented) ∈ deepIntegralFanClasses dimension
      rw [realized presented]
      exact presented.property
    · intro member
      exact ⟨⟨fanClass, member⟩, realized ⟨fanClass, member⟩⟩
  have bound := deep_integralFanFamilyClasses_finite_and_card_le_ternary_of_basis
    fans complete regular deep (parameterLatticeDimensionBasis dimension)
  rw [rangeEquality] at bound
  exact bound.1

end BondalThomsen
