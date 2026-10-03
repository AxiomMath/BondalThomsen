module

public import BondalThomsen.Rarity.DeepToricFanoIntegralRarity
public import BondalThomsen.Collection.SectionThree.ActualFanoSupport
public import BondalThomsen.LineBundle.PicardGeometricNef
public import BondalThomsen.Toric.Positivity.SemiampleClassCriterion
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Collection.SectionThree.Equivalences
public import BondalThomsen.Toric.Cohomology.PrimitivePairCohomology
public import BondalThomsen.Toric.Frobenius.FrobeniusRemainingSteps
public import BondalThomsen.Cohomology.FiniteAffineCoverQuasicoherentExtensions
public import BondalThomsen.Toric.Frobenius.MultiplicationGlobalResidueIso
public import BondalThomsen.DeepFan.PrimitiveCoefficientCriterion
public import BondalThomsen.Rarity.DeepFanUnconditionalCounting
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryDerivedCohomology
public import BondalThomsen.Toric.Cohomology.NefFirstCohomologyVanishing
public import BondalThomsen.Fan.SmoothFanoIntegralFanClassFiniteness

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set Filter Real
open TauCeti.AlgebraicGeometry TauCeti.Toric.Fan
open BondalThomsen.ToricTransport BondalThomsen.ProjectiveBundle BondalThomsen.SectionThree
open scoped Classical Topology

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

universe derivedUniverse derivedHomUniverse

theorem integralFanClasses_subset_deep_of_presentations
    (dimension : ℕ)
    (classes : Set (IntegralFanClass
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension))))
    (fans : classes → TauCeti.Toric.Fan
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension)))
    (complete : ∀ fanClass, (fans fanClass).IsComplete)
    (regular : ∀ fanClass, (fans fanClass).IsRegular)
    (deep : ∀ fanClass, (fans fanClass).IsDeep dimension)
    (realized : ∀ fanClass, integralFanClass (fans fanClass) = fanClass.val) :
    classes ⊆ deepIntegralFanClasses dimension := by
  intro fanClass membership
  exact ⟨fans ⟨fanClass, membership⟩, complete _, regular _, deep _, realized _⟩

theorem theorem_1_3_integralFanClasses_of_deep_presentations
    (classes : ∀ dimension : ℕ, Set (IntegralFanClass
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension))))
    (fans : ∀ dimension, classes dimension → TauCeti.Toric.Fan
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension)))
    (complete : ∀ dimension fanClass, (fans dimension fanClass).IsComplete)
    (regular : ∀ dimension fanClass, (fans dimension fanClass).IsRegular)
    (deep : ∀ dimension fanClass, (fans dimension fanClass).IsDeep dimension)
    (realized : ∀ dimension fanClass, integralFanClass (fans dimension fanClass) = fanClass.val) :
    (∀ dimension, (classes dimension).Finite) ∧
      ∃ constant : ℝ, 0 < constant ∧
        (∀ᶠ dimension : ℕ in atTop,
          (Nat.card ↥(classes dimension) : ℝ) ≤ exp (constant * dimension) ∧
          exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
            constant * dimension) ≤
              (Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) : ℝ)) ∧
        Tendsto (fun dimension => (Nat.card ↥(classes dimension) : ℝ) /
          Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension)) atTop (𝓝 0) := by
  have subset := fun dimension => integralFanClasses_subset_deep_of_presentations dimension
    (classes dimension) (fans dimension) (complete dimension) (regular dimension)
    (deep dimension) (realized dimension)
  have finiteClasses : ∀ dimension, (classes dimension).Finite := fun dimension =>
    (deepIntegralFanClasses_finite dimension).subset (subset dimension)
  have cardinality : ∀ dimension,
      Nat.card ↥(classes dimension) ≤ Nat.card ↥(deepIntegralFanClasses dimension) := by
    intro dimension
    let := (deepIntegralFanClasses_finite dimension).fintype
    exact Nat.card_le_card_of_injective (Set.inclusion (subset dimension))
      (Set.inclusion_injective (subset dimension))
  obtain ⟨constant, positive, bounds, _⟩ :=
    theorem_1_3_deepFanoIntegralFanClasses 𝕜
      (smoothProjectiveToricFanoIntegralFanClasses_finite 𝕜)
  have upper : ∀ᶠ dimension : ℕ in atTop,
      (Nat.card ↥(classes dimension) : ℝ) ≤ exp (constant * dimension) := by
    filter_upwards [bounds] with dimension bound
    apply le_trans _ bound.1
    exact_mod_cast cardinality dimension
  have lower := bounds.mono (fun _ bound => bound.2)
  refine ⟨finiteClasses, constant, positive, ?_, ?_⟩
  · filter_upwards [upper, lower] with dimension upperBound lowerBound
    exact ⟨upperBound, lowerBound⟩
  · exact asymptotic_rarity_of_bounds _ _ constant (fun dimension => Nat.cast_nonneg _)
      upper lower

end BondalThomsen
