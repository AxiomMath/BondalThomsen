module

public import BondalThomsen.Rarity.IntegralFanClassRarity
public import BondalThomsen.ProjectiveBundle.ConeRigidity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set Filter Real
open BondalThomsen.ToricTransport
open scoped Classical Topology

namespace BondalThomsen.ProjectiveBundle

variable {rows ones columns : ℕ}

theorem integralRayFanEquiv_class_support_iff
    (first second : FixedWeightMatrix rows columns ones)
    (equivalence : IntegralRayFanEquiv
      (fan (baseDimension := ones) (fixedWeightTwist second))
      (fan (baseDimension := ones) (fixedWeightTwist first)))
    (divisorClass : (fan (baseDimension := ones) (fixedWeightTwist second)).InvariantRayDivisorClass) :
    divisorClass ∈ raySupportClassCone (baseDimension := ones) (fixedWeightTwist second) ↔
      equivalence.classEquiv divisorClass ∈
        raySupportClassCone (baseDimension := ones) (fixedWeightTwist first) := by
  constructor
  · rintro ⟨divisor, equality, support⟩
    refine ⟨equivalence.divisorEquiv divisor, ?_, ?_⟩
    · rw [← equality, equivalence.classEquiv_mk]
    · exact (equivalence.hasRaySupportInequalities_iff divisor).mpr support
  · rintro ⟨divisor, equality, support⟩
    let original := equivalence.divisorEquiv.symm divisor
    have mapped : equivalence.divisorEquiv original = divisor :=
      equivalence.divisorEquiv.apply_symm_apply divisor
    refine ⟨original, ?_, ?_⟩
    · apply equivalence.classEquiv.injective
      rw [equivalence.classEquiv_mk, mapped, equality]
    · apply (equivalence.hasRaySupportInequalities_iff original).mp
      rwa [mapped]

theorem augmentedPermutationEquivalent_of_integralRayFanEquiv
    (first second : FixedWeightMatrix rows columns ones)
    (basePositive : 0 < ones) (fiberPositive : 0 < columns)
    (equivalence : IntegralRayFanEquiv
      (fan (baseDimension := ones) (fixedWeightTwist second))
      (fan (baseDimension := ones) (fixedWeightTwist first))) :
    AugmentedPermutationEquivalent first second := by
  apply augmentedPermutationEquivalent_of_ray_support_cone first second basePositive fiberPositive
    equivalence.rays equivalence.principal_range_map_eq
  intro divisorClass
  exact integralRayFanEquiv_class_support_iff first second equivalence divisorClass

theorem augmentedPermutationEquivalent_of_integralFanClass_eq
    (first second : FixedWeightMatrix rows columns ones)
    (basePositive : 0 < ones) (fiberPositive : 0 < columns)
    (equality : integralFanClass (fan (baseDimension := ones) (fixedWeightTwist first)) =
      integralFanClass (fan (baseDimension := ones) (fixedWeightTwist second))) :
    AugmentedPermutationEquivalent first second := by
  obtain ⟨equivalence⟩ := (integralFanClass_eq_iff _ _).mp equality.symm
  exact augmentedPermutationEquivalent_of_integralRayFanEquiv
    first second basePositive fiberPositive equivalence

theorem parameterIntegralFanClass_fiber_card_le (dimension : ℕ)
    (basePositive : 0 < familyWeight dimension) (fiberPositive : 0 < familyColumns dimension)
    (target : IntegralFanClass
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension))) :
    (Finset.univ.filter (fun matrix : FixedWeightMatrix (familyRows dimension)
      (familyColumns dimension) (familyWeight dimension) =>
        integralFanClass (parameterFan dimension matrix) = target)).card ≤
      (familyRows dimension).factorial * (familyColumns dimension + 1).factorial :=
  fixedWeightMatrix_fiber_bound_of_augmented_rigidity
    (fun matrix => integralFanClass (parameterFan dimension matrix))
    (fun first second same => augmentedPermutationEquivalent_of_integralFanClass_eq
      first second basePositive fiberPositive same) target

theorem parameterIntegralFanClasses_exp_lower (dimension : ℕ)
    (logLarge : 2 ≤ log dimension) (dimensionLarge : 16 * (log dimension) ^ 2 ≤ dimension) :
    exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
      10 * dimension) ≤ (Nat.card ↥(parameterIntegralFanClasses dimension) : ℝ) := by
  let := (parameterIntegralFanClasses_finite dimension).fintype
  obtain ⟨basePositive, weightLe, _, _, _, _, _, _⟩ :=
    family_parameter_bounds dimension logLarge dimensionLarge
  have fiberPositive : 0 < familyColumns dimension := by omega
  let classify : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension) → parameterIntegralFanClasses dimension :=
    fun matrix => ⟨integralFanClass (parameterFan dimension matrix), matrix, rfl⟩
  have bound := projective_bundle_family_exp_lower dimension logLarge dimensionLarge classify (by
    intro target
    have equality : (Finset.univ.filter (fun matrix => classify matrix = target)) =
        Finset.univ.filter (fun matrix => integralFanClass (parameterFan dimension matrix) = target.val) := by
      ext matrix
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Subtype.ext_iff
    rw [equality]
    exact parameterIntegralFanClass_fiber_card_le dimension basePositive fiberPositive target.val)
  simpa only [Nat.card_eq_fintype_card] using bound

theorem parameterIntegralFanClasses_exp_lower_eventually :
    ∀ᶠ dimension : ℕ in atTop,
      exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
        10 * dimension) ≤ (Nat.card ↥(parameterIntegralFanClasses dimension) : ℝ) :=
  family_parameter_bounds_eventually.mono fun dimension bound =>
    parameterIntegralFanClasses_exp_lower dimension bound.1 bound.2

end BondalThomsen.ProjectiveBundle
