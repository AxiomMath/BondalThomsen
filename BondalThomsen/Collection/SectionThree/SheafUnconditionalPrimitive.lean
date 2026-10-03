module

public import BondalThomsen.Collection.SectionThree.SheafEquivalences
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Collection.SectionThree.Equivalences
public import BondalThomsen.Toric.Cohomology.PrimitivePairCohomology
public import BondalThomsen.Toric.Frobenius.FrobeniusRemainingSteps
public import BondalThomsen.Cohomology.FiniteAffineCoverQuasicoherentExtensions
public import BondalThomsen.Toric.Frobenius.MultiplicationGlobalResidueIso
public import BondalThomsen.DeepFan.PrimitiveCoefficientCriterion
public import BondalThomsen.Rarity.DeepFanUnconditionalCounting
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryDerivedCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Module

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.SectionThree

universe derivedUniverse derivedHomUniverse

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    {embedding : Lattice →+ Ambient}

theorem theorem_3_1_sheaf_conditions_of_kodaira_nef_inputs
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (dimension : ℕ)
    (geometric_nef : TauCeti.AlgebraicGeometry.LineBundleClass
      (fan.algebraicRealization 𝕜 regular) → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (nef_criterion : ToricClassNefPrimitiveCriterion fan
      (fun divisor_class => geometric_nef
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisor_class))) extremal)
    (fano_support : ToricFanoExtremalSupport fan dimension extremal)
    (kodaira : ∀ multiplication : ℕ, 0 < multiplication →
      ∀ (source : fan.BondalThomsenClass) degree, 0 < degree →
        geometric_nef (Additive.toMul
          (fan.invariantDivisorPicardRealization 𝕜 complete regular (-source.val))) →
        Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular
            (-((multiplication : ℤ) • source.val))).obj degree)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let ordered : Prop := ∃ numbering : fan.BondalThomsenClass ≃
        Fin (Fintype.card fan.BondalThomsenClass),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Ext
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular source.val).obj
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular target.val).obj degree), extension = 0
    let small : Prop := ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1
    let inverse_nef : Prop := ∀ member : fan.BondalThomsenClass,
      geometric_nef ((Additive.toMul
        (fan.invariantDivisorPicardRealization 𝕜 complete regular member.val))⁻¹)
    let positive_ext : Prop := PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass =>
        fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)
    (ordered ↔ small) ∧ (small ↔ inverse_nef) ∧ (inverse_nef ↔ positive_ext) := by
  let decomposition := fan.toricFrobeniusExtDecomposition_of_splitting_transport 𝕜 complete regular
    (fan.toricMultiplicationResidueDecomposition 𝕜 complete regular)
    (fan.toricMultiplicationInvariantClassCohomologyTransport 𝕜 complete regular)
  exact theorem_3_1_sheaf_conditions_of_remaining_geometric_inputs 𝕜 fan complete regular dimension
    geometric_nef extremal nef_criterion fano_support
    (fan.primitiveBoundaryCohomologyNonvanishing_proved 𝕜 complete regular) decomposition
    (kodaira decomposition.multiplication decomposition.multiplication_positive)

theorem exceptional_iff_strong_of_kodaira_nef_and_derived_inputs
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {Derived : Type derivedUniverse} [Category.{derivedHomUniverse} Derived]
    [Preadditive Derived] [HasShift Derived ℤ] [Linear 𝕜 Derived]
    (objects : fan.BondalThomsenClass → Derived)
    (derived_comparison : DerivedSheafExtComparison (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass =>
        fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val) objects)
    (scalar_compatibility : DerivedSheafScalarCompatibility 𝕜
      (fan.scalarGlobalFunctionsEquiv 𝕜 complete regular) derived_comparison)
    (dimension : ℕ)
    (geometric_nef : TauCeti.AlgebraicGeometry.LineBundleClass
      (fan.algebraicRealization 𝕜 regular) → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (nef_criterion : ToricClassNefPrimitiveCriterion fan
      (fun divisor_class => geometric_nef
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisor_class))) extremal)
    (fano_support : ToricFanoExtremalSupport fan dimension extremal)
    (kodaira : ∀ multiplication : ℕ, 0 < multiplication →
      ∀ (source : fan.BondalThomsenClass) degree, 0 < degree →
        geometric_nef (Additive.toMul
          (fan.invariantDivisorPicardRealization 𝕜 complete regular (-source.val))) →
        Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular
            (-((multiplication : ℤ) • source.val))).obj degree)) :
    let exceptional : Prop := ∃ numbering : fan.BondalThomsenClass ≃
        Fin (Fintype.card fan.BondalThomsenClass),
      OrderingObstruction.IsExceptionalOrdering
        (fun member => IsExceptionalDerivedObject 𝕜 (objects member))
        (derivedNonvanishing objects) numbering
    let positive_ext : Prop := PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass =>
        fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)
    let strong : Prop := ∃ numbering : fan.BondalThomsenClass ≃
        Fin (Fintype.card fan.BondalThomsenClass),
      OrderingObstruction.IsStrongExceptionalOrdering
        (fun member => IsExceptionalDerivedObject 𝕜 (objects member))
        (derivedNonvanishing objects) numbering
    (exceptional ↔ positive_ext) ∧ (positive_ext ↔ strong) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  obtain ⟨ordered_small, small_nef, nef_positive⟩ :=
    theorem_3_1_sheaf_conditions_of_kodaira_nef_inputs 𝕜 fan complete regular dimension
      geometric_nef extremal nef_criterion fano_support kodaira
  have positive_strong : PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass =>
        fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val) →
      ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
        OrderingObstruction.IsStrongExceptionalOrdering
          (fun member => IsExceptionalDerivedObject 𝕜 (objects member))
          (derivedNonvanishing objects) numbering := by
    intro positive
    apply exists_strongExceptionalOrdering_of_integral_sheafExt 𝕜
      (fan.scalarGlobalFunctionsEquiv 𝕜 complete regular) derived_comparison scalar_compatibility
      ?_ positive
    intro first second equality
    dsimp only at equality
    apply Subtype.ext
    apply fan.invariantDivisorPicardRealization_injective 𝕜 complete regular
    rw [fan.invariantClassInvertibleSheaf_class 𝕜,
      fan.invariantClassInvertibleSheaf_class 𝕜] at equality
    exact congrArg Additive.ofMul equality
  refine ⟨⟨?_, ?_⟩, ⟨positive_strong, ?_⟩⟩
  · rintro ⟨numbering, ordering⟩
    apply ((ordered_small.trans small_nef).trans nef_positive).mp
    exact ⟨numbering, sheafExt_backward_of_derivedExceptionalOrdering 𝕜
      (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass =>
        fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)
      objects derived_comparison numbering ordering⟩
  · intro positive
    obtain ⟨numbering, ordering⟩ := positive_strong positive
    exact ⟨numbering, ordering.1⟩
  · rintro ⟨numbering, ordering⟩
    exact positive_sheafExt_of_derived_strongVanishing (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass =>
        fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)
      objects derived_comparison ordering.2

end BondalThomsen.SectionThree
