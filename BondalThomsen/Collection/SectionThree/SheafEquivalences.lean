module

public import BondalThomsen.Toric.Cohomology.PrimitivePairCohomology
public import BondalThomsen.Collection.BondalThomsenFaithful

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Module

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.SectionThree

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    {embedding : Lattice →+ Ambient}

theorem theorem_3_1_sheaf_conditions_of_remaining_geometric_inputs
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (dimension : ℕ)
    (geometric_nef : TauCeti.AlgebraicGeometry.LineBundleClass
      (fan.algebraicRealization 𝕜 regular) → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (nef_criterion : ToricClassNefPrimitiveCriterion fan
      (fun divisorClass => geometric_nef
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass))) extremal)
    (fano_support : ToricFanoExtremalSupport fan dimension extremal)
    (primitive_cohomology : fan.PrimitiveBoundaryCohomologyNonvanishing 𝕜 complete regular)
    (frobenius : ToricFrobeniusExtDecomposition fan (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass => member)
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular))
    (kodaira : ∀ (source : fan.BondalThomsenClass) degree, 0 < degree →
      geometric_nef (Additive.toMul
        (fan.invariantDivisorPicardRealization 𝕜 complete regular (-source.val))) →
      Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular
          (-((frobenius.multiplication : ℤ) • source.val))).obj degree)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let ordered : Prop := ∃ numbering : fan.BondalThomsenClass ≃
        Fin (Fintype.card fan.BondalThomsenClass),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Ext
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular source.val).obj
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular target.val).obj degree),
          extension = 0
    let small : Prop := ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1
    let inverse_nef : Prop := ∀ member : fan.BondalThomsenClass,
      geometric_nef ((Additive.toMul
        (fan.invariantDivisorPicardRealization 𝕜 complete regular member.val))⁻¹)
    let positive_ext : Prop := PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass =>
        fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)
    (ordered ↔ small) ∧ (small ↔ inverse_nef) ∧ (inverse_nef ↔ positive_ext) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let realization := fan.invariantClassInvertibleSheaf 𝕜 complete regular
  let nef : fan.InvariantRayDivisorClass → Prop := fun divisorClass => geometric_nef
    (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass))
  have nef_equivalence :
      (∀ member : fan.BondalThomsenClass, nef (-member.val)) ↔
        (∀ member : fan.BondalThomsenClass, geometric_nef ((Additive.toMul
          (fan.invariantDivisorPicardRealization 𝕜 complete regular member.val))⁻¹)) := by
    simp only [nef, map_neg, toMul_neg]
  have ordered_small := small_extremal_of_sheafExt_backward_ordering fan complete dimension
    (fan.algebraicRealization 𝕜 regular) realization extremal fano_support
    (fan.primitiveFloorPairSheafComparison_of_boundaryCohomology 𝕜 complete regular primitive_cohomology)
  have small_nef :
      (∀ left right (relation : fan.PrimitiveLatticeRelation left right),
        extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1) →
      ∀ member : fan.BondalThomsenClass, geometric_nef ((Additive.toMul
        (fan.invariantDivisorPicardRealization 𝕜 complete regular member.val))⁻¹) := by
    intro small
    exact nef_equivalence.mp
      (inverse_bondalThomsen_nef_of_small_extremal fan nef extremal nef_criterion small)
  have nef_positive :
      (∀ member : fan.BondalThomsenClass, geometric_nef ((Additive.toMul
        (fan.invariantDivisorPicardRealization 𝕜 complete regular member.val))⁻¹)) →
      PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
        (fun member : fan.BondalThomsenClass => realization member.val) := by
    intro all_nef
    exact positive_sheafExt_vanishing_of_frobenius fan (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass => member) realization frobenius nef kodaira
      (nef_equivalence.mpr all_nef)
  have positive_ordered :
      PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
        (fun member : fan.BondalThomsenClass => realization member.val) →
      ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
        ∀ source target, numbering target < numbering source →
          ∀ degree (extension : Ext (realization source.val).obj
            (realization target.val).obj degree), extension = 0 := by
    intro positive
    apply fan.exists_invertibleSheafExt_ordering 𝕜 complete regular
      (fun member : fan.BondalThomsenClass => realization member.val) ?_ positive
    intro first second equality
    dsimp only [realization] at equality
    apply Subtype.ext
    apply fan.invariantDivisorPicardRealization_injective 𝕜 complete regular
    rw [fan.invariantClassInvertibleSheaf_class 𝕜,
      fan.invariantClassInvertibleSheaf_class 𝕜] at equality
    exact congrArg Additive.ofMul equality
  exact ⟨⟨ordered_small, fun small => positive_ordered (nef_positive (small_nef small))⟩,
    ⟨small_nef, fun all_nef => ordered_small (positive_ordered (nef_positive all_nef))⟩,
    ⟨nef_positive, fun positive => small_nef (ordered_small (positive_ordered positive))⟩⟩

end BondalThomsen.SectionThree
