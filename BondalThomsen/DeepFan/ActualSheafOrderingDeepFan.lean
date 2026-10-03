module

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

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Module
open TauCeti.AlgebraicGeometry TauCeti.Toric.Fan

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.SectionThree

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    {embedding : Lattice →+ Ambient}

theorem small_extremal_of_actualSheafExt_backward_ordering_of_actualFano
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (reference : Basis (Fin dimension) ℤ Lattice)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (canonicalInverseAmple :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹))
    (incidence : ToricExtremalDropOneConeIncidence fan extremal)
    (ordering : ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
      ∀ first second, numbering second < numbering first →
        ∀ degree (extension : Ext
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular first.val).obj
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular second.val).obj degree),
          extension = 0) :
    ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1 :=
  small_extremal_of_sheafExt_backward_ordering_of_actualCanonicalInverse_isAmple 𝕜
    fan complete regular reference (fan.algebraicRealization 𝕜 regular)
    (fan.invariantClassInvertibleSheaf 𝕜 complete regular) extremal canonicalInverseAmple incidence
    (fan.primitiveFloorPairSheafComparison_proved 𝕜 complete regular) ordering

theorem deep_of_actualSheafExt_backward_ordering_of_actualFano_and_geometricNef_inputs
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (reference : Basis (Fin dimension) ℤ Lattice)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (canonicalInverseAmple :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹))
    (incidence : ToricExtremalDropOneConeIncidence fan extremal)
    (nefNecessarySupport :
      letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
        ⟨fan.structureMap 𝕜 regular⟩
      ToricNefSupportCriterion fan dimension (fun divisor =>
        SchemeLineBundleClassIsNef (baseField := 𝕜) (LineBundleClass.mk
          (fan.invariantDivisorLineBundle 𝕜 complete regular divisor))))
    (nefPrimitiveCriterion :
      letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
        ⟨fan.structureMap 𝕜 regular⟩
      ToricClassNefPrimitiveCriterion fan
        (fun divisorClass => SchemeLineBundleClassIsNef (baseField := 𝕜)
          (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass)))
        extremal)
    (ordering : ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
      ∀ first second, numbering second < numbering first →
        ∀ degree (extension : Ext
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular first.val).obj
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular second.val).obj degree),
          extension = 0) : fan.IsDeep dimension := by
  let : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨fan.structureMap 𝕜 regular⟩
  let nefClass : fan.InvariantRayDivisorClass → Prop := fun divisorClass =>
    SchemeLineBundleClassIsNef (baseField := 𝕜)
      (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass))
  have necessary : ToricNefSupportCriterion fan dimension
      (fun divisor => nefClass (fan.invariantRayDivisorClass divisor)) := by
    intro divisor nef basis coneBasis ray
    apply nefNecessarySupport divisor _ basis coneBasis ray
    simpa only [nefClass, fan.invariantDivisorPicardRealization_apply 𝕜, toMul_ofMul] using nef
  exact deep_of_small_extremal_primitive_coefficients fan regular dimension
    (fun divisor => nefClass (fan.invariantRayDivisorClass divisor)) extremal necessary
    (extremalPrimitiveNegativeWitness_of_classNefCriterion fan nefClass extremal nefPrimitiveCriterion)
    (small_extremal_of_actualSheafExt_backward_ordering_of_actualFano 𝕜 fan complete regular reference
      extremal canonicalInverseAmple incidence ordering)

end BondalThomsen.SectionThree
