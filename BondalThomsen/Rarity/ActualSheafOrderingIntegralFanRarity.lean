module

public import BondalThomsen.DeepFan.ActualSheafOrderingDeepFan
public import BondalThomsen.Rarity.FanoIntegralRarity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Module Set Filter Real
open TauCeti.AlgebraicGeometry TauCeti.Toric.Fan
open BondalThomsen.ToricTransport BondalThomsen.ProjectiveBundle BondalThomsen.SectionThree
open scoped Classical Topology

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

theorem theorem_1_3_of_actualSheafExt_backward_presentations_and_geometricNef_inputs
    (classes : ∀ dimension : ℕ, Set (IntegralFanClass
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension))))
    (fans : ∀ dimension, classes dimension → TauCeti.Toric.Fan
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension)))
    (complete : ∀ dimension fanClass, (fans dimension fanClass).IsComplete)
    (regular : ∀ dimension fanClass, (fans dimension fanClass).IsRegular)
    (realized : ∀ dimension fanClass, integralFanClass (fans dimension fanClass) = fanClass.val)
    (extremal : ∀ dimension fanClass (left right : Finset (fans dimension fanClass).Ray),
      (fans dimension fanClass).PrimitiveLatticeRelation left right → Prop)
    (canonicalInverseAmple : ∀ dimension fanClass,
      letI := (fans dimension fanClass).algebraicRealization_isIntegral 𝕜
        (regular dimension fanClass) ((fans dimension fanClass).completeFan_nonemptyCones
          (complete dimension fanClass))
      SchemeLineBundleClassAmple (((fans dimension fanClass).toricCanonicalLineBundleClass 𝕜
        (complete dimension fanClass) (regular dimension fanClass))⁻¹))
    (incidence : ∀ dimension fanClass,
      ToricExtremalDropOneConeIncidence (fans dimension fanClass) (extremal dimension fanClass))
    (nefNecessarySupport : ∀ dimension fanClass,
      letI : ((fans dimension fanClass).algebraicRealization 𝕜 (regular dimension fanClass)).Over
          (Spec (CommRingCat.of 𝕜)) :=
        ⟨(fans dimension fanClass).structureMap 𝕜 (regular dimension fanClass)⟩
      ToricNefSupportCriterion (fans dimension fanClass) dimension (fun divisor =>
        SchemeLineBundleClassIsNef (baseField := 𝕜) (LineBundleClass.mk
          ((fans dimension fanClass).invariantDivisorLineBundle 𝕜
            (complete dimension fanClass) (regular dimension fanClass) divisor))))
    (nefPrimitiveCriterion : ∀ dimension fanClass,
      letI : ((fans dimension fanClass).algebraicRealization 𝕜 (regular dimension fanClass)).Over
          (Spec (CommRingCat.of 𝕜)) :=
        ⟨(fans dimension fanClass).structureMap 𝕜 (regular dimension fanClass)⟩
      ToricClassNefPrimitiveCriterion (fans dimension fanClass)
        (fun divisorClass => SchemeLineBundleClassIsNef (baseField := 𝕜) (Additive.toMul
          ((fans dimension fanClass).invariantDivisorPicardRealization 𝕜
            (complete dimension fanClass) (regular dimension fanClass) divisorClass)))
        (extremal dimension fanClass))
    (ordering : ∀ dimension fanClass,
      ∃ numbering : (fans dimension fanClass).BondalThomsenClass ≃
          Fin (Fintype.card (fans dimension fanClass).BondalThomsenClass),
        ∀ first second, numbering second < numbering first →
          ∀ degree (extension : Ext
            ((fans dimension fanClass).invariantClassInvertibleSheaf 𝕜
              (complete dimension fanClass) (regular dimension fanClass) first.val).obj
            ((fans dimension fanClass).invariantClassInvertibleSheaf 𝕜
              (complete dimension fanClass) (regular dimension fanClass) second.val).obj degree),
            extension = 0) :
    (∀ dimension, (classes dimension).Finite) ∧
      ∃ constant : ℝ, 0 < constant ∧
        (∀ᶠ dimension : ℕ in atTop,
          (Nat.card ↥(classes dimension) : ℝ) ≤ exp (constant * dimension) ∧
          exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
            constant * dimension) ≤
              (Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) : ℝ)) ∧
        Tendsto (fun dimension => (Nat.card ↥(classes dimension) : ℝ) /
          Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension)) atTop (𝓝 0) := by
  apply theorem_1_3_integralFanClasses_of_deep_presentations 𝕜 classes fans complete regular _ realized
  intro dimension fanClass
  exact deep_of_actualSheafExt_backward_ordering_of_actualFano_and_geometricNef_inputs 𝕜
    (fans dimension fanClass) (complete dimension fanClass) (regular dimension fanClass)
    (parameterLatticeDimensionBasis dimension) (extremal dimension fanClass)
    (canonicalInverseAmple dimension fanClass) (incidence dimension fanClass)
    (nefNecessarySupport dimension fanClass) (nefPrimitiveCriterion dimension fanClass)
    (ordering dimension fanClass)

end BondalThomsen
