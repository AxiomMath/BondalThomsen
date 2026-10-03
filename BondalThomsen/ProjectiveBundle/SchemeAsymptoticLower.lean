module

public import BondalThomsen.Toric.Divisor.PicardEquivalence
public import BondalThomsen.ProjectiveBundle.Scheme
public import BondalThomsen.ProjectiveBundle.NefSupport
public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Toric.Positivity.GlobalGenerationCriterion
public import BondalThomsen.ProjectiveBundle.ConeRigidity
public import BondalThomsen.LineBundle.SchemePicardGlobalGeneration
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import BondalThomsen.Derived.LineBundleCollectionOrder
public import BondalThomsen.Ports.TauCeti.RingTheory.LocalRing.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.LocalRing.Basic
public import BondalThomsen.Toric.Divisor.PicardFaithfulness
public import BondalThomsen.ProjectiveBundle.DivisorClasses
public import BondalThomsen.Rarity.DeepFanSchemeCountingRigidity
public import BondalThomsen.Toric.Scheme.FanEquivSchemeIso
public import BondalThomsen.Rarity.Counting
public import Mathlib.CategoryTheory.Skeletal
public import BondalThomsen.Matroid.ColumnPermutationRigidity
public import BondalThomsen.Rarity.TreeEncoding
public import BondalThomsen.Rarity.AsymptoticRarity
public import BondalThomsen.Rarity.FamilyParameters

@[expose] public section

open Classical AlgebraicGeometry CategoryTheory Filter Real

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ProjectiveBundle

noncomputable def parameterScheme (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension)) : Scheme :=
  scheme 𝕜 (baseDimension := familyWeight dimension) (fixedWeightTwist matrix)

end BondalThomsen.ProjectiveBundle
