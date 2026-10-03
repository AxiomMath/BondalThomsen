module

public import BondalThomsen.Cohomology.ConvexNerve.DualCochainComparison
public import BondalThomsen.Cohomology.ConvexNerve.IncidenceSingularChainEquivalence

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceHomologyComparison
open BondalThomsen.ConvexNerveAcyclicCarrierAssembly
open BondalThomsen.ConvexNerveDualCochainComparison
open BondalThomsen.ConvexNerveIncidenceSingularChainEquivalence
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ConvexNerveAugmentedCochainComparison

noncomputable section

def singleChainContraction {chains : ChainComplex AddCommGrpCat.{0} ℕ}
    {coefficient : AddCommGrpCat.{0}}
    (equivalence : HomotopyEquiv chains ((ChainComplex.single₀ AddCommGrpCat.{0}).obj coefficient))
    (degree : ℕ) : chains.X degree ⟶ chains.X (degree + 1) :=
  -(equivalence.homotopyHomInvId.hom degree (degree + 1))

theorem singleChainContraction_identity_zero {chains : ChainComplex AddCommGrpCat.{0} ℕ}
    {coefficient : AddCommGrpCat.{0}}
    (equivalence : HomotopyEquiv chains ((ChainComplex.single₀ AddCommGrpCat.{0}).obj coefficient)) :
    singleChainContraction equivalence 0 ≫ chains.d 1 0 =
      𝟙 _ - equivalence.hom.f 0 ≫ equivalence.inv.f 0 := by
  have identity := equivalence.homotopyHomInvId.comm 0
  rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex] at identity
  change equivalence.hom.f 0 ≫ equivalence.inv.f 0 = _ at identity
  change (-equivalence.homotopyHomInvId.hom 0 1) ≫ _ = _
  rw [neg_comp]
  have rearranged := congrArg (fun value => 𝟙 (chains.X 0) - value) identity
  have reversed := rearranged.symm
  change 𝟙 (chains.X 0) -
    (equivalence.homotopyHomInvId.hom 0 1 ≫ chains.d 1 0 + 𝟙 (chains.X 0)) = _ at reversed
  have cancellation : ∀ value : chains.X 0 ⟶ chains.X 0,
      𝟙 _ - (value + 𝟙 _) = -value := by intro value; abel
  rw [cancellation] at reversed
  exact reversed

variable {Ray : Type*} {Chart : Type}

theorem incidenceAugmentedContraction_identity_zero
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (equivalence : HomotopyEquiv (incidenceChains incidence negative)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject))
    (augmentation : equivalence.hom = incidenceChainAugmentationMap incidence negative) :
    singleChainContraction equivalence 0 ≫ (incidenceChains incidence negative).d 1 0 =
      𝟙 _ - incidenceChainAugmentation incidence negative ≫ equivalence.inv.f 0 := by
  simpa only [augmentation, incidenceChainAugmentation] using
    singleChainContraction_identity_zero equivalence

theorem negativeReducedDegreeZero_isZero_of_augmentedHomotopyEquiv
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (equivalence : HomotopyEquiv (incidenceChains incidence negative)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject))
    (augmentation : equivalence.hom = incidenceChainAugmentationMap incidence negative) (anchor : Chart) :
    IsZero (negativeAugmentedDegreeZero 𝕜 incidence negative anchor) :=
  negativeAugmentedDegreeZero_isZero_of_augmentedChainContraction 𝕜 incidence negative
    (equivalence.inv.f 0) (singleChainContraction equivalence 0)
    (incidenceAugmentedContraction_identity_zero incidence negative equivalence augmentation) anchor

theorem incidenceRelativeHomology_positive_isZero_of_augmentedHomotopyEquiv
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (equivalence : HomotopyEquiv (incidenceChains incidence negative)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject))
    (augmentation : equivalence.hom = incidenceChainAugmentationMap incidence negative)
    (anchor : Chart) (degree : ℕ) :
    IsZero ((relativeComplex 𝕜 incidence negative).homology (degree + 1)) := by
  cases degree with
  | zero =>
    exact (negativeReducedDegreeZero_isZero_of_augmentedHomotopyEquiv 𝕜
      incidence negative equivalence augmentation anchor).of_iso
        (negativeAugmentedDegreeZeroShiftIso 𝕜 incidence negative anchor).symm
  | succ degree =>
    exact (incidenceCochain_positive_isZero_of_chainHomotopyEquiv_single 𝕜 incidence negative
      incidenceAugmentationObject equivalence degree).of_iso
        (negativePositiveHomologyShiftIso 𝕜 incidence negative anchor degree).symm

section CanonicalSingularComparison

variable [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
variable (equivalence : HomotopyEquiv (incidenceChains incidence negative)
  (integralSingularChains (incidenceRealization incidence negative)))
variable (canonical : equivalence.hom = affineSingularChainMap incidence negative)

variable [ContractibleSpace (incidenceRealization incidence negative)]

def contractibleIncidenceChainAugmentationHomotopyEquiv :
    HomotopyEquiv (incidenceChains incidence negative)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject) :=
  equivalence.trans
    (contractibleSingularChainAugmentationHomotopyEquiv (incidenceRealization incidence negative))

include canonical in
theorem contractibleIncidenceChainAugmentationHomotopyEquiv_hom :
    (contractibleIncidenceChainAugmentationHomotopyEquiv incidence negative equivalence).hom =
      incidenceChainAugmentationMap incidence negative := by
  change equivalence.hom ≫
    (contractibleSingularChainAugmentationHomotopyEquiv (incidenceRealization incidence negative)).hom = _
  rw [canonical, contractibleSingularChainAugmentationHomotopyEquiv_hom]
  exact affineSingularChainMap_augmentationMap incidence negative

include equivalence canonical in
theorem contractibleIncidence_relativeHomology_positive_isZero (anchor : Chart) (degree : ℕ) :
    IsZero ((relativeComplex 𝕜 incidence negative).homology (degree + 1)) :=
  incidenceRelativeHomology_positive_isZero_of_augmentedHomotopyEquiv 𝕜 incidence negative
    (contractibleIncidenceChainAugmentationHomotopyEquiv incidence negative equivalence)
    (contractibleIncidenceChainAugmentationHomotopyEquiv_hom incidence negative equivalence canonical)
    anchor degree

end CanonicalSingularComparison

end

end BondalThomsen.ConvexNerveAugmentedCochainComparison
