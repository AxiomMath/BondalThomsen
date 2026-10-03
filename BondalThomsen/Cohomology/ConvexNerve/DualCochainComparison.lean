module

public import BondalThomsen.Cohomology.ConvexNerve.AcyclicCarrierAssembly

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceHomologyComparison
open BondalThomsen.ConvexNerveAcyclicCarrierAssembly
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ConvexNerveDualCochainComparison

noncomputable section

variable {Ray : Type*} {Chart : Type}

def incidenceCochainHomotopyEquiv (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {target : ChainComplex AddCommGrpCat.{0} ℕ}
    (equivalence : HomotopyEquiv (incidenceChains incidence negative) target) :
    HomotopyEquiv (negativeComplex 𝕜 incidence negative) (dualChainComplex 𝕜 target) :=
  (HomotopyEquiv.ofIso (incidenceDualIso 𝕜 incidence negative).symm).trans
    (dualChainHomotopyEquiv 𝕜 equivalence)

def incidenceCochainHomologyIso (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {target : ChainComplex AddCommGrpCat.{0} ℕ}
    (equivalence : HomotopyEquiv (incidenceChains incidence negative) target) (degree : ℕ) :
    (negativeComplex 𝕜 incidence negative).homology degree ≅
      (dualChainComplex 𝕜 target).homology degree :=
  (incidenceCochainHomotopyEquiv 𝕜 incidence negative equivalence).toHomologyIso degree

theorem incidenceCochain_positive_isZero_of_chainHomotopyEquiv
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {target : ChainComplex AddCommGrpCat.{0} ℕ}
    (equivalence : HomotopyEquiv (incidenceChains incidence negative) target) (degree : ℕ)
    (targetZero : IsZero ((dualChainComplex 𝕜 target).homology (degree + 1))) :
    IsZero ((negativeComplex 𝕜 incidence negative).homology (degree + 1)) :=
  targetZero.of_iso (incidenceCochainHomologyIso 𝕜 incidence negative equivalence (degree + 1))

theorem incidenceCochain_positive_isZero_of_chainHomotopyEquiv_single
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop) (coefficient : AddCommGrpCat.{0})
    (equivalence : HomotopyEquiv (incidenceChains incidence negative)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj coefficient)) (degree : ℕ) :
    IsZero ((negativeComplex 𝕜 incidence negative).homology (degree + 1)) := by
  apply incidenceCochain_positive_isZero_of_chainHomotopyEquiv 𝕜 incidence negative equivalence degree
  have originalZero : IsZero (((ChainComplex.single₀ AddCommGrpCat.{0}).obj coefficient).X (degree + 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have dualZero : IsZero
      ((dualChainComplex 𝕜 ((ChainComplex.single₀ AddCommGrpCat.{0}).obj coefficient)).X (degree + 1)) :=
    (scalarCoefficientDual 𝕜).map_isZero originalZero.op
  exact (HomologicalComplex.ExactAt.of_isZero dualZero).isZero_homology

theorem augmentedChain_cocycle_factors {chains : ChainComplex AddCommGrpCat.{0} ℕ}
    {coefficient : AddCommGrpCat.{0}} (augmentation : chains.X 0 ⟶ coefficient)
    (sectionMap : coefficient ⟶ chains.X 0) (contraction : chains.X 0 ⟶ chains.X 1)
    (identity : contraction ≫ chains.d 1 0 = 𝟙 _ - augmentation ≫ sectionMap)
    (cocycle : chains.X 0 ⟶ AddCommGrpCat.of 𝕜) (closed : chains.d 1 0 ≫ cocycle = 0) :
    cocycle = augmentation ≫ sectionMap ≫ cocycle := by
  have equality := congrArg (fun mapping => mapping ≫ cocycle) identity
  simp only [Category.assoc, closed, comp_zero, sub_comp, Category.id_comp] at equality
  exact (sub_eq_zero.mp equality.symm)

theorem negativeDegreeZeroCycles_constant_of_augmentedChainContraction
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (sectionMap : incidenceAugmentationObject ⟶ (incidenceChains incidence negative).X 0)
    (contraction : (incidenceChains incidence negative).X 0 ⟶
      (incidenceChains incidence negative).X 1)
    (identity : contraction ≫ (incidenceChains incidence negative).d 1 0 =
      𝟙 _ - incidenceChainAugmentation incidence negative ≫ sectionMap)
    (cochain : (negativeComplex 𝕜 incidence negative).X 0)
    (closed : (negativeComplex 𝕜 incidence negative).d 0 1 cochain = 0) :
    ∀ first second, cochain first = cochain second := by
  let comparison := incidenceDualIso 𝕜 incidence negative
  let cocycle := comparison.inv.f 0 cochain
  have dualClosed : (dualChainComplex 𝕜 (incidenceChains incidence negative)).d 0 1 cocycle = 0 := by
    have square := ConcreteCategory.congr_hom (comparison.inv.comm 0 1) cochain
    change (dualChainComplex 𝕜 (incidenceChains incidence negative)).d 0 1 cocycle =
      comparison.inv.f 1 ((negativeComplex 𝕜 incidence negative).d 0 1 cochain) at square
    simpa only [closed, map_zero] using square
  have chainClosed : (incidenceChains incidence negative).d 1 0 ≫ cocycle = 0 := dualClosed
  have factors := augmentedChain_cocycle_factors 𝕜 (incidenceChainAugmentation incidence negative)
    sectionMap contraction identity cocycle chainClosed
  have coordinate (tuple : forbiddenTuple incidence negative 0) :
      (incidenceChainInclusion incidence negative 0 tuple ≫ cocycle) (1 : ℤ) = cochain tuple := by
    have inverseIdentity := ConcreteCategory.congr_hom
      (congrArg (fun mapping => mapping.f 0) comparison.inv_hom_id) cochain
    exact congrFun inverseIdentity tuple
  intro first second
  rw [← coordinate first, ← coordinate second, factors]
  simp only [← Category.assoc, incidenceChainAugmentation_generator]

theorem negativeConstantAugmentation_epi_of_augmentedChainContraction
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (sectionMap : incidenceAugmentationObject ⟶ (incidenceChains incidence negative).X 0)
    (contraction : (incidenceChains incidence negative).X 0 ⟶
      (incidenceChains incidence negative).X 1)
    (identity : contraction ≫ (incidenceChains incidence negative).d 1 0 =
      𝟙 _ - incidenceChainAugmentation incidence negative ≫ sectionMap) (anchor : Chart) :
    Epi (negativeConstantAugmentation 𝕜 incidence negative anchor) :=
  BondalThomsen.ClosedCoverReducedZeroCohomology.negativeConstantAugmentation_epi_of_degreeZeroCycles_constant 𝕜
    incidence negative
    (negativeDegreeZeroCycles_constant_of_augmentedChainContraction 𝕜 incidence negative
      sectionMap contraction identity) anchor

theorem negativeAugmentedDegreeZero_isZero_of_augmentedChainContraction
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (sectionMap : incidenceAugmentationObject ⟶ (incidenceChains incidence negative).X 0)
    (contraction : (incidenceChains incidence negative).X 0 ⟶
      (incidenceChains incidence negative).X 1)
    (identity : contraction ≫ (incidenceChains incidence negative).d 1 0 =
      𝟙 _ - incidenceChainAugmentation incidence negative ≫ sectionMap) (anchor : Chart) :
    IsZero (negativeAugmentedDegreeZero 𝕜 incidence negative anchor) := by
  let := negativeConstantAugmentation_epi_of_augmentedChainContraction 𝕜
    incidence negative sectionMap contraction identity anchor
  exact isZero_cokernel_of_epi _

end

end BondalThomsen.ConvexNerveDualCochainComparison
