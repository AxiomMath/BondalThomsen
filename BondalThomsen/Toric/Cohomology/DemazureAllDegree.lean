module

public import BondalThomsen.Cohomology.ConvexNerve.IncidenceSingularGlobalEquivalence
public import BondalThomsen.Cohomology.ConvexNerve.AugmentedCochainComparison
public import BondalThomsen.Toric.Cohomology.NefFirstCohomologyVanishing
public import BondalThomsen.Toric.Cohomology.NegativeSupportContractibility
public import BondalThomsen.Cohomology.FiniteSimplicialCechNerveAllDegreeHomology
public import BondalThomsen.Toric.Cohomology.FanNegativeSupportCohomology
public import BondalThomsen.Toric.Cohomology.CohomologyWeightVanishing
public import BondalThomsen.Toric.Divisor.DivisorExtCohomology
public import BondalThomsen.Toric.Positivity.GeometricNefSupportProof

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveGlobalCarrierHomotopy
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceSingularGlobalEquivalence
open BondalThomsen.ConvexNerveAugmentedCochainComparison
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] Classical.decEq

namespace BondalThomsen.ToricDemazureAllDegree

variable {Chart : Type} [Finite Chart]
variable {First Second : Type*}

noncomputable def activeNerveFromData (predicate : Chart → Prop)
    (complex : PreAbstractSimplicialComplex Chart)
    (singletons : ∀ chart, predicate chart → {chart} ∈ complex) :
    AbstractSimplicialComplex {chart // predicate chart} where
  faces := {face | face.image Subtype.val ∈ complex}
  isRelLowerSet_faces := by
    intro face present
    have nonempty : face.Nonempty := by
      obtain ⟨chart, contains⟩ := (complex.isRelLowerSet_faces present).1
      obtain ⟨original, contains, _⟩ := Finset.mem_image.mp contains
      exact ⟨original, contains⟩
    refine ⟨nonempty, ?_⟩
    intro smaller contained smaller_nonempty
    exact complex.isRelLowerSet_faces.mem_of_le present
      (Finset.image_subset_image contained) (smaller_nonempty.image _)
  singleton_mem := by
    intro chart
    change Finset.image Subtype.val {chart} ∈ complex
    simpa only [Finset.image_singleton] using singletons chart.val chart.property

omit [Finite Chart] in
theorem activeNerve_eq_data (patches : Chart → Set First) :
    activeNerve patches = activeNerveFromData (fun chart => (patches chart).Nonempty)
      (coverNerve patches) (fun chart nonempty => by
        obtain ⟨point, member⟩ := nonempty
        exact (mem_coverNerve_iff patches {chart}).mpr
          ⟨Finset.singleton_nonempty _, point, by simpa using member⟩) := by
  rfl

omit [Finite Chart] in
theorem activeNerveFromData_contractible_congr
    {firstPredicate secondPredicate : Chart → Prop}
    {firstComplex secondComplex : PreAbstractSimplicialComplex Chart}
    (firstSingletons : ∀ chart, firstPredicate chart → {chart} ∈ firstComplex)
    (secondSingletons : ∀ chart, secondPredicate chart → {chart} ∈ secondComplex)
    (active : firstPredicate = secondPredicate) (same : firstComplex = secondComplex)
    (contractible : ContractibleSpace (AbstractSimplicialComplex.Realization
      (activeNerveFromData firstPredicate firstComplex firstSingletons))) :
    ContractibleSpace (AbstractSimplicialComplex.Realization
      (activeNerveFromData secondPredicate secondComplex secondSingletons)) := by
  cases active
  cases same
  exact contractible

omit [Finite Chart] in
theorem activeNerve_contractible_of_sameNerve (first : Chart → Set First)
    (second : Chart → Set Second) (same : coverNerve first = coverNerve second)
    (contractible : ContractibleSpace
      (AbstractSimplicialComplex.Realization (activeNerve first))) :
    ContractibleSpace (AbstractSimplicialComplex.Realization (activeNerve second)) := by
  rw [activeNerve_eq_data first] at contractible
  rw [activeNerve_eq_data second]
  have active : (fun chart => (first chart).Nonempty) =
      (fun chart => (second chart).Nonempty) := by
    funext chart
    apply propext
    have singleton := congrArg (fun complex => {chart} ∈ complex) same
    simpa only [mem_coverNerve_iff, Finset.singleton_nonempty, true_and,
      Finset.mem_singleton, forall_eq, Set.Nonempty] using Iff.of_eq singleton
  exact activeNerveFromData_contractible_congr _ _ active same contractible

end BondalThomsen.ToricDemazureAllDegree

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem cechCharacterIncidenceRealization_contractible_of_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (character : Lattice →+ ℤ)
    (negative : ∃ ray : fan.Ray, fan.cechCharacterNegativeRay divisor character ray) :
    ContractibleSpace (incidenceRealization (fan.cechRayChartIncidence 𝕜 complete regular)
      (fan.cechCharacterNegativeRay divisor character)) := by
  apply BondalThomsen.ToricDemazureAllDegree.activeNerve_contractible_of_sameNerve
    (fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character)
  · exact (fan.coverNerve_forbiddenChartPatch_eq 𝕜 complete regular divisor character).trans
      ((fan.divisorForbiddenChartNerve_eq_negativeChartComplex 𝕜 complete regular divisor character).trans
        (incidencePatches_coverNerve _ _).symm)
  · exact fan.negativeChartActiveNerve_contractible_of_support_negativeRay 𝕜
      complete regular divisor support character negative

theorem cechCharacterRelativeHomology_positive_isZero_of_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (character : Lattice →+ ℤ) (degree : ℕ) :
    IsZero ((fan.cechNegativeSupportComplex 𝕜 complete regular divisor character).homology (degree + 1)) := by
  by_cases negative : ∃ ray : fan.Ray, fan.cechCharacterNegativeRay divisor character ray
  · let := fan.cechCharacterIncidenceRealization_contractible_of_support 𝕜
      complete regular divisor support character negative
    exact contractibleIncidence_relativeHomology_positive_isZero 𝕜 _ _
      (canonicalIncidenceSingularChainHomotopyEquiv _ _)
      (canonicalIncidenceSingularChainHomotopyEquiv_hom _ _)
      (fan.cechNegativeSupportAnchor complete) degree
  · cases degree with
    | zero =>
      exact (fan.cechCharacterNegativeReducedZero_isZero_of_support 𝕜
        complete regular divisor support character).of_iso
          (negativeAugmentedDegreeZeroShiftIso 𝕜 _ _ (fan.cechNegativeSupportAnchor complete)).symm
    | succ degree =>
      exact (BondalThomsen.FiniteSimplicialCechNerveAllDegreeHomology.negativeComplex_homology_isZero_of_no_incidence 𝕜
        (fan.cechRayChartIncidence 𝕜 complete regular) (fan.cechCharacterNegativeRay divisor character)
        (fun ray _chart below _contains => negative ⟨ray, below⟩) (degree + 1)).of_iso
          (negativePositiveHomologyShiftIso 𝕜 _ _ (fan.cechNegativeSupportAnchor complete) degree).symm

theorem invariantDivisorCohomology_positive_subsingleton_of_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (degree : ℕ) (positive : 0 < degree) :
    Subsingleton (Cohomology (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj degree) := by
  obtain ⟨degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  apply (fan.invariantDivisorCohomology_subsingleton_iff_all_character_homology 𝕜
    complete regular divisor (degree + 1)).mpr
  intro character
  exact AddCommGrpCat.isZero_iff_subsingleton.mp
    ((fan.cechCharacterRelativeHomology_positive_isZero_of_support 𝕜
      complete regular divisor support character degree).of_iso
        (fan.cechCharacterScalarRelativeHomologyIso 𝕜 complete regular divisor character (degree + 1)))

variable {𝕜} in
noncomputable local instance demazureBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

theorem invertibleSheafCohomology_positive_subsingleton_of_isNef (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular))
    (nef : AlgebraicGeometry.IsNef (baseField := 𝕜) bundle.obj)
    (degree : ℕ) (positive : 0 < degree) :
    Subsingleton (Cohomology bundle.obj degree) := by
  obtain ⟨divisor, ⟨comparison⟩⟩ :=
    fan.invertibleSheaf_exists_invariantDivisorRepresentative 𝕜 complete regular bundle
  have invariantNef := (AlgebraicGeometry.isNef_iff_of_iso comparison).mp nef
  have support := (fan.invariantDivisor_isNef_iff_raySupport 𝕜 complete regular divisor).mp invariantNef
  let cohomologyComparison : Cohomology bundle.obj degree ≃+
      Cohomology (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj degree :=
    ((cohomologyFunctor (fan.algebraicRealization 𝕜 regular) degree).mapIso comparison).addCommGroupIsoToAddEquiv
  let := fan.invariantDivisorCohomology_positive_subsingleton_of_support 𝕜
    complete regular divisor support degree positive
  exact cohomologyComparison.injective.subsingleton

end TauCeti.Toric.Fan

namespace BondalThomsen

theorem demazureVanishing_proved : DemazureVanishing 𝕜 := by
  intro Lattice Ambient additive normed normedSpace finiteDimensional embedding
    fan complete regular bundle nef degree positive
  exact fan.invertibleSheafCohomology_positive_subsingleton_of_isNef 𝕜
    complete regular bundle nef degree positive

end BondalThomsen
