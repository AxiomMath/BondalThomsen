module

public import BondalThomsen.Cohomology.ClosedCoverReducedZeroCohomology
public import BondalThomsen.Toric.Positivity.NefNegativeSupportGeometry
public import BondalThomsen.Toric.Cohomology.FanNegativeSupportCohomology
public import BondalThomsen.Toric.Cohomology.CohomologyWeightVanishing
public import BondalThomsen.Toric.Divisor.DivisorExtCohomology
public import BondalThomsen.Toric.Positivity.AmpleGlobalGenerationCriterion

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Abelian
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open BondalThomsen.ClosedCoverReducedZeroCohomology
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def divisorForbiddenRelativeChartPatch (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ)
    (chart : Fin (Nat.card fan.cones)) :
    Set (fan.divisorWeightForbiddenRegion complete regular divisor character) :=
  {point | point.val ∈ fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character chart}

theorem divisorForbiddenRelativeChartPatch_cover (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) :
    (⋃ chart, fan.divisorForbiddenRelativeChartPatch 𝕜 complete regular divisor character chart) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro point
  have covered : point.val ∈ ⋃ chart, fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character chart := by
    rw [fan.divisorForbiddenChartPatch_cover 𝕜 complete regular divisor character]
    exact point.property
  obtain ⟨chart, member⟩ := Set.mem_iUnion.mp covered
  exact Set.mem_iUnion.mpr ⟨chart, member⟩

theorem cechCharacterNegativeTuple_iff_relativeChartPatch (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    tupleForbidden (fan.cechRayChartIncidence 𝕜 complete regular)
      (fan.cechCharacterNegativeRay divisor character) degree tuple ↔
      ∃ point, ∀ index, point ∈ fan.divisorForbiddenRelativeChartPatch 𝕜 complete regular divisor character
        (tuple index) := by
  let charts := Finset.univ.image tuple
  have nonempty : charts.Nonempty := ⟨tuple 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  constructor
  · rintro ⟨ray, negative, contains⟩
    have intersects := (fan.divisorForbiddenChartIntersection_nonempty_iff_negativeRay 𝕜
      complete regular divisor character charts nonempty).mpr ⟨ray, negative, by
        intro chart member
        obtain ⟨index, _present, rfl⟩ := Finset.mem_image.mp member
        exact contains index⟩
    obtain ⟨point, member⟩ := intersects
    obtain ⟨forbidden, onCharts⟩ :=
      (fan.mem_divisorForbiddenChartIntersection_iff 𝕜 complete regular divisor character charts point).mp member
    refine ⟨⟨point, forbidden⟩, ?_⟩
    intro index
    exact ⟨onCharts (tuple index) (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩), forbidden⟩
  · rintro ⟨point, contains⟩
    have intersects : (fan.divisorForbiddenChartIntersection 𝕜 complete regular divisor character charts).Nonempty := by
      refine ⟨point.val, ?_⟩
      rw [fan.mem_divisorForbiddenChartIntersection_iff 𝕜 complete regular divisor character charts]
      refine ⟨point.property, ?_⟩
      intro chart member
      obtain ⟨index, _present, rfl⟩ := Finset.mem_image.mp member
      exact (contains index).1
    obtain ⟨ray, negative, onCharts⟩ := (fan.divisorForbiddenChartIntersection_nonempty_iff_negativeRay 𝕜
      complete regular divisor character charts nonempty).mp intersects
    exact ⟨ray, negative, fun index => onCharts (tuple index)
      (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)⟩

theorem cechCharacterNegativeDegreeZeroCycle_constant_of_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (character : Lattice →+ ℤ)
    (cochain : (fan.cechCharacterNegativeChartComplex 𝕜 complete regular divisor character).X 0)
    (cycle : (fan.cechCharacterNegativeChartComplex 𝕜 complete regular divisor character).d 0 1 cochain = 0)
    (first second : forbiddenTuple (fan.cechRayChartIncidence 𝕜 complete regular)
      (fan.cechCharacterNegativeRay divisor character) 0) : cochain first = cochain second := by
  let patches := fan.divisorForbiddenRelativeChartPatch 𝕜 complete regular divisor character
  have connected : IsPreconnected (⋃ chart, patches chart) := by
    rw [divisorForbiddenRelativeChartPatch_cover]
    let := isPreconnected_iff_preconnectedSpace.mp
      (fan.divisorWeightForbiddenRegion_convex complete regular divisor support character).isPreconnected
    exact PreconnectedSpace.isPreconnected_univ
  exact negativeDegreeZeroCycle_values_eq_of_cover_incidence 𝕜 _ _ patches connected
    (fan.divisorForbiddenChartPatch_isClosed_in_region 𝕜 complete regular divisor character)
    (fan.cechCharacterNegativeTuple_iff_relativeChartPatch 𝕜 complete regular divisor character)
    cochain cycle first second

theorem cechCharacterNegativeConstantAugmentation_epi_of_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (character : Lattice →+ ℤ) :
    Epi (fan.cechCharacterNegativeConstantAugmentation 𝕜 complete regular divisor character) :=
  negativeConstantAugmentation_epi_of_degreeZeroCycles_constant 𝕜 _ _
    (fan.cechCharacterNegativeDegreeZeroCycle_constant_of_support 𝕜 complete regular divisor support character)
    (fan.cechNegativeSupportAnchor complete)

theorem cechCharacterNegativeReducedZero_isZero_of_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) (character : Lattice →+ ℤ) :
    IsZero (fan.cechCharacterNegativeReducedCohomology 𝕜 complete regular divisor character 0) := by
  let := fan.cechCharacterNegativeConstantAugmentation_epi_of_support 𝕜 complete regular divisor support character
  exact isZero_cokernel_of_epi _

end TauCeti.Toric.Fan
