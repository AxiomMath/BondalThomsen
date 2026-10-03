module

public import BondalThomsen.Toric.Positivity.NefNegativeSupportGeometry
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open BondalThomsen.ToricCechNegativeSupportComparison
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ClosedConvexNerveComparison

variable {Index : Type} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]

def coverNerve (patches : Index → Set E) : PreAbstractSimplicialComplex Index :=
  negativeChartComplex (fun point index => point ∈ patches index) (fun _ => True)

abbrev NerveFace (patches : Index → Set E) :=
  {face : Finset Index // face ∈ coverNerve patches}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_coverNerve_iff (patches : Index → Set E) (face : Finset Index) :
    face ∈ coverNerve patches ↔ face.Nonempty ∧ ∃ point, ∀ index ∈ face, point ∈ patches index := by
  change (face.Nonempty ∧ ∃ point, True ∧ ∀ index ∈ face, point ∈ patches index) ↔ _
  simp only [true_and]

noncomputable def intersectionWitness (patches : Index → Set E) (face : NerveFace patches) : E :=
  ((mem_coverNerve_iff patches face.val).mp face.property).2.choose

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem intersectionWitness_mem (patches : Index → Set E) (face : NerveFace patches)
    (index : Index) (present : index ∈ face.val) :
    intersectionWitness patches face ∈ patches index :=
  ((mem_coverNerve_iff patches face.val).mp face.property).2.choose_spec index present

noncomputable def compactCore (patches : Index → Set E) : Set E :=
  convexHull ℝ (Set.range (intersectionWitness patches))

theorem compactCore_convex (patches : Index → Set E) : Convex ℝ (compactCore patches) :=
  convex_convexHull ℝ _

theorem compactCore_isCompact [Finite Index] (patches : Index → Set E) : IsCompact (compactCore patches) :=
  (Set.finite_range (intersectionWitness patches)).isCompact_convexHull ℝ

theorem intersectionWitness_mem_core (patches : Index → Set E) (face : NerveFace patches) :
    intersectionWitness patches face ∈ compactCore patches :=
  subset_convexHull ℝ _ ⟨face, rfl⟩

theorem compactCore_subset_region (patches : Index → Set E) (region : Set E)
    (region_convex : Convex ℝ region) (patches_subset : ∀ index, patches index ⊆ region) :
    compactCore patches ⊆ region := by
  apply region_convex.convexHull_subset_iff.mpr
  rintro point ⟨face, rfl⟩
  obtain ⟨index, present⟩ := ((mem_coverNerve_iff patches face.val).mp face.property).1
  exact patches_subset index (intersectionWitness_mem patches face index present)

theorem compactCore_nonempty (patches : Index → Set E) (region : Set E)
    (cover : (⋃ index, patches index) = region) (region_nonempty : region.Nonempty) :
    (compactCore patches).Nonempty := by
  obtain ⟨point, present⟩ := region_nonempty
  rw [← cover] at present
  obtain ⟨index, contains⟩ := Set.mem_iUnion.mp present
  have singleton_face : ({index} : Finset Index) ∈ coverNerve patches :=
    (mem_coverNerve_iff patches _).mpr ⟨Finset.singleton_nonempty index, point,
      fun selected member => by simpa only [Finset.mem_singleton.mp member] using contains⟩
  exact ⟨intersectionWitness patches ⟨{index}, singleton_face⟩,
    intersectionWitness_mem_core patches ⟨{index}, singleton_face⟩⟩

noncomputable def corePatch (patches : Index → Set E) (index : Index) : Set E :=
  compactCore patches ∩ patches index

theorem corePatch_isCompact [Finite Index] (patches : Index → Set E) (region : Set E)
    (region_convex : Convex ℝ region) (patches_subset : ∀ index, patches index ⊆ region)
    (patches_closed : ∀ index, IsClosed {point : region | point.val ∈ patches index})
    (index : Index) : IsCompact (corePatch patches index) := by
  obtain ⟨closed_set, closed, restriction⟩ := isClosed_induced_iff.mp (patches_closed index)
  have patch_eq : corePatch patches index = compactCore patches ∩ closed_set := by
    ext point
    constructor
    · rintro ⟨in_core, in_patch⟩
      have in_region := compactCore_subset_region patches region region_convex patches_subset in_core
      have same := Set.ext_iff.mp restriction (⟨point, in_region⟩ : region)
      change (point ∈ closed_set ↔ point ∈ patches index) at same
      exact ⟨in_core, same.mpr in_patch⟩
    · rintro ⟨in_core, in_closed⟩
      have in_region := compactCore_subset_region patches region region_convex patches_subset in_core
      have same := Set.ext_iff.mp restriction (⟨point, in_region⟩ : region)
      change (point ∈ closed_set ↔ point ∈ patches index) at same
      exact ⟨in_core, same.mp in_closed⟩
  rw [patch_eq]
  exact (compactCore_isCompact patches).inter_right closed

theorem corePatch_cover (patches : Index → Set E) (region : Set E)
    (region_convex : Convex ℝ region) (patches_subset : ∀ index, patches index ⊆ region)
    (cover : (⋃ index, patches index) = region) :
    (⋃ index, corePatch patches index) = compactCore patches := by
  ext point
  constructor
  · intro member
    obtain ⟨index, in_core, _⟩ := Set.mem_iUnion.mp member
    exact in_core
  · intro in_core
    have in_region := compactCore_subset_region patches region region_convex patches_subset in_core
    rw [← cover] at in_region
    obtain ⟨index, in_patch⟩ := Set.mem_iUnion.mp in_region
    exact Set.mem_iUnion.mpr ⟨index, in_core, in_patch⟩

noncomputable def cofaceWitnessCarrier (patches : Index → Set E) (face : NerveFace patches) : Set E :=
  convexHull ℝ {point | ∃ larger : NerveFace patches,
    face.val ⊆ larger.val ∧ intersectionWitness patches larger = point}

theorem cofaceWitnessCarrier_convex (patches : Index → Set E) (face : NerveFace patches) :
    Convex ℝ (cofaceWitnessCarrier patches face) :=
  convex_convexHull ℝ _

theorem cofaceWitnessCarrier_subset_patch (patches : Index → Set E)
    (patches_convex : ∀ index, Convex ℝ (patches index))
    (face : NerveFace patches) (index : Index) (present : index ∈ face.val) :
    cofaceWitnessCarrier patches face ⊆ patches index := by
  apply (patches_convex index).convexHull_subset_iff.mpr
  rintro point ⟨larger, contained, rfl⟩
  exact intersectionWitness_mem patches larger index (contained present)

theorem barycentricWitness_mem_carrier (patches : Index → Set E)
    (face : NerveFace patches) {Vertex : Type*} (vertices : Finset Vertex)
    (larger : Vertex → NerveFace patches) (weights : Vertex → ℝ)
    (contained : ∀ vertex ∈ vertices, face.val ⊆ (larger vertex).val)
    (nonnegative : ∀ vertex ∈ vertices, 0 ≤ weights vertex)
    (sum_one : ∑ vertex ∈ vertices, weights vertex = 1) :
    (∑ vertex ∈ vertices, weights vertex • intersectionWitness patches (larger vertex)) ∈
      cofaceWitnessCarrier patches face := by
  apply (cofaceWitnessCarrier_convex patches face).sum_mem nonnegative sum_one
  intro vertex present
  exact subset_convexHull ℝ _ ⟨larger vertex, contained vertex present, rfl⟩

end BondalThomsen.ClosedConvexNerveComparison

namespace TauCeti.Toric.Fan

open BondalThomsen.ClosedConvexNerveComparison

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem coverNerve_forbiddenChartPatch_eq (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) :
    coverNerve (fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character) =
      fan.divisorForbiddenChartNerve 𝕜 complete regular divisor character := by
  apply PreAbstractSimplicialComplex.ext
  ext charts
  change charts ∈ coverNerve (fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character) ↔
    charts ∈ fan.divisorForbiddenChartNerve 𝕜 complete regular divisor character
  rw [mem_coverNerve_iff, fan.mem_divisorForbiddenChartNerve_iff 𝕜]
  constructor
  · rintro ⟨nonempty, point, contains⟩
    obtain ⟨chart, present⟩ := nonempty
    exact ⟨⟨chart, present⟩, point,
      (fan.mem_divisorForbiddenChartIntersection_iff 𝕜 complete regular divisor character charts point).mpr
        ⟨(contains chart present).2, fun chart present => (contains chart present).1⟩⟩
  · rintro ⟨nonempty, point, contains⟩
    obtain ⟨forbidden, in_charts⟩ :=
      (fan.mem_divisorForbiddenChartIntersection_iff 𝕜 complete regular divisor character charts point).mp contains
    exact ⟨nonempty, point, fun chart present => ⟨in_charts chart present, forbidden⟩⟩

end TauCeti.Toric.Fan
