module

public import BondalThomsen.Cohomology.ConvexNerve.RealizationEquivalence

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped Classical
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveBarycentricHomotopy
open BondalThomsen.ConvexNerveOpenNeighborhoods
open BondalThomsen.ConvexNerveRealizationEquivalence

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveGlobalCarrierHomotopy

section PartitionCoordinates

variable {Index : Type} [Finite Index] {Space : Type*} [TopologicalSpace Space]

noncomputable def partitionCoordinates (partition : PartitionOfUnity Index Space) :
    C(Space, Convexity.StdSimplex ℝ Index) where
  toFun point := {
    weights := Finsupp.equivFunOnFinite.symm (fun index => partition index point)
    nonneg := fun index => partition.nonneg index point
    total := by
      let : Fintype Index := Fintype.ofFinite _
      rw [Finsupp.equivFunOnFinite_symm_sum]
      simpa only [finsum_eq_sum_of_fintype] using partition.sum_eq_one (Set.mem_univ point)
  }
  continuous_toFun := (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Index).continuous_iff.mpr
    (continuous_pi fun index => (partition index).continuous)

theorem partitionCoordinates_support (partition : PartitionOfUnity Index Space) (point : Space) :
    (partitionCoordinates partition point).weights.support = partition.finsupport point := by
  ext index
  simp only [Finsupp.mem_support_iff, PartitionOfUnity.mem_finsupport, Function.mem_support]
  rfl

theorem partitionCoordinates_nonempty (partition : PartitionOfUnity Index Space) (point : Space) :
    (partition.finsupport point).Nonempty := by
  rw [← partitionCoordinates_support]
  exact Convexity.StdSimplex.support_weights_nonempty _

end PartitionCoordinates

section SubdivisionCoordinates

variable {Index : Type} {E : Type*} [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem activeFaceBarycenter_coordinate (patches : Index → Set E) (face : NerveFace patches)
    (index : ActiveIndex patches) :
    (activeFaceBarycenter patches face).weights index =
      if index ∈ activeFaceVertices patches face then (face.val.card : ℝ)⁻¹ else 0 := by
  unfold activeFaceBarycenter
  rw [Convexity.StdSimplex.weights_subBarycenter]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have same_card : (activeFaceVertices patches face).card = face.val.card := by
    rw [← activeFaceVertices_image patches face, Finset.card_image_of_injective _ Subtype.val_injective]
  simp [same_card]

omit [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem activeFaceVertices_mem_iff (patches : Index → Set E) (face : NerveFace patches)
    (index : ActiveIndex patches) : index ∈ activeFaceVertices patches face ↔ index.val ∈ face.val := by
  constructor
  · intro present
    rw [← activeFaceVertices_image patches face]
    exact Finset.mem_image.mpr ⟨index, present, rfl⟩
  · intro present
    rw [← activeFaceVertices_image patches face] at present
    obtain ⟨original, contains, same⟩ := Finset.mem_image.mp present
    have equal : original = index := Subtype.ext same
    exact equal ▸ contains

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem subdivisionBarycenter_coordinate_sum (patches : Index → Set E)
    (point : AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches))
    (index : ActiveIndex patches) :
    (subdivisionBarycenterMap patches point).val index =
      ∑ face ∈ point.val.support, point.val face * (activeFaceBarycenter patches face).weights index := by
  change (point.val.sum (fun face weight => weight • (activeFaceBarycenter patches face).weights)) index = _
  rw [Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.smul_apply, smul_eq_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem subdivisionBarycenter_positive_of_face (patches : Index → Set E)
    (point : AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches))
    (face : NerveFace patches) (present : face ∈ point.val.support)
    (index : ActiveIndex patches) (contains : index.val ∈ face.val) :
    0 < (subdivisionBarycenterMap patches point).val index := by
  rw [subdivisionBarycenter_coordinate_sum]
  apply Finset.sum_pos'
  · intro vertex _
    exact mul_nonneg (AbstractSimplicialComplex.Realization.nonneg _ point vertex)
      ((activeFaceBarycenter patches vertex).nonneg index)
  · refine ⟨face, present, mul_pos ?_ ?_⟩
    · exact lt_of_le_of_ne (AbstractSimplicialComplex.Realization.nonneg _ point face)
        (Finsupp.mem_support_iff.mp present).symm
    · rw [activeFaceBarycenter_coordinate, ite_eq_left ((activeFaceVertices_mem_iff patches face index).mpr contains)]
      exact inv_pos.mpr (Nat.cast_pos.mpr ((mem_coverNerve_iff patches face.val).mp face.property).1.card_pos)

def simultaneousPatch (patches : Index → Set E) (radius : ℝ) (index : ActiveIndex patches) :
    Set (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
  {point | 0 < (subdivisionBarycenterMap patches point).val index ∧
    (barycentricWitnessMap patches point).val ∈ Metric.thickening radius (corePatch patches index.val)}

theorem simultaneousPatch_isOpen (patches : Index → Set E) (radius : ℝ) (index : ActiveIndex patches) :
    IsOpen (simultaneousPatch patches radius index) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const
      ((continuous_into_realization_iff (activeNerve patches) _).mp
        (subdivisionBarycenterMap patches).continuous index)
  · exact Metric.isOpen_thickening.preimage
      (continuous_subtype_val.comp (barycentricWitnessMap patches).continuous)

theorem simultaneousPatch_cover (patches : Index → Set E)
    (patches_convex : ∀ index, Convex ℝ (patches index)) (radius : ℝ) (positive : 0 < radius) :
    (⋃ index, simultaneousPatch patches radius index) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro point
  obtain ⟨least, present, minimal⟩ := barycentricFace_has_minimum patches point.val.support
    (AbstractSimplicialComplex.support_mem _ point)
  obtain ⟨index, contains⟩ := ((mem_coverNerve_iff patches least.val).mp least.property).1
  let active : ActiveIndex patches := ⟨index, intersectionWitness patches least,
    intersectionWitness_mem patches least index contains⟩
  refine Set.mem_iUnion.mpr ⟨active, subdivisionBarycenter_positive_of_face patches point least present active contains,
    Metric.self_subset_thickening positive _ ⟨(barycentricWitnessMap patches point).property, ?_⟩⟩
  have in_carrier := witnessEvaluation_face_mem_carrier patches
    ⟨point.val.support, AbstractSimplicialComplex.support_mem _ point⟩ least minimal
    ⟨point.val, AbstractSimplicialComplex.mem_convexHull_carrier _ point⟩
  exact cofaceWitnessCarrier_subset_patch patches patches_convex least index contains in_carrier

end SubdivisionCoordinates

section GlobalComparison

variable {Index : Type} {E : Type*} [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Finite Index] in
theorem thickenedFace_mem_activeNerve (patches : Index → Set E) (radius : ℝ)
    (preserves : ∀ face : Finset Index,
      (∃ point ∈ compactCore patches, ∀ index ∈ face,
        point ∈ Metric.thickening radius (corePatch patches index)) ↔
      ∃ point ∈ compactCore patches, ∀ index ∈ face, point ∈ corePatch patches index)
    (point : compactCore patches) (face : Finset (ActiveIndex patches))
    (nonempty : face.Nonempty)
    (contains : ∀ index ∈ face, point.val ∈ Metric.thickening radius (corePatch patches index.val)) :
    face ∈ activeNerve patches := by
  change face.image Subtype.val ∈ coverNerve patches
  apply (mem_coverNerve_iff patches _).mpr
  refine ⟨nonempty.image _, ?_⟩
  obtain ⟨witness, _, present⟩ := (preserves (face.image Subtype.val)).mp
    ⟨point.val, point.property, by
      intro index member
      obtain ⟨active, active_member, rfl⟩ := Finset.mem_image.mp member
      exact contains active active_member⟩
  exact ⟨witness, fun index member => (present index member).2⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
noncomputable def activePartitionNerveMap (patches : Index → Set E)
    {Space : Type*} [TopologicalSpace Space]
    (partition : PartitionOfUnity (ActiveIndex patches) Space)
    (supported : ∀ point, partition.finsupport point ∈ activeNerve patches) :
    C(Space, AbstractSimplicialComplex.Realization (activeNerve patches)) where
  toFun point := simplexToRealization (activeNerve patches) (partitionCoordinates partition point) (by
    rw [partitionCoordinates_support]
    exact supported point)
  continuous_toFun := (continuous_into_realization_iff (activeNerve patches) _).mpr
    fun index => (partition index).continuous

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem activePartitionNerveMap_support (patches : Index → Set E)
    {Space : Type*} [TopologicalSpace Space]
    (partition : PartitionOfUnity (ActiveIndex patches) Space)
    (supported : ∀ point, partition.finsupport point ∈ activeNerve patches) (point : Space) :
    (activePartitionNerveMap patches partition supported point).val.support = partition.finsupport point :=
  partitionCoordinates_support partition point

theorem exists_global_subdivision_comparison (patches : Index → Set E) (region : Set E)
    (region_convex : Convex ℝ region) (patches_subset : ∀ index, patches index ⊆ region)
    (patches_convex : ∀ index, Convex ℝ (patches index))
    (patches_closed : ∀ index, IsClosed {point : region | point.val ∈ patches index})
    (cover : (⋃ index, patches index) = region) :
    ∃ mapping : C(compactCore patches, AbstractSimplicialComplex.Realization (activeNerve patches)),
      Nonempty ((subdivisionBarycenterMap patches).Homotopy
        (mapping.comp (barycentricWitnessMap patches))) := by
  let : DecidableEq (ActiveIndex patches) := Classical.decEq _
  let : CompactSpace (compactCore patches) :=
    isCompact_iff_compactSpace.mp (compactCore_isCompact patches)
  let : CompactSpace (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    finiteRealization_compactSpace _
  let : T2Space (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    (realizationCoordinates_isClosedEmbedding _).isEmbedding.t2Space
  obtain ⟨radius, positive, preserves⟩ := exists_uniform_nerve_preserving_radius
    (compactCore patches) (corePatch patches) (compactCore_isCompact patches)
    (fun index => (corePatch_isCompact patches region region_convex patches_subset patches_closed index).isClosed)
  have core_cover : compactCore patches ⊆ ⋃ index, corePatch patches index := by
    rw [corePatch_cover patches region region_convex patches_subset cover]
  obtain ⟨core_partition, core_subordinate⟩ := PartitionOfUnity.exists_isSubordinate
    (s := (Set.univ : Set (compactCore patches))) isClosed_univ
    (relativeOpenPatch (compactCore patches) (corePatch patches) radius)
    (relativeOpenPatch_isOpen _ _ _)
    (by rw [relativeOpenPatch_cover _ _ core_cover radius positive])
  have core_supported : ∀ point : compactCore patches,
      (partitionCoordinates core_partition point).weights.support ∈ coverNerve patches := by
    intro point
    rw [partitionCoordinates_support]
    apply (mem_coverNerve_iff patches _).mpr
    refine ⟨partitionCoordinates_nonempty core_partition point, ?_⟩
    obtain ⟨witness, _, present⟩ := (preserves (core_partition.finsupport point)).mp
      ⟨point.val, point.property, by
        intro index member
        apply core_subordinate index
        apply subset_tsupport
        exact (core_partition.mem_finsupport point).mp member⟩
    exact ⟨witness, fun index member => (present index member).2⟩
  let mapping : C(compactCore patches, AbstractSimplicialComplex.Realization (activeNerve patches)) := {
    toFun point := coordinatesToNerve patches (partitionCoordinates core_partition point) (core_supported point)
    continuous_toFun := (continuous_into_realization_iff (activeNerve patches) _).mpr
      fun index => (core_partition index.val).continuous
  }
  obtain ⟨source_partition, source_subordinate⟩ := PartitionOfUnity.exists_isSubordinate
    (s := (Set.univ : Set (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches))))
    isClosed_univ (simultaneousPatch patches radius) (simultaneousPatch_isOpen patches radius)
    (by rw [simultaneousPatch_cover patches patches_convex radius positive])
  have simultaneous : ∀ point, ∀ index ∈ source_partition.finsupport point,
      point ∈ simultaneousPatch patches radius index := by
    intro point index member
    apply source_subordinate index
    apply subset_tsupport
    exact (source_partition.mem_finsupport point).mp member
  have source_supported : ∀ point, source_partition.finsupport point ∈ activeNerve patches := by
    intro point
    exact thickenedFace_mem_activeNerve patches radius preserves (barycentricWitnessMap patches point)
      (source_partition.finsupport point) (partitionCoordinates_nonempty source_partition point)
      (fun index member => (simultaneous point index member).2)
  let intermediate := activePartitionNerveMap patches source_partition source_supported
  have source_contiguous : ∀ point,
      (subdivisionBarycenterMap patches point).val.support ∪ (intermediate point).val.support ∈
        activeNerve patches := by
    intro point
    have contained : (intermediate point).val.support ⊆
        (subdivisionBarycenterMap patches point).val.support := by
      rw [activePartitionNerveMap_support]
      intro index member
      exact Finsupp.mem_support_iff.mpr (ne_of_gt (simultaneous point index member).1)
    rw [Finset.union_eq_left.mpr contained]
    exact AbstractSimplicialComplex.support_mem _ _
  have composite_contiguous : ∀ point,
      (intermediate point).val.support ∪ (mapping (barycentricWitnessMap patches point)).val.support ∈
        activeNerve patches := by
    intro point
    apply thickenedFace_mem_activeNerve patches radius preserves (barycentricWitnessMap patches point)
    · apply Finset.Nonempty.mono Finset.subset_union_left
      rw [activePartitionNerveMap_support]
      exact partitionCoordinates_nonempty source_partition point
    · intro index member
      rcases Finset.mem_union.mp member with source_member | core_member
      · rw [activePartitionNerveMap_support] at source_member
        exact (simultaneous point index source_member).2
      · apply core_subordinate index.val
        apply subset_tsupport
        apply (core_partition.mem_finsupport _).mp
        have nonzero := Finsupp.mem_support_iff.mp core_member
        change (coordinatesActiveSimplex patches
          (partitionCoordinates core_partition (barycentricWitnessMap patches point))
          (core_supported _)).weights index ≠ 0 at nonzero
        exact (core_partition.mem_finsupport _).mpr nonzero
  exact ⟨mapping, ⟨(realizationAffineHomotopy _ (subdivisionBarycenterMap patches)
    intermediate source_contiguous).trans
    (realizationAffineHomotopy _ intermediate (mapping.comp (barycentricWitnessMap patches))
      composite_contiguous)⟩⟩

end GlobalComparison

section SubdivisionPeeling

variable {Index : Type} {E : Type*} [Finite Index]

noncomputable def barycenterEvaluationLinearMap (patches : Index → Set E) :
    (NerveFace patches →₀ ℝ) →ₗ[ℝ] (ActiveIndex patches →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun face => (activeFaceBarycenter patches face).weights)

omit [Finite Index] in
theorem barycenterEvaluationLinearMap_apply (patches : Index → Set E)
    (weights : NerveFace patches →₀ ℝ) :
    barycenterEvaluationLinearMap patches weights =
      weights.sum (fun face weight => weight • (activeFaceBarycenter patches face).weights) :=
  Finsupp.linearCombination_apply ℝ _

omit [Finite Index] in
theorem activeFaceVertices_card (patches : Index → Set E) (face : NerveFace patches) :
    (activeFaceVertices patches face).card = face.val.card := by
  rw [← activeFaceVertices_image patches face,
    Finset.card_image_of_injective _ Subtype.val_injective]

noncomputable def supportedNerveFace (patches : Index → Set E)
    (vertices : Finset (ActiveIndex patches)) (present : vertices ∈ activeNerve patches) :
    NerveFace patches := ⟨vertices.image Subtype.val, present⟩

omit [Finite Index] in
theorem supportedNerveFace_vertices (patches : Index → Set E)
    (vertices : Finset (ActiveIndex patches)) (present : vertices ∈ activeNerve patches) :
    activeFaceVertices patches (supportedNerveFace patches vertices present) = vertices := by
  ext index
  rw [activeFaceVertices_mem_iff]
  exact Finset.mem_image.trans ⟨by
    rintro ⟨original, member, same⟩
    exact Subtype.val_injective same ▸ member,
    fun member => ⟨index, member, rfl⟩⟩

omit [Finite Index] in
theorem exists_minimum_coordinate_peeling (patches : Index → Set E)
    (weights : ActiveIndex patches →₀ ℝ) (nonneg : ∀ index, 0 ≤ weights index)
    (present : weights.support ∈ activeNerve patches) :
    ∃ face : NerveFace patches, ∃ coefficient : ℝ, ∃ remainder : ActiveIndex patches →₀ ℝ,
      0 < coefficient ∧ (∀ index, 0 ≤ remainder index) ∧
      remainder.support ⊆ weights.support ∧ remainder.support.card < weights.support.card ∧
      activeFaceVertices patches face = weights.support ∧
      weights = coefficient • (activeFaceBarycenter patches face).weights + remainder := by
  let : DecidableEq (ActiveIndex patches) := Classical.decEq _
  have support_nonempty : weights.support.Nonempty :=
    (activeNerve patches).isRelLowerSet_faces.prop_of_mem present
  obtain ⟨least, contains, minimal⟩ := weights.support.exists_min_image weights support_nonempty
  have minimum_positive : 0 < weights least :=
    lt_of_le_of_ne (nonneg least) (Finsupp.mem_support_iff.mp contains).symm
  let face := supportedNerveFace patches weights.support present
  have same_vertices : activeFaceVertices patches face = weights.support :=
    supportedNerveFace_vertices patches weights.support present
  have same_card : face.val.card = weights.support.card := by
    rw [← activeFaceVertices_card, same_vertices]
  have card_positive : 0 < (face.val.card : ℝ) := by
    rw [same_card]
    exact Nat.cast_pos.mpr support_nonempty.card_pos
  let coefficient := weights least * (face.val.card : ℝ)
  let remainder := weights - coefficient • (activeFaceBarycenter patches face).weights
  have remainder_coordinate : ∀ index, remainder index =
      if index ∈ weights.support then weights index - weights least else 0 := by
    intro index
    dsimp [remainder, coefficient]
    rw [activeFaceBarycenter_coordinate, same_vertices]
    split_ifs with member
    · field_simp
    · simp [Finsupp.notMem_support_iff.mp member]
  have support_contained : remainder.support ⊆ weights.support := by
    intro index member
    by_contra absent
    have zero : remainder index = 0 := by rw [remainder_coordinate, ite_eq_right absent]
    exact Finsupp.mem_support_iff.mp member zero
  have minimum_absent : least ∉ remainder.support := by
    rw [Finsupp.mem_support_iff, remainder_coordinate, ite_eq_left contains, sub_self]
    exact not_not.mpr rfl
  refine ⟨face, coefficient, remainder, mul_pos minimum_positive card_positive, ?_,
    support_contained, ?_, same_vertices, ?_⟩
  · intro index
    rw [remainder_coordinate]
    split_ifs with member
    · exact sub_nonneg.mpr (minimal index member)
    · exact le_rfl
  · exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨support_contained, fun same => minimum_absent (same ▸ contains)⟩)
  · dsimp [remainder]
    abel

omit [Finite Index] in
theorem exists_chain_barycenter_decomposition (patches : Index → Set E)
    (weights : ActiveIndex patches →₀ ℝ) (nonneg : ∀ index, 0 ≤ weights index)
    (supported : weights.support = ∅ ∨ weights.support ∈ activeNerve patches) :
    ∃ coefficients : NerveFace patches →₀ ℝ,
      (∀ face, 0 ≤ coefficients face) ∧
      IsChain (· ≤ ·) (coefficients.support : Set (NerveFace patches)) ∧
      (∀ face ∈ coefficients.support, activeFaceVertices patches face ⊆ weights.support) ∧
      barycenterEvaluationLinearMap patches coefficients = weights := by
  let : DecidableEq (ActiveIndex patches) := Classical.decEq _
  generalize cardinality : weights.support.card = count
  induction count using Nat.strong_induction_on generalizing weights with
  | h count induction =>
    by_cases empty : weights.support = ∅
    · have zero : weights = 0 := Finsupp.support_eq_empty.mp empty
      exact ⟨0, fun _ => le_rfl, by simp, by simp, by simp [zero]⟩
    · have present : weights.support ∈ activeNerve patches := supported.resolve_left empty
      obtain ⟨face, coefficient, remainder, positive, remainder_nonneg, contained,
        smaller, face_vertices, decomposition⟩ :=
        exists_minimum_coordinate_peeling patches weights nonneg present
      have remainder_supported : remainder.support = ∅ ∨ remainder.support ∈ activeNerve patches := by
        by_cases remainder_empty : remainder.support = ∅
        · exact Or.inl remainder_empty
        · exact Or.inr ((activeNerve patches).isRelLowerSet_faces.mem_of_le present contained
            (Finset.nonempty_iff_ne_empty.mpr remainder_empty))
      obtain ⟨coefficients, coefficients_nonneg, chain, coefficients_contained, evaluates⟩ :=
        induction remainder.support.card (by omega) remainder remainder_nonneg remainder_supported rfl
      let combined := Finsupp.single face coefficient + coefficients
      have combined_support : combined.support ⊆ insert face coefficients.support := by
        exact Finsupp.support_add.trans (Finset.union_subset
          (Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))
          (Finset.subset_insert _ _))
      refine ⟨combined, ?_, ?_, ?_, ?_⟩
      · intro vertex
        exact add_nonneg (by
          simp only [Finsupp.single_apply]
          split_ifs <;> first | exact positive.le | exact le_rfl) (coefficients_nonneg vertex)
      · refine IsChain.mono (Finset.coe_subset.mpr combined_support) ?_
        rw [Finset.coe_insert]
        apply chain.insert
        intro vertex member _
        right
        change vertex.val ⊆ face.val
        rw [← activeFaceVertices_image patches vertex, ← activeFaceVertices_image patches face]
        exact Finset.image_subset_image ((coefficients_contained vertex member).trans
          (face_vertices ▸ contained))
      · intro vertex member
        rcases Finset.mem_insert.mp (combined_support member) with same | member
        · simp [same, face_vertices]
        · exact (coefficients_contained vertex member).trans contained
      · change barycenterEvaluationLinearMap patches
          (Finsupp.single face coefficient + coefficients) = weights
        rw [map_add, evaluates]
        simpa only [barycenterEvaluationLinearMap, Finsupp.linearCombination_single] using decomposition.symm

end SubdivisionPeeling

section SubdivisionSurjectivity

variable {Index : Type} {E : Type*} [Finite Index]

omit [Finite Index] in
theorem barycenterEvaluationLinearMap_total (patches : Index → Set E)
    (coefficients : NerveFace patches →₀ ℝ) :
    (barycenterEvaluationLinearMap patches coefficients).sum (fun _ value => value) =
      coefficients.sum (fun _ value => value) := by
  rw [barycenterEvaluationLinearMap_apply]
  rw [Finsupp.sum_sum_index (by simp) (by simp)]
  apply Finsupp.sum_congr
  intro face _
  rw [Finsupp.sum_smul_index' (by simp)]
  simp only [smul_eq_mul, ← Finsupp.mul_sum, (activeFaceBarycenter patches face).total, mul_one]

theorem subdivisionBarycenterMap_surjective (patches : Index → Set E) :
    Function.Surjective (subdivisionBarycenterMap patches) := by
  let : DecidableEq (NerveFace patches) := Classical.decEq _
  intro point
  obtain ⟨coefficients, nonneg, chain, _, evaluates⟩ := exists_chain_barycenter_decomposition
    patches point.val (AbstractSimplicialComplex.Realization.nonneg _ point)
    (Or.inr (AbstractSimplicialComplex.support_mem _ point))
  have total : coefficients.sum (fun _ value => value) = 1 := by
    rw [← barycenterEvaluationLinearMap_total patches coefficients, evaluates]
    exact (realizationToSimplex (activeNerve patches) point).total
  have nonempty : coefficients.support.Nonempty := by
    by_contra absent
    have empty := Finset.not_nonempty_iff_eq_empty.mp absent
    simp only [Finsupp.sum, empty, Finset.sum_empty] at total
    exact zero_ne_one total
  let preimage : AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches) :=
    ⟨coefficients, AbstractSimplicialComplex.mem_realization_iff.mpr
      ⟨coefficients.support, ⟨nonempty, chain⟩, by
        rw [Finset.coe_image]
        exact AbstractSimplicialComplex.mem_standardSimplex_iff.mpr
          ⟨nonneg, total, Finset.Subset.refl _⟩⟩⟩
  refine ⟨preimage, Subtype.ext ?_⟩
  exact evaluates

end SubdivisionSurjectivity

section SubdivisionUniqueness

variable {Index : Type} {E : Type*} [Finite Index]

omit [Finite Index] in
theorem barycenterEvaluationLinearMap_coordinate (patches : Index → Set E)
    (coefficients : NerveFace patches →₀ ℝ) (index : ActiveIndex patches) :
    (barycenterEvaluationLinearMap patches coefficients) index =
      ∑ face ∈ coefficients.support,
        coefficients face * (activeFaceBarycenter patches face).weights index := by
  rw [barycenterEvaluationLinearMap_apply, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.smul_apply, smul_eq_mul]

omit [Finite Index] in
theorem chainEvaluation_support_and_minimum (patches : Index → Set E)
    (coefficients : NerveFace patches →₀ ℝ) (nonneg : ∀ face, 0 ≤ coefficients face)
    (chain : IsChain (· ≤ ·) (coefficients.support : Set (NerveFace patches)))
    (greatest : NerveFace patches) (present : greatest ∈ coefficients.support)
    (maximal : ∀ face ∈ coefficients.support, face.val ⊆ greatest.val) :
    (barycenterEvaluationLinearMap patches coefficients).support = activeFaceVertices patches greatest ∧
      ∃ index ∈ activeFaceVertices patches greatest,
        (barycenterEvaluationLinearMap patches coefficients) index =
          coefficients greatest * (greatest.val.card : ℝ)⁻¹ ∧
        ∀ other ∈ activeFaceVertices patches greatest,
          coefficients greatest * (greatest.val.card : ℝ)⁻¹ ≤
            (barycenterEvaluationLinearMap patches coefficients) other := by
  let : DecidableEq (NerveFace patches) := Classical.decEq _
  let : DecidableEq (ActiveIndex patches) := Classical.decEq _
  have coefficient_positive : 0 < coefficients greatest :=
    lt_of_le_of_ne (nonneg greatest) (Finsupp.mem_support_iff.mp present).symm
  have inverse_positive : 0 < (greatest.val.card : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr ((mem_coverNerve_iff patches _).mp greatest.property).1.card_pos)
  have lower_bound : ∀ index ∈ activeFaceVertices patches greatest,
      coefficients greatest * (greatest.val.card : ℝ)⁻¹ ≤
        (barycenterEvaluationLinearMap patches coefficients) index := by
    intro index member
    rw [barycenterEvaluationLinearMap_coordinate]
    have bound := Finset.single_le_sum (fun face _ =>
      mul_nonneg (nonneg face) ((activeFaceBarycenter patches face).nonneg index)) present
    simpa only [activeFaceBarycenter_coordinate, ite_eq_left member] using bound
  have support_equal : (barycenterEvaluationLinearMap patches coefficients).support =
      activeFaceVertices patches greatest := by
    ext index
    constructor
    · intro supported
      by_contra absent
      have zero : (barycenterEvaluationLinearMap patches coefficients) index = 0 := by
        rw [barycenterEvaluationLinearMap_coordinate]
        apply Finset.sum_eq_zero
        intro face member
        have missing : index ∉ activeFaceVertices patches face := fun contains =>
          absent (activeFaceVertices_mono patches face greatest (maximal face member) contains)
        rw [activeFaceBarycenter_coordinate, ite_eq_right missing, mul_zero]
      exact Finsupp.mem_support_iff.mp supported zero
    · intro member
      exact Finsupp.mem_support_iff.mpr (ne_of_gt
        (lt_of_lt_of_le (mul_pos coefficient_positive inverse_positive) (lower_bound index member)))
  have isolated : ∃ index ∈ activeFaceVertices patches greatest,
      ∀ face ∈ coefficients.support, face ≠ greatest → index ∉ activeFaceVertices patches face := by
    by_cases empty : (coefficients.support.erase greatest) = ∅
    · obtain ⟨index, member⟩ := activeFaceVertices_nonempty patches greatest
      refine ⟨index, member, ?_⟩
      intro face contains distinct
      have impossible := Finset.mem_erase.mpr ⟨distinct, contains⟩
      rw [empty] at impossible
      exact (Finset.notMem_empty _ impossible).elim
    · have smaller_nonempty := Finset.nonempty_iff_ne_empty.mpr empty
      have smaller_chain := chain.mono
        (Finset.coe_subset.mpr (Finset.erase_subset greatest coefficients.support))
      obtain ⟨next, next_present, next_maximal⟩ := barycentricFace_has_maximum patches
        (coefficients.support.erase greatest) ⟨smaller_nonempty, smaller_chain⟩
      have next_subset : next.val ⊆ greatest.val := maximal next (Finset.mem_of_mem_erase next_present)
      have next_distinct : next.val ≠ greatest.val := fun equal =>
        (Finset.ne_of_mem_erase next_present) (Subtype.ext equal)
      have strict : next.val ⊂ greatest.val := Finset.ssubset_iff_subset_ne.mpr ⟨next_subset, next_distinct⟩
      obtain ⟨original, in_greatest, not_next⟩ := Finset.exists_of_ssubset strict
      let index : ActiveIndex patches := ⟨original, intersectionWitness patches greatest,
        intersectionWitness_mem patches greatest original in_greatest⟩
      refine ⟨index, (activeFaceVertices_mem_iff _ _ _).mpr in_greatest, ?_⟩
      intro face member distinct contains
      apply not_next
      exact next_maximal face (Finset.mem_erase.mpr ⟨distinct, member⟩)
        ((activeFaceVertices_mem_iff _ _ _).mp contains)
  obtain ⟨index, member, isolated⟩ := isolated
  refine ⟨support_equal, index, member, ?_, lower_bound⟩
  rw [barycenterEvaluationLinearMap_coordinate]
  rw [Finset.sum_eq_single greatest]
  · rw [activeFaceBarycenter_coordinate, ite_eq_left member]
  · intro face supported distinct
    rw [activeFaceBarycenter_coordinate, ite_eq_right (isolated face supported distinct), mul_zero]
  · exact fun absent => (absent present).elim

end SubdivisionUniqueness

section SubdivisionInjectivity

variable {Index : Type} {E : Type*} [Finite Index]

omit [Finite Index] in
theorem chainEvaluation_injective (patches : Index → Set E)
    (first second : NerveFace patches →₀ ℝ)
    (first_nonneg : ∀ face, 0 ≤ first face) (second_nonneg : ∀ face, 0 ≤ second face)
    (first_chain : IsChain (· ≤ ·) (first.support : Set (NerveFace patches)))
    (second_chain : IsChain (· ≤ ·) (second.support : Set (NerveFace patches)))
    (equal : barycenterEvaluationLinearMap patches first = barycenterEvaluationLinearMap patches second) :
    first = second := by
  let : DecidableEq (NerveFace patches) := Classical.decEq _
  let : DecidableEq (ActiveIndex patches) := Classical.decEq _
  generalize cardinality : first.support.card = count
  induction count using Nat.strong_induction_on generalizing first second with
  | h count induction =>
    by_cases first_empty : first.support = ∅
    · have first_zero : first = 0 := Finsupp.support_eq_empty.mp first_empty
      by_cases second_empty : second.support = ∅
      · exact first_zero.trans (Finsupp.support_eq_empty.mp second_empty).symm
      · obtain ⟨greatest, present, maximal⟩ := barycentricFace_has_maximum patches second.support
          ⟨Finset.nonempty_iff_ne_empty.mpr second_empty, second_chain⟩
        have support := (chainEvaluation_support_and_minimum patches second second_nonneg
          second_chain greatest present maximal).1
        have zero : barycenterEvaluationLinearMap patches second = 0 := by
          simpa only [first_zero, map_zero] using equal.symm
        rw [zero, Finsupp.support_zero] at support
        have nonempty := activeFaceVertices_nonempty patches greatest
        rw [← support] at nonempty
        exact (Finset.not_nonempty_empty nonempty).elim
    · obtain ⟨greatest, present, maximal⟩ := barycentricFace_has_maximum patches first.support
        ⟨Finset.nonempty_iff_ne_empty.mpr first_empty, first_chain⟩
      obtain ⟨first_support, first_index, first_member, first_minimum, first_bound⟩ :=
        chainEvaluation_support_and_minimum patches first first_nonneg first_chain greatest present maximal
      have second_nonempty : second.support.Nonempty := by
        by_contra absent
        have second_zero : second = 0 := Finsupp.support_eq_empty.mp
          (Finset.not_nonempty_iff_eq_empty.mp absent)
        have zero : barycenterEvaluationLinearMap patches first = 0 := by
          simpa only [second_zero, map_zero] using equal
        rw [zero, Finsupp.support_zero] at first_support
        have nonempty := activeFaceVertices_nonempty patches greatest
        rw [← first_support] at nonempty
        exact Finset.not_nonempty_empty nonempty
      obtain ⟨second_greatest, second_present, second_maximal⟩ :=
        barycentricFace_has_maximum patches second.support ⟨second_nonempty, second_chain⟩
      obtain ⟨second_support, second_index, second_member, second_minimum, second_bound⟩ :=
        chainEvaluation_support_and_minimum patches second second_nonneg second_chain
          second_greatest second_present second_maximal
      have same_vertices : activeFaceVertices patches greatest = activeFaceVertices patches second_greatest := by
        rw [← first_support, equal, second_support]
      have same_greatest : second_greatest = greatest := by
        apply Subtype.ext
        rw [← activeFaceVertices_image patches greatest,
          ← activeFaceVertices_image patches second_greatest, same_vertices]
      subst second_greatest
      have inverse_positive : 0 < (greatest.val.card : ℝ)⁻¹ :=
        inv_pos.mpr (Nat.cast_pos.mpr ((mem_coverNerve_iff patches _).mp greatest.property).1.card_pos)
      have first_le : first greatest * (greatest.val.card : ℝ)⁻¹ ≤
          second greatest * (greatest.val.card : ℝ)⁻¹ := by
        rw [← second_minimum, ← equal]
        exact first_bound second_index second_member
      have second_le : second greatest * (greatest.val.card : ℝ)⁻¹ ≤
          first greatest * (greatest.val.card : ℝ)⁻¹ := by
        rw [← first_minimum, equal]
        exact second_bound first_index first_member
      have coefficient_equal : first greatest = second greatest := by
        nlinarith
      have erased_equal : barycenterEvaluationLinearMap patches (first.erase greatest) =
          barycenterEvaluationLinearMap patches (second.erase greatest) := by
        have first_decomposition := congrArg (barycenterEvaluationLinearMap patches)
          (Finsupp.single_add_erase greatest first)
        have second_decomposition := congrArg (barycenterEvaluationLinearMap patches)
          (Finsupp.single_add_erase greatest second)
        rw [map_add] at first_decomposition second_decomposition
        apply add_left_cancel (a := barycenterEvaluationLinearMap patches (Finsupp.single greatest (first greatest)))
        rw [first_decomposition, equal, coefficient_equal, second_decomposition]
      have erased_nonneg : ∀ (coefficients : NerveFace patches →₀ ℝ),
          (∀ face, 0 ≤ coefficients face) → ∀ face, 0 ≤ (coefficients.erase greatest) face := by
        intro coefficients nonneg face
        rw [Finsupp.erase_apply]
        split_ifs <;> first | exact le_rfl | exact nonneg face
      have erased_chain : ∀ (coefficients : NerveFace patches →₀ ℝ),
          IsChain (· ≤ ·) (coefficients.support : Set (NerveFace patches)) →
          IsChain (· ≤ ·) ((coefficients.erase greatest).support : Set (NerveFace patches)) := by
        intro coefficients chain
        rw [Finsupp.support_erase]
        exact chain.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
      have smaller : (first.erase greatest).support.card < count := by
        rw [Finsupp.support_erase, ← cardinality]
        exact Finset.card_erase_lt_of_mem present
      have erased_same := induction (first.erase greatest).support.card smaller
        (first.erase greatest) (second.erase greatest)
        (erased_nonneg first first_nonneg) (erased_nonneg second second_nonneg)
        (erased_chain first first_chain) (erased_chain second second_chain) erased_equal rfl
      calc
        first = Finsupp.single greatest (first greatest) + first.erase greatest :=
          (Finsupp.single_add_erase greatest first).symm
        _ = Finsupp.single greatest (second greatest) + second.erase greatest := by
          rw [coefficient_equal, erased_same]
        _ = second := Finsupp.single_add_erase greatest second

theorem subdivisionBarycenterMap_injective (patches : Index → Set E) :
    Function.Injective (subdivisionBarycenterMap patches) := by
  intro first second equal
  apply Subtype.ext
  apply chainEvaluation_injective patches first.val second.val
    (AbstractSimplicialComplex.Realization.nonneg _ first)
    (AbstractSimplicialComplex.Realization.nonneg _ second)
    ((AbstractSimplicialComplex.support_mem _ first).2)
    ((AbstractSimplicialComplex.support_mem _ second).2)
  exact congrArg Subtype.val equal

noncomputable def subdivisionBarycenterHomeomorph (patches : Index → Set E) :
    AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches) ≃ₜ
      AbstractSimplicialComplex.Realization (activeNerve patches) := by
  letI : CompactSpace (AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    finiteRealization_compactSpace _
  letI : T2Space (AbstractSimplicialComplex.Realization (activeNerve patches)) :=
    (realizationCoordinates_isClosedEmbedding _).isEmbedding.t2Space
  let equivalence := Equiv.ofBijective (subdivisionBarycenterMap patches)
    ⟨subdivisionBarycenterMap_injective patches, subdivisionBarycenterMap_surjective patches⟩
  exact (show Continuous equivalence from (subdivisionBarycenterMap patches).continuous).homeoOfEquivCompactToT2

end SubdivisionInjectivity

section EntireNerveEquivalence

variable {Index : Type} {E : Type*} [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def nerveToCompactCore (patches : Index → Set E) :
    C(AbstractSimplicialComplex.Realization (activeNerve patches), compactCore patches) :=
  (barycentricWitnessMap patches).comp
    ⟨(subdivisionBarycenterHomeomorph patches).symm, (subdivisionBarycenterHomeomorph patches).symm.continuous⟩

theorem exists_entire_nerve_homotopyEquiv (patches : Index → Set E) (region : Set E)
    (region_convex : Convex ℝ region) (patches_subset : ∀ index, patches index ⊆ region)
    (patches_convex : ∀ index, Convex ℝ (patches index))
    (patches_closed : ∀ index, IsClosed {point : region | point.val ∈ patches index})
    (cover : (⋃ index, patches index) = region) :
    ∃ equivalence : ContinuousMap.HomotopyEquiv
      (AbstractSimplicialComplex.Realization (activeNerve patches)) (compactCore patches),
      equivalence.toFun = nerveToCompactCore patches := by
  obtain ⟨mapping, ⟨global_homotopy⟩⟩ := exists_global_subdivision_comparison patches region
    region_convex patches_subset patches_convex patches_closed cover
  let inverse : C(AbstractSimplicialComplex.Realization (activeNerve patches),
      AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :=
    ⟨(subdivisionBarycenterHomeomorph patches).symm, (subdivisionBarycenterHomeomorph patches).symm.continuous⟩
  have source_start : (subdivisionBarycenterMap patches).comp inverse =
      ContinuousMap.id (AbstractSimplicialComplex.Realization (activeNerve patches)) := by
    apply ContinuousMap.ext
    intro point
    exact (subdivisionBarycenterHomeomorph patches).apply_symm_apply point
  have source_finish : (mapping.comp (barycentricWitnessMap patches)).comp inverse =
      mapping.comp (nerveToCompactCore patches) := rfl
  let source_homotopy := (global_homotopy.compContinuousMap inverse).cast source_start source_finish
  exact ⟨{
    toFun := nerveToCompactCore patches
    invFun := mapping
    left_inv := ⟨source_homotopy.symm⟩
    right_inv := ⟨convexCoreAffineHomotopy (compactCore patches) (compactCore_convex patches)
      ((nerveToCompactCore patches).comp mapping) (ContinuousMap.id _)⟩
  }, rfl⟩

noncomputable def entireNerveHomotopyEquiv (patches : Index → Set E) (region : Set E)
    (region_convex : Convex ℝ region) (patches_subset : ∀ index, patches index ⊆ region)
    (patches_convex : ∀ index, Convex ℝ (patches index))
    (patches_closed : ∀ index, IsClosed {point : region | point.val ∈ patches index})
    (cover : (⋃ index, patches index) = region) :
    ContinuousMap.HomotopyEquiv (AbstractSimplicialComplex.Realization (activeNerve patches))
      (compactCore patches) :=
  (exists_entire_nerve_homotopyEquiv patches region region_convex patches_subset
    patches_convex patches_closed cover).choose

theorem entireNerve_contractible (patches : Index → Set E) (region : Set E)
    (region_convex : Convex ℝ region) (region_nonempty : region.Nonempty)
    (patches_subset : ∀ index, patches index ⊆ region)
    (patches_convex : ∀ index, Convex ℝ (patches index))
    (patches_closed : ∀ index, IsClosed {point : region | point.val ∈ patches index})
    (cover : (⋃ index, patches index) = region) :
    ContractibleSpace (AbstractSimplicialComplex.Realization (activeNerve patches)) := by
  let : ContractibleSpace (compactCore patches) := (compactCore_convex patches).contractibleSpace
    (compactCore_nonempty patches region cover region_nonempty)
  exact (entireNerveHomotopyEquiv patches region region_convex patches_subset
    patches_convex patches_closed cover).contractibleSpace

end EntireNerveEquivalence

end BondalThomsen.ConvexNerveGlobalCarrierHomotopy
