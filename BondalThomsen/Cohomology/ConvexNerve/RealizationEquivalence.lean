module

public import BondalThomsen.Cohomology.ConvexNerve.OpenNeighborhoods
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped Classical
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveBarycentricHomotopy
open BondalThomsen.ConvexNerveOpenNeighborhoods

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveRealizationEquivalence

section FiniteRealizations

variable {Vertex : Type} [Finite Vertex]

noncomputable def faceSimplexEquiv (face : Finset Vertex) :
    Convexity.StdSimplex ℝ face ≃ AbstractSimplicialComplex.StandardSimplex face where
  toFun point := ⟨(point.map Subtype.val).weights, by
    rw [Finset.coe_image]
    apply AbstractSimplicialComplex.mem_standardSimplex_iff.mpr
    refine ⟨(point.map Subtype.val).nonneg, (point.map Subtype.val).total, ?_⟩
    rw [Convexity.StdSimplex.weights_map, Finsupp.support_mapDomain_of_nonneg point.nonneg]
    intro vertex present
    obtain ⟨original, _, rfl⟩ := Finset.mem_image.mp present
    exact original.property⟩
  invFun point := {
    weights := Finsupp.equivFunOnFinite.symm (fun vertex : face => point.val vertex.val)
    nonneg := fun vertex => AbstractSimplicialComplex.StandardSimplex.nonneg point vertex.val
    total := by
      rw [Finsupp.equivFunOnFinite_symm_sum]
      rw [Finset.sum_coe_sort face (fun vertex => point.val vertex)]
      rw [← point.val.sum_of_support_subset
        (AbstractSimplicialComplex.StandardSimplex.support_subset point) (fun _ weight => weight)
        (fun _ _ => rfl)]
      exact AbstractSimplicialComplex.StandardSimplex.sum_eq_one point
  }
  left_inv point := by
    apply Convexity.StdSimplex.ext
    ext vertex
    exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective point.weights vertex
  right_inv point := by
    apply Subtype.ext
    ext vertex
    change (Finsupp.mapDomain (Subtype.val : face → Vertex)
      (Finsupp.equivFunOnFinite.symm (fun original : face => point.val original.val))) vertex = point.val vertex
    by_cases present : vertex ∈ face
    · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨vertex, present⟩
    · have absent : vertex ∉ (Finsupp.mapDomain (Subtype.val : face → Vertex)
          (Finsupp.equivFunOnFinite.symm (fun original : face => point.val original.val))).support := by
        have nonnegative : 0 ≤ Finsupp.equivFunOnFinite.symm
            (fun original : face => point.val original.val) :=
          fun original => AbstractSimplicialComplex.StandardSimplex.nonneg point original.val
        rw [Finsupp.support_mapDomain_of_nonneg nonnegative]
        intro contains
        obtain ⟨original, _, same⟩ := Finset.mem_image.mp contains
        exact present (same ▸ original.property)
      rw [Finsupp.notMem_support_iff.mp absent]
      exact (Finsupp.notMem_support_iff.mp
        (fun contains => present (AbstractSimplicialComplex.StandardSimplex.support_subset point contains))).symm

theorem faceSimplexEquiv_continuous (face : Finset Vertex) :
    Continuous (faceSimplexEquiv face) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro vertex
  exact (continuous_apply vertex).comp
    ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Vertex).continuous.comp
      (Convexity.StdSimplex.continuous_map ℝ Subtype.val))

theorem standardSimplex_compactSpace (face : Finset Vertex) :
    CompactSpace (AbstractSimplicialComplex.StandardSimplex face) := by
  exact (faceSimplexEquiv face).surjective.compactSpace (faceSimplexEquiv_continuous face)

theorem finiteRealization_compactSpace (complex : AbstractSimplicialComplex Vertex) :
    CompactSpace (AbstractSimplicialComplex.Realization complex) := by
  have cover : (⋃ face : TauCeti.SetLike.Face complex,
      Set.range (AbstractSimplicialComplex.faceInclusion complex face)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro point
    obtain ⟨face, present, membership⟩ := AbstractSimplicialComplex.mem_realization_iff.mp point.property
    exact Set.mem_iUnion.mpr ⟨⟨face, present⟩, ⟨⟨point.val, membership⟩, Subtype.ext rfl⟩⟩
  constructor
  rw [← cover]
  apply isCompact_iUnion
  intro face
  let := standardSimplex_compactSpace face.val
  exact isCompact_range (AbstractSimplicialComplex.continuous_faceInclusion complex face)

omit [Finite Vertex] in
theorem realizationCoordinates_continuous (complex : AbstractSimplicialComplex Vertex) :
    Continuous (fun point : AbstractSimplicialComplex.Realization complex => (point.val : Vertex → ℝ)) := by
  apply AbstractSimplicialComplex.continuous_iff_faceInclusion.mpr
  intro face
  exact continuous_induced_dom

theorem realizationCoordinates_isClosedEmbedding (complex : AbstractSimplicialComplex Vertex) :
    Topology.IsClosedEmbedding
      (fun point : AbstractSimplicialComplex.Realization complex => (point.val : Vertex → ℝ)) := by
  let := finiteRealization_compactSpace complex
  apply (realizationCoordinates_continuous complex).isClosedEmbedding
  intro first second same
  apply Subtype.ext
  exact Finsupp.ext (congrFun same)

theorem continuous_into_realization_iff (complex : AbstractSimplicialComplex Vertex)
    {Space : Type*} [TopologicalSpace Space]
    (mapping : Space → AbstractSimplicialComplex.Realization complex) :
    Continuous mapping ↔ ∀ vertex, Continuous (fun point => (mapping point).val vertex) := by
  rw [(realizationCoordinates_isClosedEmbedding complex).isEmbedding.continuous_iff]
  exact continuous_pi_iff

end FiniteRealizations

section SupportedCoordinates

variable {Vertex : Type} [Finite Vertex]

noncomputable def realizationToSimplex (complex : AbstractSimplicialComplex Vertex) :
    C(AbstractSimplicialComplex.Realization complex, Convexity.StdSimplex ℝ Vertex) where
  toFun point := {
    weights := point.val
    nonneg := fun vertex => AbstractSimplicialComplex.StandardSimplex.nonneg
      ⟨point.val, AbstractSimplicialComplex.mem_convexHull_carrier complex point⟩ vertex
    total := AbstractSimplicialComplex.StandardSimplex.sum_eq_one
      ⟨point.val, AbstractSimplicialComplex.mem_convexHull_carrier complex point⟩
  }
  continuous_toFun :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Vertex).continuous_iff.mpr
      (realizationCoordinates_continuous complex)

noncomputable def simplexToRealization (complex : AbstractSimplicialComplex Vertex)
    (point : Convexity.StdSimplex ℝ Vertex) (supported : point.weights.support ∈ complex) :
    AbstractSimplicialComplex.Realization complex :=
  ⟨point.weights, AbstractSimplicialComplex.mem_realization_iff.mpr ⟨point.weights.support, supported, by
    rw [Finset.coe_image]
    exact AbstractSimplicialComplex.mem_standardSimplex_iff.mpr
      ⟨point.nonneg, point.total, Finset.Subset.refl _⟩⟩⟩

end SupportedCoordinates

section SimplicialHomotopies

variable {Vertex : Type} [Finite Vertex]

noncomputable def realizationAffineHomotopy (complex : AbstractSimplicialComplex Vertex)
    {Space : Type*} [TopologicalSpace Space]
    (first second : C(Space, AbstractSimplicialComplex.Realization complex))
    (contiguous : ∀ point, (first point).val.support ∪ (second point).val.support ∈ complex) :
    first.Homotopy second where
  toFun pair := ⟨(1 - (pair.1 : ℝ)) • (first pair.2).val + (pair.1 : ℝ) • (second pair.2).val, by
    apply AbstractSimplicialComplex.mem_realization_iff.mpr
    refine ⟨(first pair.2).val.support ∪ (second pair.2).val.support, contiguous pair.2, ?_⟩
    have first_mem := AbstractSimplicialComplex.mem_convexHull_carrier complex (first pair.2)
    have second_mem := AbstractSimplicialComplex.mem_convexHull_carrier complex (second pair.2)
    apply (convex_convexHull ℝ _)
      (convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image Finset.subset_union_left)) first_mem)
      (convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image Finset.subset_union_right)) second_mem)
      (sub_nonneg.mpr pair.1.property.2) pair.1.property.1 (sub_add_cancel 1 (pair.1 : ℝ))⟩
  continuous_toFun := by
    apply (continuous_into_realization_iff complex _).mpr
    intro vertex
    have time : Continuous (fun pair : unitInterval × Space => (pair.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have first_coordinate : Continuous (fun pair : unitInterval × Space => (first pair.2).val vertex) :=
      ((continuous_into_realization_iff complex first).mp first.continuous vertex).comp continuous_snd
    have second_coordinate : Continuous (fun pair : unitInterval × Space => (second pair.2).val vertex) :=
      ((continuous_into_realization_iff complex second).mp second.continuous vertex).comp continuous_snd
    exact ((continuous_const.sub time).mul first_coordinate).add (time.mul second_coordinate)
  map_zero_left := by intro point; apply Subtype.ext; simp
  map_one_left := by intro point; apply Subtype.ext; simp

theorem realizationAffineHomotopy_mem_face (complex : AbstractSimplicialComplex Vertex)
    {Space : Type*} [TopologicalSpace Space]
    (first second : C(Space, AbstractSimplicialComplex.Realization complex))
    (contiguous : ∀ point, (first point).val.support ∪ (second point).val.support ∈ complex)
    (face : Finset Vertex) (point : Space)
    (first_contained : (first point).val.support ⊆ face)
    (second_contained : (second point).val.support ⊆ face) (time : unitInterval) :
    ((realizationAffineHomotopy complex first second contiguous) (time, point)).val.support ⊆ face := by
  apply Finsupp.support_add.trans
  exact Finset.union_subset
    (Finsupp.support_smul.trans first_contained) (Finsupp.support_smul.trans second_contained)

end SimplicialHomotopies

section ActualNerve

variable {Index : Type} {E : Type*} [Finite Index]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev ActiveIndex (patches : Index → Set E) := {index : Index // (patches index).Nonempty}

noncomputable def activeNerve (patches : Index → Set E) : AbstractSimplicialComplex (ActiveIndex patches) where
  faces := {face | face.image Subtype.val ∈ coverNerve patches}
  isRelLowerSet_faces := by
    intro face present
    have nonempty : face.Nonempty := by
      obtain ⟨index, contains⟩ := ((mem_coverNerve_iff patches _).mp present).1
      obtain ⟨original, contains, _⟩ := Finset.mem_image.mp contains
      exact ⟨original, contains⟩
    refine ⟨nonempty, ?_⟩
    intro smaller contained smaller_nonempty
    exact (coverNerve patches).isRelLowerSet_faces.mem_of_le present
      (Finset.image_subset_image contained) (smaller_nonempty.image _)
  singleton_mem := by
    intro index
    apply (mem_coverNerve_iff patches _).mpr
    obtain ⟨point, present⟩ := index.property
    exact ⟨by simp, point, by simpa using present⟩

noncomputable def coordinatesActiveSimplex (patches : Index → Set E)
    (coordinates : Convexity.StdSimplex ℝ Index)
    (supported : coordinates.weights.support ∈ coverNerve patches) :
    Convexity.StdSimplex ℝ (ActiveIndex patches) where
  weights := Finsupp.equivFunOnFinite.symm (fun index => coordinates.weights index.val)
  nonneg := fun index => coordinates.nonneg index.val
  total := by
    let : Fintype Index := Fintype.ofFinite _
    let : Fintype (ActiveIndex patches) := Fintype.ofFinite _
    rw [Finsupp.equivFunOnFinite_symm_sum]
    have sum_active : ∑ index : ActiveIndex patches, coordinates.weights index.val =
        ∑ index ∈ coordinates.weights.support, coordinates.weights index := by
      apply Finset.sum_bij_ne_zero (fun index _ _ => index.val)
      · intro index _ nonzero
        exact Finsupp.mem_support_iff.mpr nonzero
      · intro first _ _ second _ _ same
        exact Subtype.ext same
      · intro index contains _
        obtain ⟨witness, membership⟩ := ((mem_coverNerve_iff patches _).mp supported).2
        exact ⟨⟨index, witness, membership index contains⟩, Finset.mem_univ _,
          Finsupp.mem_support_iff.mp contains, rfl⟩
      · intro index _ _
        rfl
    rw [sum_active]
    exact coordinates.total

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem coordinatesActiveSimplex_image_support (patches : Index → Set E)
    (coordinates : Convexity.StdSimplex ℝ Index)
    (supported : coordinates.weights.support ∈ coverNerve patches) :
    (coordinatesActiveSimplex patches coordinates supported).weights.support.image Subtype.val =
      coordinates.weights.support := by
  ext index
  constructor
  · rintro contains
    obtain ⟨original, original_present, rfl⟩ := Finset.mem_image.mp contains
    apply Finsupp.mem_support_iff.mpr
    change coordinates.weights original.val ≠ 0
    have nonzero := Finsupp.mem_support_iff.mp original_present
    change coordinates.weights original.val ≠ 0 at nonzero
    exact nonzero
  · intro contains
    obtain ⟨witness, membership⟩ := ((mem_coverNerve_iff patches _).mp supported).2
    let original : ActiveIndex patches := ⟨index, witness, membership index contains⟩
    apply Finset.mem_image.mpr
    refine ⟨original, ?_, rfl⟩
    apply Finsupp.mem_support_iff.mpr
    change coordinates.weights index ≠ 0
    exact Finsupp.mem_support_iff.mp contains

noncomputable def coordinatesToNerve (patches : Index → Set E)
    (coordinates : Convexity.StdSimplex ℝ Index)
    (supported : coordinates.weights.support ∈ coverNerve patches) :
    AbstractSimplicialComplex.Realization (activeNerve patches) :=
  simplexToRealization (activeNerve patches) (coordinatesActiveSimplex patches coordinates supported) (by
    change (coordinatesActiveSimplex patches coordinates supported).weights.support.image Subtype.val ∈
      coverNerve patches
    rw [coordinatesActiveSimplex_image_support]
    exact supported)

end ActualNerve

section SubdivisionMaps

variable {Index : Type} {E : Type*} [Finite Index]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem barycentricFace_has_maximum (patches : Index → Set E)
    (vertices : Finset (NerveFace patches)) (present : vertices ∈ nerveBarycentricComplex patches) :
    ∃ greatest ∈ vertices, ∀ face ∈ vertices, face.val ⊆ greatest.val := by
  obtain ⟨nonempty, chain⟩ := (mem_nerveBarycentricComplex_iff patches vertices).mp present
  obtain ⟨greatest, present, maximal⟩ := vertices.exists_max_image (fun face => face.val.card) nonempty
  refine ⟨greatest, present, ?_⟩
  intro face face_present
  rcases chain.total face_present present with contained | reverse
  · exact contained
  · have same : greatest.val = face.val :=
      Finset.eq_of_subset_of_card_le reverse (maximal face face_present)
    rw [same]

noncomputable def activeFaceVertices (patches : Index → Set E) (face : NerveFace patches) :
    Finset (ActiveIndex patches) :=
  face.val.attach.image (fun index =>
    ⟨index.val, intersectionWitness patches face, intersectionWitness_mem patches face index.val index.property⟩)

omit [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem activeFaceVertices_image (patches : Index → Set E) (face : NerveFace patches) :
    (activeFaceVertices patches face).image Subtype.val = face.val := by
  simp [activeFaceVertices, Finset.image_image, Function.comp_def]

omit [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem activeFaceVertices_nonempty (patches : Index → Set E) (face : NerveFace patches) :
    (activeFaceVertices patches face).Nonempty := by
  have nonempty := ((mem_coverNerve_iff patches face.val).mp face.property).1
  exact nonempty.attach.image _

omit [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem activeFaceVertices_mono (patches : Index → Set E) (first second : NerveFace patches)
    (contained : first.val ⊆ second.val) : activeFaceVertices patches first ⊆ activeFaceVertices patches second := by
  intro index present
  obtain ⟨original, _, same⟩ := Finset.mem_image.mp present
  apply Finset.mem_image.mpr
  refine ⟨⟨original.val, contained original.property⟩, Finset.mem_attach _ _, ?_⟩
  exact Subtype.ext (congrArg Subtype.val same)

noncomputable def activeFaceBarycenter (patches : Index → Set E) (face : NerveFace patches) :
    Convexity.StdSimplex ℝ (ActiveIndex patches) :=
  Convexity.StdSimplex.subBarycenter (activeFaceVertices patches face) (activeFaceVertices_nonempty patches face)

noncomputable def subdivisionEvaluation (patches : Index → Set E)
    (vertex_values : NerveFace patches → Convexity.StdSimplex ℝ (ActiveIndex patches))
    (point : AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :
    ActiveIndex patches →₀ ℝ :=
  point.val.sum (fun face weight => weight • (vertex_values face).weights)

omit [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem subdivisionEvaluation_face_mem (patches : Index → Set E)
    (vertex_values : NerveFace patches → Convexity.StdSimplex ℝ (ActiveIndex patches))
    (carried : ∀ face, (vertex_values face).weights.support ⊆ activeFaceVertices patches face)
    (point : AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches))
    (greatest : NerveFace patches)
    (maximal : ∀ face ∈ point.val.support, face.val ⊆ greatest.val) :
    subdivisionEvaluation patches vertex_values point ∈
      convexHull ℝ ((fun index => Finsupp.single index (1 : ℝ)) ''
        (activeFaceVertices patches greatest : Set (ActiveIndex patches))) := by
  let simplex : AbstractSimplicialComplex.StandardSimplex point.val.support :=
    ⟨point.val, AbstractSimplicialComplex.mem_convexHull_carrier _ point⟩
  change (∑ face ∈ point.val.support, point.val face • (vertex_values face).weights) ∈ _
  have sum_one : ∑ face ∈ point.val.support, point.val face = 1 := by
    simpa only [simplex, Finsupp.sum] using AbstractSimplicialComplex.StandardSimplex.sum_eq_one simplex
  refine (convex_convexHull ℝ _).sum_mem
    (t := point.val.support) (w := fun face => point.val face)
    (z := fun face => (vertex_values face).weights) ?_ sum_one ?_
  · intro face _
    exact AbstractSimplicialComplex.StandardSimplex.nonneg simplex face
  · intro face present
    exact AbstractSimplicialComplex.mem_standardSimplex_iff.mpr
      ⟨(vertex_values face).nonneg, (vertex_values face).total,
        (carried face).trans (activeFaceVertices_mono patches face greatest (maximal face present))⟩

noncomputable def subdivisionRealizationMap (patches : Index → Set E)
    (vertex_values : NerveFace patches → Convexity.StdSimplex ℝ (ActiveIndex patches))
    (carried : ∀ face, (vertex_values face).weights.support ⊆ activeFaceVertices patches face) :
    C(AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches),
      AbstractSimplicialComplex.Realization (activeNerve patches)) where
  toFun point := ⟨subdivisionEvaluation patches vertex_values point, by
    obtain ⟨greatest, _, maximal⟩ := barycentricFace_has_maximum patches point.val.support
      (AbstractSimplicialComplex.support_mem _ point)
    apply AbstractSimplicialComplex.mem_realization_iff.mpr
    refine ⟨activeFaceVertices patches greatest, ?_, ?_⟩
    · change (activeFaceVertices patches greatest).image Subtype.val ∈ coverNerve patches
      rw [activeFaceVertices_image]
      exact greatest.property
    · convert subdivisionEvaluation_face_mem patches vertex_values carried point greatest maximal using 1
      ext coordinate
      simp only [Finset.coe_image]⟩
  continuous_toFun := by
    apply AbstractSimplicialComplex.continuous_iff_faceInclusion.mpr
    intro face
    apply (continuous_into_realization_iff (activeNerve patches) _).mpr
    intro index
    have formula : ∀ point : AbstractSimplicialComplex.StandardSimplex face.val,
        subdivisionEvaluation patches vertex_values (AbstractSimplicialComplex.faceInclusion _ face point) index =
          ∑ vertex ∈ face.val, point.val vertex * (vertex_values vertex).weights index := by
      intro point
      unfold subdivisionEvaluation
      rw [AbstractSimplicialComplex.faceInclusion_val]
      rw [point.val.sum_of_support_subset (AbstractSimplicialComplex.StandardSimplex.support_subset point)
        (fun vertex weight => weight • (vertex_values vertex).weights) (fun _ _ => zero_smul ℝ _)]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply (continuous_finsetSum _ fun vertex _ =>
      ((continuous_apply vertex).comp (continuous_induced_dom :
        Continuous (fun point : AbstractSimplicialComplex.StandardSimplex face.val =>
          (point.val : NerveFace patches → ℝ)))).mul continuous_const).congr
    intro point
    exact (formula point).symm

omit [Finite Index] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem activeFaceBarycenter_carried (patches : Index → Set E) (face : NerveFace patches) :
    (activeFaceBarycenter patches face).weights.support ⊆ activeFaceVertices patches face := by
  intro index present
  by_contra absent
  exact (Finsupp.mem_support_iff.mp present)
    (Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero _ _ index absent)

noncomputable def subdivisionBarycenterMap (patches : Index → Set E) :=
  subdivisionRealizationMap patches (activeFaceBarycenter patches) (activeFaceBarycenter_carried patches)

end SubdivisionMaps

section SourceClosedStars

variable {Vertex : Type} [Finite Vertex]

abbrev RealizedClosedStar (complex : AbstractSimplicialComplex Vertex) (face : Finset Vertex) :=
  {point : AbstractSimplicialComplex.Realization complex // point.val.support ∪ face ∈ complex}

noncomputable def closedStarAnchor (complex : AbstractSimplicialComplex Vertex)
    (face : TauCeti.SetLike.Face complex) : RealizedClosedStar complex face.val :=
  ⟨simplexToRealization complex
    (Convexity.StdSimplex.subBarycenter face.val (complex.isRelLowerSet_faces.prop_of_mem face.property))
    (by
      apply complex.isRelLowerSet_faces.mem_of_le face.property
      · intro vertex present
        by_contra absent
        exact (Finsupp.mem_support_iff.mp present)
          (Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero _ _ vertex absent)
      · exact Convexity.StdSimplex.support_weights_nonempty _), by
    have contained :
        (Convexity.StdSimplex.subBarycenter (K := ℝ) face.val
          (complex.isRelLowerSet_faces.prop_of_mem face.property)).weights.support ⊆ face.val := by
      intro vertex present
      by_contra absent
      exact (Finsupp.mem_support_iff.mp present)
        (Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero _ _ vertex absent)
    change (Convexity.StdSimplex.subBarycenter (K := ℝ) face.val
      (complex.isRelLowerSet_faces.prop_of_mem face.property)).weights.support ∪ face.val ∈ complex
    rw [Finset.union_eq_right.mpr contained]
    exact face.property⟩

noncomputable def closedStarContraction (complex : AbstractSimplicialComplex Vertex)
    (face : TauCeti.SetLike.Face complex) :
    (ContinuousMap.id (RealizedClosedStar complex face.val)).Homotopy
      (ContinuousMap.const _ (closedStarAnchor complex face)) := by
  let inclusion : C(RealizedClosedStar complex face.val, AbstractSimplicialComplex.Realization complex) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let anchor : C(RealizedClosedStar complex face.val, AbstractSimplicialComplex.Realization complex) :=
    ContinuousMap.const _ (closedStarAnchor complex face).val
  have anchor_support : (closedStarAnchor complex face).val.val.support ⊆ face.val := by
    intro vertex present
    by_contra absent
    exact (Finsupp.mem_support_iff.mp present)
      (Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero face.val
        (complex.isRelLowerSet_faces.prop_of_mem face.property) vertex absent)
  have contiguous : ∀ point, (inclusion point).val.support ∪ (anchor point).val.support ∈ complex := by
    intro point
    apply complex.isRelLowerSet_faces.mem_of_le point.property
      (Finset.union_subset_union_right anchor_support)
    exact (complex.isRelLowerSet_faces.prop_of_mem (AbstractSimplicialComplex.support_mem complex point.val)).mono
      Finset.subset_union_left
  let homotopy := realizationAffineHomotopy complex inclusion anchor contiguous
  have stays : ∀ pair : unitInterval × RealizedClosedStar complex face.val,
      (homotopy pair).val.support ∪ face.val ∈ complex := by
    intro pair
    apply complex.isRelLowerSet_faces.mem_of_le pair.2.property
      (Finset.union_subset
        (realizationAffineHomotopy_mem_face complex inclusion anchor contiguous _ pair.2
          Finset.subset_union_left (anchor_support.trans Finset.subset_union_right) pair.1)
        Finset.subset_union_right)
    exact (complex.isRelLowerSet_faces.prop_of_mem face.property).mono Finset.subset_union_right
  refine {
    toFun := fun pair => ⟨homotopy pair, stays pair⟩
    continuous_toFun := homotopy.continuous.subtype_mk stays
    map_zero_left := ?_
    map_one_left := ?_
  }
  · intro point
    apply Subtype.ext
    exact homotopy.map_zero_left point
  · intro point
    apply Subtype.ext
    exact homotopy.map_one_left point

theorem realizedClosedStar_contractible (complex : AbstractSimplicialComplex Vertex)
    (face : TauCeti.SetLike.Face complex) : ContractibleSpace (RealizedClosedStar complex face.val) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨closedStarAnchor complex face, ⟨closedStarContraction complex face⟩⟩

end SourceClosedStars

section CompositeCarriers

variable {Index : Type} {E : Type*} [Finite Index]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def convexCoreAffineHomotopy (core : Set E) (core_convex : Convex ℝ core)
    {Space : Type*} [TopologicalSpace Space] (first second : C(Space, core)) : first.Homotopy second where
  toFun pair := ⟨(1 - (pair.1 : ℝ)) • (first pair.2).val + (pair.1 : ℝ) • (second pair.2).val,
    core_convex (first pair.2).property (second pair.2).property
      (sub_nonneg.mpr pair.1.property.2) pair.1.property.1 (sub_add_cancel 1 (pair.1 : ℝ))⟩
  continuous_toFun := by
    have time : Continuous (fun pair : unitInterval × Space => (pair.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have first_value : Continuous (fun pair : unitInterval × Space => (first pair.2).val) :=
      continuous_subtype_val.comp (first.continuous.comp continuous_snd)
    have second_value : Continuous (fun pair : unitInterval × Space => (second pair.2).val) :=
      continuous_subtype_val.comp (second.continuous.comp continuous_snd)
    exact (((continuous_const.sub time).smul first_value).add (time.smul second_value)).subtype_mk _
  map_zero_left := by intro point; apply Subtype.ext; simp
  map_one_left := by intro point; apply Subtype.ext; simp

end CompositeCarriers

end BondalThomsen.ConvexNerveRealizationEquivalence
