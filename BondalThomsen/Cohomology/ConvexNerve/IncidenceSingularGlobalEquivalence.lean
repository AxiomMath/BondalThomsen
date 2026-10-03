module

public import BondalThomsen.Cohomology.ConvexNerve.IncidenceSingularChainEquivalence

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceHomologyComparison
open BondalThomsen.ConvexNerveAcyclicCarrierAssembly
open BondalThomsen.ConvexNerveSmallSingularComparison
open BondalThomsen.ConvexNerveSmallChainQuasiIso
open BondalThomsen.ConvexNerveSmallChainPositiveComparison
open BondalThomsen.ConvexNerveSmallChainMeshShrinking
open BondalThomsen.ConvexNerveSubdivisionCellExpansion
open BondalThomsen.ConvexNerveIncidenceSingularChainEquivalence
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial BigOperators

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveIncidenceSingularGlobalEquivalence

section ImageCarriers

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

def imagePointIncidence (degree : ℕ) (simplex : (openStarSmallSet incidence negative) _⦋degree⦌)
    (point : Convexity.StdSimplex ℝ (Fin (degree + 1))) (chart : Chart) : Prop :=
  ∃ vertex ∈ (singularSimplexMap incidence negative (.op ⦋degree⦌) simplex.val point).val.support,
    vertex.val = chart

omit [Finite Chart] in
theorem imagePointIncidence_original (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌)
    (point : Convexity.StdSimplex ℝ (Fin (degree + 1))) :
    ∃ ray, negative ray ∧ ∀ chart, imagePointIncidence incidence negative degree simplex point chart →
      incidence ray chart := by
  have face := AbstractSimplicialComplex.support_mem (activeNerve (incidencePatches incidence negative))
    (singularSimplexMap incidence negative (.op ⦋degree⦌) simplex.val point)
  change (singularSimplexMap incidence negative (.op ⦋degree⦌) simplex.val point).val.support.image
    Subtype.val ∈ coverNerve (incidencePatches incidence negative) at face
  rw [incidencePatches_coverNerve] at face
  obtain ⟨nonempty, ray, negativeRay, contains⟩ := face
  exact ⟨ray, negativeRay, fun chart ⟨vertex, supported, equal⟩ =>
    contains chart (Finset.mem_image.mpr ⟨vertex, supported, equal⟩)⟩

noncomputable def imageCarrierSimplicialInclusion (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) :
    incidenceSimplicialSet (imagePointIncidence incidence negative degree simplex) (fun _point => True) ⟶
      incidenceSimplicialSet incidence negative where
  app _shape := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨point, _positive, contains⟩ := tuple.property
    obtain ⟨ray, negativeRay, original⟩ := imagePointIncidence_original incidence negative degree simplex point
    exact ⟨ray, negativeRay, fun column => original _ (contains column)⟩⟩
  naturality {source target} selection := by apply ConcreteCategory.hom_ext; intro tuple; rfl

noncomputable def imageCarrierChainInclusion (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) :
    incidenceChains (imagePointIncidence incidence negative degree simplex) (fun _point => True) ⟶
      incidenceChains incidence negative :=
  SSet.chainComplexMap (imageCarrierSimplicialInclusion incidence negative degree simplex) (AddCommGrpCat.of ℤ)

omit [Finite Chart] in
theorem imageCarrierChainInclusion_mono (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) (component : ℕ) :
    Mono ((imageCarrierChainInclusion incidence negative degree simplex).f component) := by
  let inclusion := imageCarrierSimplicialInclusion incidence negative degree simplex
  have componentMono (shape : SimplexCategoryᵒᵖ) : Mono (inclusion.app shape) := by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro first second equal
    apply Subtype.ext
    exact congrArg (fun tuple => tuple.val) equal
  let : Mono inclusion := NatTrans.mono_of_mono_app inclusion
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of inclusion).hom (AddCommGrpCat.of ℤ)).f component))

omit [Finite Chart] in
theorem imageCarrierChainInclusion_augmentation (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) :
    (imageCarrierChainInclusion incidence negative degree simplex).f 0 ≫
      incidenceChainAugmentation incidence negative =
      incidenceChainAugmentation (imagePointIncidence incidence negative degree simplex) (fun _point => True) := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  rw [← Category.assoc, imageCarrierChainInclusion, SSet.ι_chainComplexMap_f]
  exact (incidenceChainAugmentation_generator _ _ _).trans
    (incidenceChainAugmentation_generator _ _ _).symm

theorem imageCarrier_isCone (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌)
    (vertex : ActiveIndex (incidencePatches incidence negative))
    (positive : vertex ∈ commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val) :
    PreAbstractSimplicialComplex.IsCone
      (negativeChartComplex (imagePointIncidence incidence negative degree simplex) (fun _point => True))
      vertex.val where
  apex_mem := ⟨Finset.singleton_nonempty _, Convexity.StdSimplex.single 0, trivial,
    fun chart member => by
      obtain rfl := Finset.mem_singleton.mp member
      exact ⟨vertex, commonPositiveVertices_support incidence negative _ simplex.val _ positive, rfl⟩⟩
  insert_mem := by
    intro face present
    obtain ⟨nonempty, point, _positive, contains⟩ := present
    refine ⟨Finset.insert_nonempty _ _, point, trivial, fun chart member => ?_⟩
    rcases Finset.mem_insert.mp member with equal | contained
    · subst chart
      exact ⟨vertex, commonPositiveVertices_support incidence negative _ simplex.val point positive, rfl⟩
    · exact contains chart contained

noncomputable def imageCarrierRefinement (degree : ℕ) (deleted : Fin (degree + 2))
    (simplex : (openStarSmallSet incidence negative) _⦋degree + 1⦌) :
    incidenceSimplicialSet
      (imagePointIncidence incidence negative degree ((openStarSmallSet incidence negative).δ deleted simplex))
      (fun _point => True) ⟶
    incidenceSimplicialSet (imagePointIncidence incidence negative (degree + 1) simplex) (fun _point => True) where
  app _shape := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨point, _positive, contains⟩ := tuple.property
    refine ⟨point.map deleted.succAbove, trivial, fun column => ?_⟩
    obtain ⟨vertex, supported, equal⟩ := contains column
    refine ⟨vertex, ?_, equal⟩
    change vertex ∈ (singularSimplexMap incidence negative (.op ⦋degree⦌)
      ((incidenceSingularSet incidence negative).map (SimplexCategory.δ deleted).op simplex.val) point).val.support
      at supported
    rw [singularSimplexMap_precomp] at supported
    exact supported⟩
  naturality {source target} selection := by apply ConcreteCategory.hom_ext; intro tuple; rfl

noncomputable def imageIncidenceCarrier :
    IntegralAcyclicCarrier (openStarSmallSet incidence negative)
      (incidenceChains incidence negative) (incidenceChainAugmentation incidence negative) where
  complex degree simplex := incidenceChains
    (imagePointIncidence incidence negative degree simplex) (fun _point => True)
  inclusion degree simplex := imageCarrierChainInclusion incidence negative degree simplex
  inclusion_mono degree simplex component := imageCarrierChainInclusion_mono incidence negative degree simplex component
  faceMap degree deleted simplex := SSet.chainComplexMap
    (imageCarrierRefinement incidence negative degree deleted simplex) (AddCommGrpCat.of ℤ)
  faceMap_inclusion degree deleted simplex := by
    apply HomologicalComplex.Hom.ext
    funext component
    apply SSet.chainComplex_hom_ext
    intro tuple
    change _ ≫ ((SSet.chainComplexMap (imageCarrierRefinement incidence negative degree deleted simplex)
      (AddCommGrpCat.of ℤ)).f component ≫ _) = _
    rw [← Category.assoc, SSet.ι_chainComplexMap_f, imageCarrierChainInclusion,
      SSet.ι_chainComplexMap_f, imageCarrierChainInclusion, SSet.ι_chainComplexMap_f]
    congr 1
  augmentation_zero degree simplex := by
    rw [imageCarrierChainInclusion_augmentation, incidenceChainAugmentation_zero]
  exact_zero degree simplex := by
    simp only [imageCarrierChainInclusion_augmentation]
    obtain ⟨vertex, positive⟩ := commonPositiveVertices_nonempty incidence negative _ simplex.val simplex.property
    exact incidenceConeChains_augmentedExact _ _ vertex.val
      (imageCarrier_isCone incidence negative degree simplex vertex positive)
  exact_positive degree simplex component := by
    obtain ⟨vertex, positive⟩ := commonPositiveVertices_nonempty incidence negative _ simplex.val simplex.property
    exact incidenceConeChains_exactAt_positive _ _ vertex.val
      (imageCarrier_isCone incidence negative degree simplex vertex positive) component

noncomputable def imageCarrierVertexValues : (imageIncidenceCarrier incidence negative).CarrierMapValues 0 :=
  fun simplex => (incidenceSimplicialSet (imagePointIncidence incidence negative 0 simplex)
    (fun _point => True)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      ⟨fun _column => smallVertexChoice incidence negative simplex, by
        obtain ⟨vertex, positive, equal⟩ := Finset.mem_image.mp (smallVertexChoice_mem incidence negative simplex)
        refine ⟨Convexity.StdSimplex.single 0, trivial, fun _column => ?_⟩
        exact ⟨vertex, commonPositiveVertices_support incidence negative _ simplex.val _ positive, equal⟩⟩

theorem imageCarrierVertexValues_augmentation (simplex : (openStarSmallSet incidence negative) _⦋0⦌) :
    imageCarrierVertexValues incidence negative simplex ≫
      ((imageIncidenceCarrier incidence negative).inclusion 0 simplex).f 0 ≫
        incidenceChainAugmentation incidence negative =
      Sigma.ι (fun _point : Unit => AddCommGrpCat.of ℤ) () := by
  change _ ≫ (imageCarrierChainInclusion incidence negative 0 simplex).f 0 ≫ _ = _
  rw [imageCarrierChainInclusion_augmentation]
  exact incidenceChainAugmentation_generator _ _ _

theorem imageCarrierVertexValues_compatible (simplex : (openStarSmallSet incidence negative) _⦋1⦌) :
    imageCarrierVertexValues incidence negative ((openStarSmallSet incidence negative).δ 0 simplex) ≫
      ((imageIncidenceCarrier incidence negative).inclusion 0
        ((openStarSmallSet incidence negative).δ 0 simplex)).f 0 ≫ incidenceChainAugmentation incidence negative =
    imageCarrierVertexValues incidence negative ((openStarSmallSet incidence negative).δ 1 simplex) ≫
      ((imageIncidenceCarrier incidence negative).inclusion 0
        ((openStarSmallSet incidence negative).δ 1 simplex)).f 0 ≫ incidenceChainAugmentation incidence negative := by
  rw [imageCarrierVertexValues_augmentation, imageCarrierVertexValues_augmentation]

noncomputable def imageSmallIncidenceMap :
    (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) ⟶ incidenceChains incidence negative :=
  (imageIncidenceCarrier incidence negative).extendCarriedVertexMap (imageCarrierVertexValues incidence negative)
    (imageCarrierVertexValues_compatible incidence negative)

noncomputable def imageSmallIncidenceMap_carried :
    (imageIncidenceCarrier incidence negative).CarriedIntegralChainMap (imageSmallIncidenceMap incidence negative) :=
  (imageIncidenceCarrier incidence negative).extendCarriedVertexMap_carried
    (imageCarrierVertexValues incidence negative) (imageCarrierVertexValues_compatible incidence negative)

noncomputable def imageCarrierClosedStarInclusion (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) :
    incidenceSimplicialSet (imagePointIncidence incidence negative degree simplex) (fun _point => True) ⟶
      incidenceSimplicialSet incidence
        (faceCarrierNegative incidence negative (smallSimplexShape incidence negative degree simplex)) where
  app _shape := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨point, _positive, contains⟩ := tuple.property
    obtain ⟨ray, negativeRay, original⟩ := imagePointIncidence_original incidence negative degree simplex point
    refine ⟨ray, ⟨negativeRay, ?_⟩, fun column => original _ (contains column)⟩
    intro chart member
    obtain ⟨vertex, positive, equal⟩ := Finset.mem_image.mp member
    exact original chart ⟨vertex,
      commonPositiveVertices_support incidence negative _ simplex.val point positive, equal⟩⟩
  naturality {source target} selection := by apply ConcreteCategory.hom_ext; intro tuple; rfl

theorem imageCarrierClosedStarInclusion_comp (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) :
    SSet.chainComplexMap (imageCarrierClosedStarInclusion incidence negative degree simplex)
      (AddCommGrpCat.of ℤ) ≫
        faceCarrierChainInclusion incidence negative (smallSimplexShape incidence negative degree simplex) =
      imageCarrierChainInclusion incidence negative degree simplex := by
  apply HomologicalComplex.Hom.ext
  funext component
  apply SSet.chainComplex_hom_ext
  intro tuple
  change _ ≫ ((SSet.chainComplexMap _ _).f component ≫ _) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, faceCarrierChainInclusion,
    SSet.ι_chainComplexMap_f, imageCarrierChainInclusion, SSet.ι_chainComplexMap_f]
  congr 1

noncomputable def imageSmallIncidenceMap_closedStarCarried :
    (smallSingularIncidenceCarrier incidence negative).CarriedIntegralChainMap
      (imageSmallIncidenceMap incidence negative) where
  value degree simplex := (imageSmallIncidenceMap_carried incidence negative).value degree simplex ≫
    (SSet.chainComplexMap (imageCarrierClosedStarInclusion incidence negative degree simplex)
      (AddCommGrpCat.of ℤ)).f degree
  value_inclusion degree simplex := by
    rw [Category.assoc]
    change _ ≫ (SSet.chainComplexMap _ _ ≫ faceCarrierChainInclusion _ _ _).f degree = _
    rw [imageCarrierClosedStarInclusion_comp]
    exact (imageSmallIncidenceMap_carried incidence negative).value_inclusion degree simplex

theorem imageSmallIncidenceMap_augmentation :
    (imageSmallIncidenceMap incidence negative).f 0 ≫ incidenceChainAugmentation incidence negative =
      smallSingularChainAugmentation incidence negative := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc]
  rw [← (imageSmallIncidenceMap_carried incidence negative).value_inclusion 0 simplex]
  change imageCarrierVertexValues incidence negative simplex ≫
    ((imageIncidenceCarrier incidence negative).inclusion 0 simplex).f 0 ≫
      incidenceChainAugmentation incidence negative = _
  exact (imageCarrierVertexValues_augmentation incidence negative simplex).trans
    (smallSingularChainAugmentation_generator incidence negative simplex).symm

noncomputable def imageSmallIncidenceMapHomotopy :
    Homotopy (imageSmallIncidenceMap incidence negative) (smallSingularIncidenceMap incidence negative) :=
  (smallSingularIncidenceCarrier incidence negative).carriedMapsHomotopy
    (imageSmallIncidenceMap_closedStarCarried incidence negative)
    (smallSingularIncidenceMap_carried incidence negative) (by
      rw [imageSmallIncidenceMap_augmentation]
      exact (smallSingularIncidenceMapOfChoice_augmentation incidence negative _).symm)

end ImageCarriers

section FaceRealizations

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

def simplexFaceIncidence (face : Finset Chart) (_point : Unit) (chart : Chart) : Prop := chart ∈ face

noncomputable def simplexFaceVertex (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative)
    (vertex : ActiveIndex (incidencePatches (simplexFaceIncidence face) (fun _point => True))) :
    ActiveIndex (incidencePatches incidence negative) :=
  ⟨vertex.val, by
    obtain ⟨_point, _positive, member⟩ := vertex.property
    obtain ⟨_nonempty, ray, negativeRay, contains⟩ := present
    exact ⟨ray, negativeRay, contains vertex.val member⟩⟩

omit [Finite Chart] in
theorem simplexFaceVertex_injective (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    Function.Injective (simplexFaceVertex incidence negative face present) := by
  intro first second equal
  exact Subtype.ext (congrArg (fun vertex => vertex.val) equal)

noncomputable def simplexFaceRealizationInclusion (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    C(incidenceRealization (simplexFaceIncidence face) (fun _point => True),
      incidenceRealization incidence negative) where
  toFun point := simplexToRealization (activeNerve (incidencePatches incidence negative))
    ((realizationToSimplex _ point).map (simplexFaceVertex incidence negative face present)) (by
      change ((realizationToSimplex _ point).map (simplexFaceVertex incidence negative face present)).weights.support.image
        Subtype.val ∈ coverNerve (incidencePatches incidence negative)
      rw [incidencePatches_coverNerve]
      obtain ⟨_nonempty, ray, negativeRay, contains⟩ := present
      refine ⟨(Convexity.StdSimplex.support_weights_nonempty _).image _, ray, negativeRay, ?_⟩
      intro chart member
      obtain ⟨vertex, supported, equal⟩ := Finset.mem_image.mp member
      rw [Convexity.StdSimplex.weights_map] at supported
      obtain ⟨original, _supported, same⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support supported)
      obtain ⟨_point, _positive, onFace⟩ := original.property
      exact contains chart ((same ▸ equal) ▸ onFace))
  continuous_toFun := (continuous_into_realization_iff _ _).mpr fun vertex =>
    (continuous_apply vertex).comp
      ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous.comp
        ((Convexity.StdSimplex.continuous_map ℝ _).comp (realizationToSimplex _).continuous))

theorem simplexFaceRealizationInclusion_coordinate (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative)
    (point : incidenceRealization (simplexFaceIncidence face) (fun _point => True))
    (vertex : ActiveIndex (incidencePatches (simplexFaceIncidence face) (fun _point => True))) :
    (simplexFaceRealizationInclusion incidence negative face present point).val
      (simplexFaceVertex incidence negative face present vertex) = point.val vertex :=
  Finsupp.mapDomain_apply_of_injective (simplexFaceVertex_injective incidence negative face present) point.val vertex

theorem simplexFaceRealizationInclusion_support (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative)
    (point : incidenceRealization (simplexFaceIncidence face) (fun _point => True)) :
    (simplexFaceRealizationInclusion incidence negative face present point).val.support.image Subtype.val ⊆ face := by
  intro chart member
  obtain ⟨vertex, supported, equal⟩ := Finset.mem_image.mp member
  change vertex ∈ (Finsupp.mapDomain (simplexFaceVertex incidence negative face present) point.val).support at supported
  obtain ⟨original, _supported, same⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support supported)
  obtain ⟨_point, _positive, onFace⟩ := original.property
  exact (same ▸ equal) ▸ onFace

theorem simplexFaceRealizationInclusion_injective (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    Function.Injective (simplexFaceRealizationInclusion incidence negative face present) := by
  intro first second equal
  apply Subtype.ext
  ext vertex
  have coordinates := congrArg
    (fun point => point.val (simplexFaceVertex incidence negative face present vertex)) equal
  simpa only [simplexFaceRealizationInclusion_coordinate] using coordinates

noncomputable def simplexFaceSmallInclusion (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    openStarSmallSet (simplexFaceIncidence face) (fun _point => True) ⟶ openStarSmallSet incidence negative where
  app shape := ↾fun simplex => ⟨(TopCat.toSSet.map
    (TopCat.ofHom (simplexFaceRealizationInclusion incidence negative face present))).app shape simplex.val, by
      obtain ⟨vertex, positive⟩ := simplex.property
      refine ⟨simplexFaceVertex incidence negative face present vertex, fun point => ?_⟩
      change 0 < (simplexFaceRealizationInclusion incidence negative face present
        (singularSimplexMap (simplexFaceIncidence face) (fun _point => True) shape simplex.val point)).val
          (simplexFaceVertex incidence negative face present vertex)
      rw [simplexFaceRealizationInclusion_coordinate]
      exact positive point⟩
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro simplex
    apply Subtype.ext
    rfl

noncomputable def simplexFaceSmallChainInclusion (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    (openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) :=
  SSet.chainComplexMap (simplexFaceSmallInclusion incidence negative face present) (AddCommGrpCat.of ℤ)

theorem simplexFaceSmallChainInclusion_mono (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ) :
    Mono ((simplexFaceSmallChainInclusion incidence negative face present).f degree) := by
  let inclusion := simplexFaceSmallInclusion incidence negative face present
  have componentMono (shape : SimplexCategoryᵒᵖ) : Mono (inclusion.app shape) := by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro first second equal
    apply Subtype.ext
    apply (TopCat.toSSetObjEquiv _ shape).injective
    apply ContinuousMap.ext
    intro point
    apply simplexFaceRealizationInclusion_injective incidence negative face present
    exact congrArg
      (fun simplex => singularSimplexMap incidence negative shape simplex.val point) equal
  let : Mono inclusion := NatTrans.mono_of_mono_app inclusion
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of inclusion).hom (AddCommGrpCat.of ℤ)).f degree))

theorem simplexFaceSmallChainInclusion_augmentation (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    (simplexFaceSmallChainInclusion incidence negative face present).f 0 ≫
      smallSingularChainAugmentation incidence negative =
        smallSingularChainAugmentation (simplexFaceIncidence face) (fun _point => True) := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, simplexFaceSmallChainInclusion, SSet.ι_chainComplexMap_f]
  exact (smallSingularChainAugmentation_generator _ _ _).trans
    (smallSingularChainAugmentation_generator _ _ _).symm

omit [Finite Chart] in
theorem simplexFace_isCone (face : Finset Chart) (anchor : Chart) (member : anchor ∈ face) :
    PreAbstractSimplicialComplex.IsCone
      (negativeChartComplex (simplexFaceIncidence face) (fun _point => True)) anchor where
  apex_mem := ⟨Finset.singleton_nonempty _, (), trivial,
    fun chart onSingleton => (Finset.mem_singleton.mp onSingleton) ▸ member⟩
  insert_mem := by
    intro support supported
    obtain ⟨_nonempty, _point, _positive, contains⟩ := supported
    exact ⟨Finset.insert_nonempty _ _, (), trivial, fun chart onInsert =>
      (Finset.mem_insert.mp onInsert).elim (fun equal => equal ▸ member) (contains chart)⟩

noncomputable def simplexFaceSmallAugmentationEquiv (face : Finset Chart) (nonempty : face.Nonempty) :
    HomotopyEquiv
      ((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex (AddCommGrpCat.of ℤ))
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject) := by
  letI := incidenceCone_realization_contractible (simplexFaceIncidence face) (fun _point => True)
    nonempty.choose (simplexFace_isCone face nonempty.choose nonempty.choose_spec)
  exact (smallSingularChainHomotopyEquiv (simplexFaceIncidence face) (fun _point => True)).trans
    (contractibleSingularChainAugmentationHomotopyEquiv _)

theorem simplexFaceSmallAugmentationEquiv_zero (face : Finset Chart) (nonempty : face.Nonempty) :
    (simplexFaceSmallAugmentationEquiv face nonempty).hom.f 0 =
      smallSingularChainAugmentation (simplexFaceIncidence face) (fun _point => True) := by
  let := incidenceCone_realization_contractible (simplexFaceIncidence face) (fun _point => True)
    nonempty.choose (simplexFace_isCone face nonempty.choose nonempty.choose_spec)
  change ((smallSingularChainHomotopyEquiv (simplexFaceIncidence face) (fun _point => True)).hom ≫
    (contractibleSingularChainAugmentationHomotopyEquiv
      (incidenceRealization (simplexFaceIncidence face) (fun _point => True))).hom).f 0 = _
  rw [smallSingularChainHomotopyEquiv_hom, contractibleSingularChainAugmentationHomotopyEquiv_hom]
  exact smallSingularChainInclusion_augmentation _ _

theorem simplexFaceSmall_exactAt_positive (face : Finset Chart) (nonempty : face.Nonempty) (degree : ℕ) :
    ((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex
      (AddCommGrpCat.of ℤ)).ExactAt (degree + 1) := by
  have zeroTerm : IsZero
      (((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject).X (degree + 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact (HomologicalComplex.ExactAt.of_isZero zeroTerm).isZero_homology.of_iso
    ((simplexFaceSmallAugmentationEquiv face nonempty).toHomologyIso (degree + 1))

theorem simplexFaceSmall_augmentedExact (face : Finset Chart) (nonempty : face.Nonempty) :
    (ShortComplex.mk
      (((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex
        (AddCommGrpCat.of ℤ)).d 1 0)
      (smallSingularChainAugmentation (simplexFaceIncidence face) (fun _point => True))
      (by rw [← smallSingularChainInclusion_augmentation, ← Category.assoc,
        ← (smallSingularChainInclusion _ _).comm, Category.assoc, singularChainAugmentation_zero, comp_zero])).Exact := by
  let equivalence := simplexFaceSmallAugmentationEquiv face nonempty
  apply (ShortComplex.ab_exact_iff _).mpr
  intro cycle closed
  refine ⟨-equivalence.homotopyHomInvId.hom 0 1 cycle, ?_⟩
  have identity := ConcreteCategory.congr_hom (equivalence.homotopyHomInvId.comm 0) cycle
  rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex] at identity
  change (equivalence.hom.f 0 ≫ equivalence.inv.f 0) cycle =
    ((equivalence.homotopyHomInvId.hom 0 1 ≫
      ((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex
        (AddCommGrpCat.of ℤ)).d 1 0) +
      𝟙 (((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex
        (AddCommGrpCat.of ℤ)).X 0)) cycle at identity
  have canonical : equivalence.hom.f 0 = smallSingularChainAugmentation
      (simplexFaceIncidence face) (fun _point => True) := simplexFaceSmallAugmentationEquiv_zero face nonempty
  rw [canonical] at identity
  change (smallSingularChainAugmentation (simplexFaceIncidence face) (fun _point => True)) cycle = 0 at closed
  change (equivalence.inv.f 0).hom
    ((smallSingularChainAugmentation (simplexFaceIncidence face) (fun _point => True)).hom cycle) =
      ((equivalence.homotopyHomInvId.hom 0 1 ≫
        ((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex
          (AddCommGrpCat.of ℤ)).d 1 0) +
        𝟙 (((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex
          (AddCommGrpCat.of ℤ)).X 0)) cycle at identity
  rw [closed, map_zero] at identity
  have sumZero :
      ((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex
        (AddCommGrpCat.of ℤ)).d 1 0 (equivalence.homotopyHomInvId.hom 0 1 cycle) + cycle = 0 := by
    simpa only [AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.id_apply, closed, map_zero] using identity.symm
  simpa only [AddCommGrpCat.hom_neg_apply, map_neg, neg_neg] using
    congrArg Neg.neg (eq_neg_of_add_eq_zero_left sumZero)

end FaceRealizations

section GlobalFaceCarriers

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable def tupleFace (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) : Finset Chart :=
  Finset.univ.image tuple.val

omit [Finite Chart] in
theorem tupleFace_present (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    tupleFace incidence negative degree tuple ∈ negativeChartComplex incidence negative :=
  (tupleForbidden_iff_face incidence negative degree tuple.val).mp tuple.property

omit [Finite Chart] in
theorem tupleFace_face (degree : ℕ) (deleted : Fin (degree + 2))
    (tuple : forbiddenTuple incidence negative (degree + 1)) :
    tupleFace incidence negative degree ((incidenceSimplicialSet incidence negative).δ deleted tuple) ⊆
      tupleFace incidence negative (degree + 1) tuple := by
  intro chart member
  obtain ⟨column, _member, equal⟩ := Finset.mem_image.mp member
  exact Finset.mem_image.mpr ⟨deleted.succAbove column, Finset.mem_univ _, equal⟩

noncomputable def simplexFaceRefinement (smaller larger : Finset Chart) (nonempty : smaller.Nonempty)
    (subset : smaller ⊆ larger) :
    C(incidenceRealization (simplexFaceIncidence smaller) (fun _point => True),
      incidenceRealization (simplexFaceIncidence larger) (fun _point => True)) :=
  simplexFaceRealizationInclusion (simplexFaceIncidence larger) (fun _point => True) smaller
    ⟨nonempty, (), trivial, fun _chart member => subset member⟩

noncomputable def simplexFaceSmallRefinement (smaller larger : Finset Chart) (nonempty : smaller.Nonempty)
    (subset : smaller ⊆ larger) :
    openStarSmallSet (simplexFaceIncidence smaller) (fun _point => True) ⟶
      openStarSmallSet (simplexFaceIncidence larger) (fun _point => True) :=
  simplexFaceSmallInclusion (simplexFaceIncidence larger) (fun _point => True) smaller
    ⟨nonempty, (), trivial, fun _chart member => subset member⟩

theorem simplexFaceRefinement_inclusion (smaller larger : Finset Chart)
    (smallerPresent : smaller ∈ negativeChartComplex incidence negative)
    (largerPresent : larger ∈ negativeChartComplex incidence negative) (subset : smaller ⊆ larger) :
    (simplexFaceRealizationInclusion incidence negative larger largerPresent).comp
      (simplexFaceRefinement smaller larger smallerPresent.1 subset) =
        simplexFaceRealizationInclusion incidence negative smaller smallerPresent := by
  apply ContinuousMap.ext
  intro point
  apply Subtype.ext
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ point.val) = Finsupp.mapDomain _ point.val
  rw [← Finsupp.mapDomain_comp]
  congr 1

theorem simplexFaceSmallRefinement_inclusion (smaller larger : Finset Chart)
    (smallerPresent : smaller ∈ negativeChartComplex incidence negative)
    (largerPresent : larger ∈ negativeChartComplex incidence negative) (subset : smaller ⊆ larger) :
    SSet.chainComplexMap (simplexFaceSmallRefinement smaller larger smallerPresent.1 subset)
      (AddCommGrpCat.of ℤ) ≫ simplexFaceSmallChainInclusion incidence negative larger largerPresent =
        simplexFaceSmallChainInclusion incidence negative smaller smallerPresent := by
  apply HomologicalComplex.Hom.ext
  funext component
  apply SSet.chainComplex_hom_ext
  intro simplex
  change _ ≫ ((SSet.chainComplexMap _ _).f component ≫ _) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, simplexFaceSmallChainInclusion,
    SSet.ι_chainComplexMap_f, simplexFaceSmallChainInclusion, SSet.ι_chainComplexMap_f]
  congr 1
  apply Subtype.ext
  apply (TopCat.toSSetObjEquiv _ (.op ⦋component⦌)).injective
  apply ContinuousMap.ext
  intro point
  exact congrArg (fun mapping => mapping
    (singularSimplexMap (simplexFaceIncidence smaller) (fun _point => True) (.op ⦋component⦌) simplex.val point))
      (simplexFaceRefinement_inclusion incidence negative smaller larger smallerPresent largerPresent subset)

noncomputable def tupleSmallFaceCarrier :
    IntegralAcyclicCarrier (incidenceSimplicialSet incidence negative)
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ))
      (smallSingularChainAugmentation incidence negative) where
  complex degree tuple := (openStarSmallSet (simplexFaceIncidence (tupleFace incidence negative degree tuple))
    (fun _point => True)).chainComplex (AddCommGrpCat.of ℤ)
  inclusion degree tuple := simplexFaceSmallChainInclusion incidence negative _
    (tupleFace_present incidence negative degree tuple)
  inclusion_mono degree tuple component := simplexFaceSmallChainInclusion_mono incidence negative _ _ component
  faceMap degree deleted tuple := SSet.chainComplexMap
    (simplexFaceSmallRefinement _ _ (tupleFace_present incidence negative degree
      ((incidenceSimplicialSet incidence negative).δ deleted tuple)).1
      (tupleFace_face incidence negative degree deleted tuple)) (AddCommGrpCat.of ℤ)
  faceMap_inclusion degree deleted tuple := simplexFaceSmallRefinement_inclusion incidence negative _ _ _ _ _
  augmentation_zero degree tuple := by
    rw [simplexFaceSmallChainInclusion_augmentation, ← smallSingularChainInclusion_augmentation,
      ← Category.assoc, ← (smallSingularChainInclusion _ _).comm, Category.assoc,
      singularChainAugmentation_zero, comp_zero]
  exact_zero degree tuple := by
    simpa only [simplexFaceSmallChainInclusion_augmentation] using
      simplexFaceSmall_augmentedExact _ (tupleFace_present incidence negative degree tuple).1
  exact_positive degree tuple component := simplexFaceSmall_exactAt_positive _
    (tupleFace_present incidence negative degree tuple).1 component

noncomputable def tupleFaceSmallVertex (tuple : forbiddenTuple incidence negative 0) :
    (openStarSmallSet (simplexFaceIncidence (tupleFace incidence negative 0 tuple)) (fun _point => True)) _⦋0⦌ :=
  let vertex : ActiveIndex (incidencePatches (simplexFaceIncidence (tupleFace incidence negative 0 tuple))
      (fun _point => True)) :=
    ⟨tuple.val 0, (), trivial, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  ⟨(TopCat.toSSetObjEquiv _ (.op ⦋0⦌)).symm
    (ContinuousMap.const _ (AbstractSimplicialComplex.vertex _ vertex)),
    vertex, fun point => by
      change 0 < (Finsupp.single vertex (1 : ℝ)) vertex
      simp⟩

noncomputable def tupleSmallVertexValues :
    (tupleSmallFaceCarrier incidence negative).CarrierMapValues 0 :=
  fun tuple => (openStarSmallSet (simplexFaceIncidence (tupleFace incidence negative 0 tuple))
    (fun _point => True)).ιChainComplex (R := AddCommGrpCat.of ℤ) (tupleFaceSmallVertex incidence negative tuple)

theorem tupleSmallVertexValues_augmentation (tuple : forbiddenTuple incidence negative 0) :
    tupleSmallVertexValues incidence negative tuple ≫
      ((tupleSmallFaceCarrier incidence negative).inclusion 0 tuple).f 0 ≫
        smallSingularChainAugmentation incidence negative =
      Sigma.ι (fun _point : Unit => AddCommGrpCat.of ℤ) () := by
  change tupleSmallVertexValues incidence negative tuple ≫
    (simplexFaceSmallChainInclusion incidence negative _ (tupleFace_present incidence negative 0 tuple)).f 0 ≫
      smallSingularChainAugmentation incidence negative = _
  rw [simplexFaceSmallChainInclusion_augmentation]
  exact smallSingularChainAugmentation_generator _ _ _

theorem tupleSmallVertexValues_compatible :
    ∀ tuple : forbiddenTuple incidence negative 1,
      tupleSmallVertexValues incidence negative ((incidenceSimplicialSet incidence negative).δ 0 tuple) ≫
        ((tupleSmallFaceCarrier incidence negative).inclusion 0
          ((incidenceSimplicialSet incidence negative).δ 0 tuple)).f 0 ≫
            smallSingularChainAugmentation incidence negative =
      tupleSmallVertexValues incidence negative ((incidenceSimplicialSet incidence negative).δ 1 tuple) ≫
        ((tupleSmallFaceCarrier incidence negative).inclusion 0
          ((incidenceSimplicialSet incidence negative).δ 1 tuple)).f 0 ≫
            smallSingularChainAugmentation incidence negative := by
  intro tuple
  rw [tupleSmallVertexValues_augmentation, tupleSmallVertexValues_augmentation]

noncomputable def facePreservingIncidenceSmallMap :
    incidenceChains incidence negative ⟶
      (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) :=
  (tupleSmallFaceCarrier incidence negative).extendCarriedVertexMap
    (tupleSmallVertexValues incidence negative) (tupleSmallVertexValues_compatible incidence negative)

noncomputable def facePreservingIncidenceSmallMap_carried :
    (tupleSmallFaceCarrier incidence negative).CarriedIntegralChainMap
      (facePreservingIncidenceSmallMap incidence negative) :=
  (tupleSmallFaceCarrier incidence negative).extendCarriedVertexMap_carried
    (tupleSmallVertexValues incidence negative) (tupleSmallVertexValues_compatible incidence negative)

theorem facePreservingIncidenceSmallMap_augmentation :
    (facePreservingIncidenceSmallMap incidence negative).f 0 ≫
      smallSingularChainAugmentation incidence negative = incidenceChainAugmentation incidence negative := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  rw [← Category.assoc, ← (facePreservingIncidenceSmallMap_carried incidence negative).value_inclusion 0 tuple]
  exact (tupleSmallVertexValues_augmentation incidence negative tuple).trans
    (incidenceChainAugmentation_generator incidence negative tuple).symm

noncomputable def simplexFaceSingularChainInclusion (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    integralSingularChains (incidenceRealization (simplexFaceIncidence face) (fun _point => True)) ⟶
      integralSingularChains (incidenceRealization incidence negative) :=
  SSet.chainComplexMap (TopCat.toSSet.map
    (TopCat.ofHom (simplexFaceRealizationInclusion incidence negative face present))) (AddCommGrpCat.of ℤ)

theorem simplexFaceSingularChainInclusion_mono (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ) :
    Mono ((simplexFaceSingularChainInclusion incidence negative face present).f degree) := by
  let inclusion := TopCat.toSSet.map (TopCat.ofHom (simplexFaceRealizationInclusion incidence negative face present))
  have componentMono (shape : SimplexCategoryᵒᵖ) : Mono (inclusion.app shape) := by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro first second equal
    apply (TopCat.toSSetObjEquiv _ shape).injective
    apply ContinuousMap.ext
    intro point
    apply simplexFaceRealizationInclusion_injective incidence negative face present
    exact congrArg (fun simplex => singularSimplexMap incidence negative shape simplex point) equal
  let : Mono inclusion := NatTrans.mono_of_mono_app inclusion
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of inclusion).hom (AddCommGrpCat.of ℤ)).f degree))

theorem simplexFaceSmallSingular_square (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    smallSingularChainInclusion (simplexFaceIncidence face) (fun _point => True) ≫
      simplexFaceSingularChainInclusion incidence negative face present =
    simplexFaceSmallChainInclusion incidence negative face present ≫ smallSingularChainInclusion incidence negative := by
  apply HomologicalComplex.Hom.ext
  funext degree
  apply SSet.chainComplex_hom_ext
  intro simplex
  simp only [HomologicalComplex.comp_f, ← Category.assoc, smallSingularChainInclusion,
    simplexFaceSingularChainInclusion, simplexFaceSmallChainInclusion, SSet.ι_chainComplexMap_f]
  congr 1

noncomputable def tupleSingularFaceCarrier :
    IntegralAcyclicCarrier (incidenceSimplicialSet incidence negative)
      (integralSingularChains (incidenceRealization incidence negative))
      (singularChainAugmentation (incidenceRealization incidence negative)) where
  complex degree tuple := integralSingularChains
    (incidenceRealization (simplexFaceIncidence (tupleFace incidence negative degree tuple)) (fun _point => True))
  inclusion degree tuple := simplexFaceSingularChainInclusion incidence negative _
    (tupleFace_present incidence negative degree tuple)
  inclusion_mono degree tuple component := simplexFaceSingularChainInclusion_mono incidence negative _ _ component
  faceMap degree deleted tuple := SSet.chainComplexMap (TopCat.toSSet.map
    (TopCat.ofHom (simplexFaceRefinement _ _ (tupleFace_present incidence negative degree
      ((incidenceSimplicialSet incidence negative).δ deleted tuple)).1
      (tupleFace_face incidence negative degree deleted tuple)))) (AddCommGrpCat.of ℤ)
  faceMap_inclusion degree deleted tuple := by
    change ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of ℤ)).map _ ≫
        ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map _ = _
    rw [← Functor.map_comp]
    change ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom ((simplexFaceRealizationInclusion incidence negative _
        (tupleFace_present incidence negative (degree + 1) tuple)).comp
        (simplexFaceRefinement _ _ (tupleFace_present incidence negative degree
          ((incidenceSimplicialSet incidence negative).δ deleted tuple)).1
          (tupleFace_face incidence negative degree deleted tuple)))) = _
    exact congrArg
      (fun mapping => ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom mapping))
      (simplexFaceRefinement_inclusion incidence negative _ _
        (tupleFace_present incidence negative degree ((incidenceSimplicialSet incidence negative).δ deleted tuple))
        (tupleFace_present incidence negative (degree + 1) tuple)
        (tupleFace_face incidence negative degree deleted tuple))
  augmentation_zero degree tuple := by
    rw [simplexFaceSingularChainInclusion, singularChainAugmentation_naturality]
    exact singularChainAugmentation_zero _
  exact_zero degree tuple := by
    simp only [simplexFaceSingularChainInclusion, singularChainAugmentation_naturality]
    let present := tupleFace_present incidence negative degree tuple
    let := incidenceCone_realization_contractible _ _ present.1.choose
      (simplexFace_isCone _ present.1.choose present.1.choose_spec)
    exact contractibleSingularChains_augmentedExact _
  exact_positive degree tuple component := by
    let present := tupleFace_present incidence negative degree tuple
    let := incidenceCone_realization_contractible _ _ present.1.choose
      (simplexFace_isCone _ present.1.choose present.1.choose_spec)
    exact contractibleSingularChains_exactAt_positive _ component

noncomputable def facePreservingIncidenceSingularMap_carried :
    (tupleSingularFaceCarrier incidence negative).CarriedIntegralChainMap
      (facePreservingIncidenceSmallMap incidence negative ≫ smallSingularChainInclusion incidence negative) where
  value degree tuple := (facePreservingIncidenceSmallMap_carried incidence negative).value degree tuple ≫
    (smallSingularChainInclusion (simplexFaceIncidence (tupleFace incidence negative degree tuple))
      (fun _point => True)).f degree
  value_inclusion degree tuple := by
    rw [Category.assoc]
    change _ ≫ (smallSingularChainInclusion _ _ ≫ simplexFaceSingularChainInclusion _ _ _ _).f degree = _
    rw [simplexFaceSmallSingular_square]
    rw [HomologicalComplex.comp_f, ← Category.assoc]
    exact congrArg (fun mapping => mapping ≫ (smallSingularChainInclusion incidence negative).f degree)
      ((facePreservingIncidenceSmallMap_carried incidence negative).value_inclusion degree tuple)

noncomputable def tupleInOwnFace (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    forbiddenTuple (simplexFaceIncidence (tupleFace incidence negative degree tuple)) (fun _point => True) degree :=
  ⟨tuple.val, (), trivial, fun column => Finset.mem_image.mpr ⟨column, Finset.mem_univ _, rfl⟩⟩

theorem tupleAffineSimplex_faceInclusion (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    (simplexFaceRealizationInclusion incidence negative _ (tupleFace_present incidence negative degree tuple)).comp
      (tupleAffineSimplex (simplexFaceIncidence (tupleFace incidence negative degree tuple)) (fun _point => True)
        degree (tupleInOwnFace incidence negative degree tuple)) = tupleAffineSimplex incidence negative degree tuple := by
  apply ContinuousMap.ext
  intro point
  apply Subtype.ext
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ point.weights) = Finsupp.mapDomain _ point.weights
  rw [← Finsupp.mapDomain_comp]
  congr 1

noncomputable def affineSingularChainMap_faceCarried :
    (tupleSingularFaceCarrier incidence negative).CarriedIntegralChainMap (affineSingularChainMap incidence negative) where
  value degree tuple := (incidenceSingularSet (simplexFaceIncidence (tupleFace incidence negative degree tuple))
    (fun _point => True)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      (tupleSingularSimplex _ _ degree (tupleInOwnFace incidence negative degree tuple))
  value_inclusion degree tuple := by
    change _ ≫ (SSet.chainComplexMap _ _).f degree = _
    rw [SSet.ι_chainComplexMap_f, affineSingularChainMap, SSet.ι_chainComplexMap_f]
    congr 1
    apply (TopCat.toSSetObjEquiv _ (.op ⦋degree⦌)).injective
    exact tupleAffineSimplex_faceInclusion incidence negative degree tuple

noncomputable def facePreservingIncidenceSmallMapHomotopy :
    Homotopy (facePreservingIncidenceSmallMap incidence negative ≫ smallSingularChainInclusion incidence negative)
      (affineSingularChainMap incidence negative) :=
  (tupleSingularFaceCarrier incidence negative).carriedMapsHomotopy
    (facePreservingIncidenceSingularMap_carried incidence negative)
    (affineSingularChainMap_faceCarried incidence negative) (by
      rw [HomologicalComplex.comp_f, Category.assoc, smallSingularChainInclusion_augmentation,
        facePreservingIncidenceSmallMap_augmentation, affineSingularChainMap_augmentation])

noncomputable def simplexFaceIncidenceInclusion (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    incidenceSimplicialSet (simplexFaceIncidence face) (fun _point => True) ⟶ incidenceSimplicialSet incidence negative where
  app _shape := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨ray, negativeRay, contains⟩ := present.2
    exact ⟨ray, negativeRay, fun column => contains _ (tuple.property.choose_spec.2 column)⟩⟩
  naturality {source target} selection := by apply ConcreteCategory.hom_ext; intro tuple; rfl

noncomputable def simplexFaceIncidenceChainInclusion (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    incidenceChains (simplexFaceIncidence face) (fun _point => True) ⟶ incidenceChains incidence negative :=
  SSet.chainComplexMap (simplexFaceIncidenceInclusion incidence negative face present) (AddCommGrpCat.of ℤ)

omit [Finite Chart] in
theorem simplexFaceIncidenceChainInclusion_mono (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ) :
    Mono ((simplexFaceIncidenceChainInclusion incidence negative face present).f degree) := by
  let inclusion := simplexFaceIncidenceInclusion incidence negative face present
  have componentMono (shape : SimplexCategoryᵒᵖ) : Mono (inclusion.app shape) := by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro first second equal
    exact Subtype.ext (congrArg (fun tuple => tuple.val) equal)
  let : Mono inclusion := NatTrans.mono_of_mono_app inclusion
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of inclusion).hom (AddCommGrpCat.of ℤ)).f degree))

omit [Finite Chart] in
theorem simplexFaceIncidenceChainInclusion_augmentation (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    (simplexFaceIncidenceChainInclusion incidence negative face present).f 0 ≫
      incidenceChainAugmentation incidence negative =
        incidenceChainAugmentation (simplexFaceIncidence face) (fun _point => True) := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  rw [← Category.assoc, simplexFaceIncidenceChainInclusion, SSet.ι_chainComplexMap_f]
  exact (incidenceChainAugmentation_generator _ _ _).trans
    (incidenceChainAugmentation_generator _ _ _).symm

noncomputable def simplexFaceIncidenceRefinement (smaller larger : Finset Chart) (subset : smaller ⊆ larger) :
    incidenceSimplicialSet (simplexFaceIncidence smaller) (fun _point => True) ⟶
      incidenceSimplicialSet (simplexFaceIncidence larger) (fun _point => True) where
  app _shape := ↾fun tuple => ⟨tuple.val, (), trivial,
    fun column => subset (tuple.property.choose_spec.2 column)⟩
  naturality {source target} selection := by apply ConcreteCategory.hom_ext; intro tuple; rfl

omit [Finite Chart] in
theorem simplexFaceIncidenceRefinement_inclusion (smaller larger : Finset Chart)
    (smallerPresent : smaller ∈ negativeChartComplex incidence negative)
    (largerPresent : larger ∈ negativeChartComplex incidence negative) (subset : smaller ⊆ larger) :
    SSet.chainComplexMap (simplexFaceIncidenceRefinement smaller larger subset) (AddCommGrpCat.of ℤ) ≫
      simplexFaceIncidenceChainInclusion incidence negative larger largerPresent =
        simplexFaceIncidenceChainInclusion incidence negative smaller smallerPresent := by
  apply HomologicalComplex.Hom.ext
  funext component
  apply SSet.chainComplex_hom_ext
  intro tuple
  change _ ≫ ((SSet.chainComplexMap _ _).f component ≫ _) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, simplexFaceIncidenceChainInclusion,
    SSet.ι_chainComplexMap_f, simplexFaceIncidenceChainInclusion, SSet.ι_chainComplexMap_f]
  congr 1

noncomputable def tupleIncidenceFaceCarrier :
    IntegralAcyclicCarrier (incidenceSimplicialSet incidence negative)
      (incidenceChains incidence negative) (incidenceChainAugmentation incidence negative) where
  complex degree tuple := incidenceChains (simplexFaceIncidence (tupleFace incidence negative degree tuple))
    (fun _point => True)
  inclusion degree tuple := simplexFaceIncidenceChainInclusion incidence negative _
    (tupleFace_present incidence negative degree tuple)
  inclusion_mono degree tuple component := simplexFaceIncidenceChainInclusion_mono incidence negative _ _ component
  faceMap degree deleted tuple := SSet.chainComplexMap (simplexFaceIncidenceRefinement _ _
    (tupleFace_face incidence negative degree deleted tuple)) (AddCommGrpCat.of ℤ)
  faceMap_inclusion degree deleted tuple := simplexFaceIncidenceRefinement_inclusion incidence negative _ _ _ _ _
  augmentation_zero degree tuple := by
    rw [simplexFaceIncidenceChainInclusion_augmentation, incidenceChainAugmentation_zero]
  exact_zero degree tuple := by
    simp only [simplexFaceIncidenceChainInclusion_augmentation]
    let present := tupleFace_present incidence negative degree tuple
    exact incidenceConeChains_augmentedExact _ _ present.1.choose
      (simplexFace_isCone _ present.1.choose present.1.choose_spec)
  exact_positive degree tuple component := by
    let present := tupleFace_present incidence negative degree tuple
    exact incidenceConeChains_exactAt_positive _ _ present.1.choose
      (simplexFace_isCone _ present.1.choose present.1.choose_spec) component

noncomputable def identityIncidenceMap_faceCarried :
    (tupleIncidenceFaceCarrier incidence negative).CarriedIntegralChainMap (𝟙 (incidenceChains incidence negative)) where
  value degree tuple := (incidenceSimplicialSet (simplexFaceIncidence (tupleFace incidence negative degree tuple))
    (fun _point => True)).ιChainComplex (R := AddCommGrpCat.of ℤ) (tupleInOwnFace incidence negative degree tuple)
  value_inclusion degree tuple := by
    change _ ≫ (SSet.chainComplexMap _ _).f degree = _
    rw [SSet.ι_chainComplexMap_f, HomologicalComplex.id_f, Category.comp_id]
    congr 1

noncomputable def imageCarrierFaceInclusion (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ)
    (simplex : (openStarSmallSet (simplexFaceIncidence face) (fun _point => True)) _⦋degree⦌) :
    incidenceSimplicialSet
      (imagePointIncidence incidence negative degree
        ((simplexFaceSmallInclusion incidence negative face present).app (.op ⦋degree⦌) simplex))
      (fun _point => True) ⟶ incidenceSimplicialSet (simplexFaceIncidence face) (fun _point => True) where
  app _shape := ↾fun tuple => ⟨tuple.val, (), trivial, fun column => by
    obtain ⟨point, _positive, contains⟩ := tuple.property
    obtain ⟨vertex, supported, equal⟩ := contains column
    exact simplexFaceRealizationInclusion_support incidence negative face present
      (singularSimplexMap (simplexFaceIncidence face) (fun _point => True) (.op ⦋degree⦌) simplex.val point)
      (Finset.mem_image.mpr ⟨vertex, supported, equal⟩)⟩
  naturality {source target} selection := by apply ConcreteCategory.hom_ext; intro tuple; rfl

theorem imageCarrierFaceInclusion_comp (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ)
    (simplex : (openStarSmallSet (simplexFaceIncidence face) (fun _point => True)) _⦋degree⦌) :
    SSet.chainComplexMap (imageCarrierFaceInclusion incidence negative face present degree simplex)
      (AddCommGrpCat.of ℤ) ≫ simplexFaceIncidenceChainInclusion incidence negative face present =
    imageCarrierChainInclusion incidence negative degree
      ((simplexFaceSmallInclusion incidence negative face present).app (.op ⦋degree⦌) simplex) := by
  apply HomologicalComplex.Hom.ext
  funext component
  apply SSet.chainComplex_hom_ext
  intro tuple
  change _ ≫ ((SSet.chainComplexMap _ _).f component ≫ _) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, simplexFaceIncidenceChainInclusion,
    SSet.ι_chainComplexMap_f, imageCarrierChainInclusion, SSet.ι_chainComplexMap_f]
  congr 1

noncomputable def imageSmallIncidenceFaceComponent (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ) :
    ((openStarSmallSet (simplexFaceIncidence face) (fun _point => True)).chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶
      (incidenceChains (simplexFaceIncidence face) (fun _point => True)).X degree :=
  Sigma.desc fun simplex => (imageSmallIncidenceMap_carried incidence negative).value degree
    ((simplexFaceSmallInclusion incidence negative face present).app (.op ⦋degree⦌) simplex) ≫
      (SSet.chainComplexMap (imageCarrierFaceInclusion incidence negative face present degree simplex)
        (AddCommGrpCat.of ℤ)).f degree

theorem imageSmallIncidenceFaceComponent_inclusion (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ) :
    imageSmallIncidenceFaceComponent incidence negative face present degree ≫
      (simplexFaceIncidenceChainInclusion incidence negative face present).f degree =
    (simplexFaceSmallChainInclusion incidence negative face present).f degree ≫
      (imageSmallIncidenceMap incidence negative).f degree := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc]
  change Sigma.ι
    (fun _simplex : (openStarSmallSet (simplexFaceIncidence face) (fun _point => True)) _⦋degree⦌ =>
      AddCommGrpCat.of ℤ) simplex ≫ Sigma.desc _ ≫ _ = _
  rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc]
  change _ ≫ (SSet.chainComplexMap _ _ ≫ simplexFaceIncidenceChainInclusion _ _ _ _).f degree = _
  rw [imageCarrierFaceInclusion_comp]
  have carried := (imageSmallIncidenceMap_carried incidence negative).value_inclusion degree
    ((simplexFaceSmallInclusion incidence negative face present).app (.op ⦋degree⦌) simplex)
  exact carried.trans (by
    rw [← Category.assoc, simplexFaceSmallChainInclusion, SSet.ι_chainComplexMap_f])

noncomputable def facePreservingImageIncidenceMap_carried :
    (tupleIncidenceFaceCarrier incidence negative).CarriedIntegralChainMap
      (facePreservingIncidenceSmallMap incidence negative ≫ imageSmallIncidenceMap incidence negative) where
  value degree tuple := (facePreservingIncidenceSmallMap_carried incidence negative).value degree tuple ≫
    imageSmallIncidenceFaceComponent incidence negative _ (tupleFace_present incidence negative degree tuple) degree
  value_inclusion degree tuple := by
    rw [Category.assoc]
    change _ ≫ (imageSmallIncidenceFaceComponent incidence negative _
      (tupleFace_present incidence negative degree tuple) degree ≫
      (simplexFaceIncidenceChainInclusion incidence negative _
        (tupleFace_present incidence negative degree tuple)).f degree) = _
    rw [imageSmallIncidenceFaceComponent_inclusion, ← Category.assoc]
    exact congrArg (fun mapping => mapping ≫ (imageSmallIncidenceMap incidence negative).f degree)
      ((facePreservingIncidenceSmallMap_carried incidence negative).value_inclusion degree tuple)

noncomputable def incidenceFacePreservingImageHomotopy :
    Homotopy (facePreservingIncidenceSmallMap incidence negative ≫ imageSmallIncidenceMap incidence negative)
      (𝟙 (incidenceChains incidence negative)) :=
  (tupleIncidenceFaceCarrier incidence negative).carriedMapsHomotopy
    (facePreservingImageIncidenceMap_carried incidence negative)
    (identityIncidenceMap_faceCarried incidence negative) (by
      rw [HomologicalComplex.comp_f, Category.assoc, imageSmallIncidenceMap_augmentation,
        facePreservingIncidenceSmallMap_augmentation, HomologicalComplex.id_f, Category.id_comp])

end GlobalFaceCarriers

section ActualTwoSidedEquivalences

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable def imageSingularIncidenceChainMap :
    integralSingularChains (incidenceRealization incidence negative) ⟶ incidenceChains incidence negative :=
  singularSmallChainRetraction incidence negative ≫ imageSmallIncidenceMap incidence negative

noncomputable def affineImageSingularIncidenceHomotopy :
    Homotopy (affineSingularChainMap incidence negative ≫ imageSingularIncidenceChainMap incidence negative)
      (𝟙 (incidenceChains incidence negative)) := by
  have first := ((facePreservingIncidenceSmallMapHomotopy incidence negative).symm.compRight
    (singularSmallChainRetraction incidence negative)).compRight (imageSmallIncidenceMap incidence negative)
  have second := ((smallInclusionRetractionHomotopy incidence negative).compLeft
    (facePreservingIncidenceSmallMap incidence negative)).compRight (imageSmallIncidenceMap incidence negative)
  have firstNormalized : Homotopy
      (affineSingularChainMap incidence negative ≫ imageSingularIncidenceChainMap incidence negative)
      ((facePreservingIncidenceSmallMap incidence negative ≫ smallSingularChainInclusion incidence negative) ≫
        singularSmallChainRetraction incidence negative ≫ imageSmallIncidenceMap incidence negative) := by
    simpa only [imageSingularIncidenceChainMap, Category.assoc] using first
  have secondNormalized : Homotopy
      ((facePreservingIncidenceSmallMap incidence negative ≫ smallSingularChainInclusion incidence negative) ≫
        singularSmallChainRetraction incidence negative ≫ imageSmallIncidenceMap incidence negative)
      (facePreservingIncidenceSmallMap incidence negative ≫ imageSmallIncidenceMap incidence negative) := by
    simpa only [Category.assoc, Category.comp_id] using second
  exact firstNormalized.trans (secondNormalized.trans (incidenceFacePreservingImageHomotopy incidence negative))

noncomputable def imageSingularIncidenceChainMapHomotopy :
    Homotopy (imageSingularIncidenceChainMap incidence negative) (singularIncidenceChainMap incidence negative) :=
  (imageSmallIncidenceMapHomotopy incidence negative).compLeft (singularSmallChainRetraction incidence negative)

noncomputable def affineSingularIncidenceHomotopy :
    Homotopy (affineSingularChainMap incidence negative ≫ singularIncidenceChainMap incidence negative)
      (𝟙 (incidenceChains incidence negative)) :=
  ((imageSingularIncidenceChainMapHomotopy incidence negative).symm.compLeft
    (affineSingularChainMap incidence negative)).trans (affineImageSingularIncidenceHomotopy incidence negative)

noncomputable def canonicalIncidenceSingularChainHomotopyEquiv :
    HomotopyEquiv (incidenceChains incidence negative)
      (integralSingularChains (incidenceRealization incidence negative)) where
  hom := affineSingularChainMap incidence negative
  inv := singularIncidenceChainMap incidence negative
  homotopyHomInvId := affineSingularIncidenceHomotopy incidence negative
  homotopyInvHomId := singularIncidenceAffineHomotopy incidence negative

theorem canonicalIncidenceSingularChainHomotopyEquiv_hom :
    (canonicalIncidenceSingularChainHomotopyEquiv incidence negative).hom =
      affineSingularChainMap incidence negative := rfl

end ActualTwoSidedEquivalences

end BondalThomsen.ConvexNerveIncidenceSingularGlobalEquivalence
