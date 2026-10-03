module

public import BondalThomsen.Cohomology.ConvexNerve.AcyclicCarrierAssembly

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceHomologyComparison
open BondalThomsen.ConvexNerveAcyclicCarrierAssembly
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveSmallSingularComparison

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable abbrev incidenceSingularSet : SSet.{0} :=
  TopCat.toSSet.obj (TopCat.of (incidenceRealization incidence negative))

def realizationOpenStar (vertex : ActiveIndex (incidencePatches incidence negative)) :
    Set (incidenceRealization incidence negative) :=
  {point | 0 < point.val vertex}

omit [Finite Chart] in
theorem realizationOpenStar_isOpen
    (vertex : ActiveIndex (incidencePatches incidence negative)) :
    IsOpen (realizationOpenStar incidence negative vertex) := by
  exact isOpen_lt continuous_const
    ((continuous_apply vertex).comp
      (realizationCoordinates_continuous (activeNerve (incidencePatches incidence negative))))

omit [Finite Chart] in
theorem realizationOpenStar_cover (point : incidenceRealization incidence negative) :
    ∃ vertex, point ∈ realizationOpenStar incidence negative vertex := by
  obtain ⟨vertex, supported⟩ :=
    (activeNerve (incidencePatches incidence negative)).isRelLowerSet_faces.prop_of_mem
      (AbstractSimplicialComplex.support_mem _ point)
  refine ⟨vertex, lt_of_le_of_ne (AbstractSimplicialComplex.Realization.nonneg _ point vertex) ?_⟩
  exact (Finsupp.mem_support_iff.mp supported).symm

noncomputable def singularSimplexMap (simplex : SimplexCategoryᵒᵖ)
    (value : (incidenceSingularSet incidence negative).obj simplex) :
    C(Convexity.StdSimplex ℝ (Fin (simplex.unop.len + 1)),
      incidenceRealization incidence negative) :=
  TopCat.toSSetObjEquiv _ simplex value

omit [Finite Chart] in
theorem singularSimplexMap_precomp {source target : SimplexCategory}
    (selection : source ⟶ target)
    (value : (incidenceSingularSet incidence negative).obj (.op target))
    (point : Convexity.StdSimplex ℝ (Fin (source.len + 1))) :
    singularSimplexMap incidence negative (.op source)
      ((incidenceSingularSet incidence negative).map selection.op value) point =
    singularSimplexMap incidence negative (.op target) value
      (point.map selection.toOrderHom) := rfl

def IsOpenStarSmall (simplex : SimplexCategoryᵒᵖ)
    (value : (incidenceSingularSet incidence negative).obj simplex) : Prop :=
  ∃ vertex : ActiveIndex (incidencePatches incidence negative),
    ∀ point, 0 < (singularSimplexMap incidence negative simplex value point).val vertex

omit [Finite Chart] in
theorem isOpenStarSmall_precomp {source target : SimplexCategory}
    (selection : source ⟶ target)
    (value : (incidenceSingularSet incidence negative).obj (.op target))
    (small : IsOpenStarSmall incidence negative (.op target) value) :
    IsOpenStarSmall incidence negative (.op source)
      ((incidenceSingularSet incidence negative).map selection.op value) := by
  obtain ⟨vertex, positive⟩ := small
  exact ⟨vertex, fun point => positive (point.map selection.toOrderHom)⟩

noncomputable def openStarSmallSubcomplex :
    (incidenceSingularSet incidence negative).Subcomplex where
  obj simplex := {value | IsOpenStarSmall incidence negative simplex value}
  map selection value small :=
    isOpenStarSmall_precomp incidence negative selection.unop value small

noncomputable abbrev openStarSmallSet : SSet.{0} :=
  (openStarSmallSubcomplex incidence negative).toSSet

noncomputable def commonPositiveVertices (simplex : SimplexCategoryᵒᵖ)
    (value : (incidenceSingularSet incidence negative).obj simplex) :
    Finset (ActiveIndex (incidencePatches incidence negative)) :=
  (Fintype.ofFinite (ActiveIndex (incidencePatches incidence negative))).elems.filter
    (fun vertex => ∀ point,
      0 < (singularSimplexMap incidence negative simplex value point).val vertex)

theorem mem_commonPositiveVertices (simplex : SimplexCategoryᵒᵖ)
    (value : (incidenceSingularSet incidence negative).obj simplex)
    (vertex : ActiveIndex (incidencePatches incidence negative)) :
    vertex ∈ commonPositiveVertices incidence negative simplex value ↔
      ∀ point, 0 < (singularSimplexMap incidence negative simplex value point).val vertex := by
  let := Fintype.ofFinite (ActiveIndex (incidencePatches incidence negative))
  change vertex ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem commonPositiveVertices_nonempty (simplex : SimplexCategoryᵒᵖ)
    (value : (incidenceSingularSet incidence negative).obj simplex)
    (small : IsOpenStarSmall incidence negative simplex value) :
    (commonPositiveVertices incidence negative simplex value).Nonempty := by
  obtain ⟨vertex, positive⟩ := small
  exact ⟨vertex, (mem_commonPositiveVertices incidence negative simplex value vertex).mpr positive⟩

theorem commonPositiveVertices_precomp {source target : SimplexCategory}
    (selection : source ⟶ target)
    (value : (incidenceSingularSet incidence negative).obj (.op target)) :
    commonPositiveVertices incidence negative (.op target) value ⊆
      commonPositiveVertices incidence negative (.op source)
        ((incidenceSingularSet incidence negative).map selection.op value) := by
  intro vertex present
  rw [mem_commonPositiveVertices] at present ⊢
  exact fun point => present (point.map selection.toOrderHom)

theorem commonPositiveVertices_support (simplex : SimplexCategoryᵒᵖ)
    (value : (incidenceSingularSet incidence negative).obj simplex)
    (point : Convexity.StdSimplex ℝ (Fin (simplex.unop.len + 1))) :
    commonPositiveVertices incidence negative simplex value ⊆
      (singularSimplexMap incidence negative simplex value point).val.support := by
  intro vertex present
  apply Finsupp.mem_support_iff.mpr
  exact ne_of_gt ((mem_commonPositiveVertices incidence negative simplex value vertex).mp present point)

theorem commonPositiveVertices_face (simplex : SimplexCategoryᵒᵖ)
    (value : (incidenceSingularSet incidence negative).obj simplex)
    (small : IsOpenStarSmall incidence negative simplex value) :
    commonPositiveVertices incidence negative simplex value ∈
      activeNerve (incidencePatches incidence negative) := by
  exact (activeNerve (incidencePatches incidence negative)).isRelLowerSet_faces.mem_of_le
    (AbstractSimplicialComplex.support_mem _
      (singularSimplexMap incidence negative simplex value (Convexity.StdSimplex.single 0)))
    (commonPositiveVertices_support incidence negative simplex value _)
    (commonPositiveVertices_nonempty incidence negative simplex value small)

noncomputable def smallSimplexShape (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) : Finset Chart :=
  (commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val).image Subtype.val

theorem smallSimplexShape_present (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) :
    smallSimplexShape incidence negative degree simplex ∈ negativeChartComplex incidence negative := by
  have present := commonPositiveVertices_face incidence negative (.op ⦋degree⦌)
    simplex.val simplex.property
  change smallSimplexShape incidence negative degree simplex ∈
    BondalThomsen.ClosedConvexNerveComparison.coverNerve (incidencePatches incidence negative) at present
  rwa [incidencePatches_coverNerve] at present

theorem smallSimplexShape_face (degree : ℕ) (deleted : Fin (degree + 2))
    (simplex : (openStarSmallSet incidence negative) _⦋degree + 1⦌) :
    smallSimplexShape incidence negative (degree + 1) simplex ⊆
      smallSimplexShape incidence negative degree
        ((openStarSmallSet incidence negative).δ deleted simplex) :=
  Finset.image_subset_image
    (commonPositiveVertices_precomp incidence negative (SimplexCategory.δ deleted) simplex.val)

noncomputable def smallSingularIncidenceCarrier :
    IntegralAcyclicCarrier (openStarSmallSet incidence negative)
      (incidenceChains incidence negative) (incidenceChainAugmentation incidence negative) :=
  reverseFaceCarrier incidence negative (openStarSmallSet incidence negative)
    (smallSimplexShape incidence negative) (smallSimplexShape_face incidence negative)
    (smallSimplexShape_present incidence negative)

noncomputable def smallSingularChainInclusion :
    (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) ⟶
      integralSingularChains (incidenceRealization incidence negative) :=
  SSet.chainComplexMap (openStarSmallSubcomplex incidence negative).ι (AddCommGrpCat.of ℤ)

omit [Finite Chart] in
theorem smallSingularChainInclusion_mono (degree : ℕ) :
    Mono ((smallSingularChainInclusion incidence negative).f degree) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap
    (SSetPair.of (openStarSmallSubcomplex incidence negative).ι).hom
    (AddCommGrpCat.of ℤ)).f degree))

noncomputable def smallVertexChoice
    (simplex : (openStarSmallSet incidence negative) _⦋0⦌) : Chart :=
  (smallSimplexShape_present incidence negative 0 simplex).1.choose

theorem smallVertexChoice_mem
    (simplex : (openStarSmallSet incidence negative) _⦋0⦌) :
    smallVertexChoice incidence negative simplex ∈ smallSimplexShape incidence negative 0 simplex :=
  (smallSimplexShape_present incidence negative 0 simplex).1.choose_spec

def smallCarrierVertexTuple
    (simplex : (openStarSmallSet incidence negative) _⦋0⦌)
    (vertex : Chart) (present : vertex ∈ smallSimplexShape incidence negative 0 simplex) :
    forbiddenTuple incidence
      (faceCarrierNegative incidence negative (smallSimplexShape incidence negative 0 simplex)) 0 :=
  ⟨fun _column => vertex, by
    obtain ⟨ray, negativeRay, contains⟩ := (smallSimplexShape_present incidence negative 0 simplex).2
    exact ⟨ray, ⟨negativeRay, contains⟩, fun _column => contains vertex present⟩⟩

noncomputable def smallCarrierVerticesOfChoice
    (vertices : ∀ simplex : (openStarSmallSet incidence negative) _⦋0⦌,
      {vertex : Chart // vertex ∈ smallSimplexShape incidence negative 0 simplex}) :
    (smallSingularIncidenceCarrier incidence negative).CarrierMapValues 0 :=
  fun simplex => incidenceChainInclusion incidence
    (faceCarrierNegative incidence negative (smallSimplexShape incidence negative 0 simplex)) 0
    (smallCarrierVertexTuple incidence negative simplex (vertices simplex).val (vertices simplex).property)

theorem smallCarrierVerticesOfChoice_augmentation
    (vertices : ∀ simplex : (openStarSmallSet incidence negative) _⦋0⦌,
      {vertex : Chart // vertex ∈ smallSimplexShape incidence negative 0 simplex})
    (simplex : (openStarSmallSet incidence negative) _⦋0⦌) :
    smallCarrierVerticesOfChoice incidence negative vertices simplex ≫
      ((smallSingularIncidenceCarrier incidence negative).inclusion 0 simplex).f 0 ≫
        incidenceChainAugmentation incidence negative =
      Sigma.ι (fun _point : Unit => AddCommGrpCat.of ℤ) () := by
  change incidenceChainInclusion incidence
    (faceCarrierNegative incidence negative (smallSimplexShape incidence negative 0 simplex)) 0 _ ≫
    (faceCarrierChainInclusion incidence negative (smallSimplexShape incidence negative 0 simplex)).f 0 ≫
    incidenceChainAugmentation incidence negative = _
  rw [faceCarrierChainInclusion_augmentation, incidenceChainAugmentation_generator]

theorem smallCarrierVerticesOfChoice_compatible
    (vertices : ∀ simplex : (openStarSmallSet incidence negative) _⦋0⦌,
      {vertex : Chart // vertex ∈ smallSimplexShape incidence negative 0 simplex})
    (simplex : (openStarSmallSet incidence negative) _⦋1⦌) :
    smallCarrierVerticesOfChoice incidence negative vertices
        ((openStarSmallSet incidence negative).δ 0 simplex) ≫
      ((smallSingularIncidenceCarrier incidence negative).inclusion 0
        ((openStarSmallSet incidence negative).δ 0 simplex)).f 0 ≫
        incidenceChainAugmentation incidence negative =
    smallCarrierVerticesOfChoice incidence negative vertices
        ((openStarSmallSet incidence negative).δ 1 simplex) ≫
      ((smallSingularIncidenceCarrier incidence negative).inclusion 0
        ((openStarSmallSet incidence negative).δ 1 simplex)).f 0 ≫
        incidenceChainAugmentation incidence negative := by
  rw [smallCarrierVerticesOfChoice_augmentation, smallCarrierVerticesOfChoice_augmentation]

noncomputable def smallSingularIncidenceMapOfChoice
    (vertices : ∀ simplex : (openStarSmallSet incidence negative) _⦋0⦌,
      {vertex : Chart // vertex ∈ smallSimplexShape incidence negative 0 simplex}) :
    (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) ⟶
      incidenceChains incidence negative :=
  (smallSingularIncidenceCarrier incidence negative).extendCarriedVertexMap
    (smallCarrierVerticesOfChoice incidence negative vertices)
    (smallCarrierVerticesOfChoice_compatible incidence negative vertices)

noncomputable def smallSingularIncidenceMapOfChoice_carried
    (vertices : ∀ simplex : (openStarSmallSet incidence negative) _⦋0⦌,
      {vertex : Chart // vertex ∈ smallSimplexShape incidence negative 0 simplex}) :
    (smallSingularIncidenceCarrier incidence negative).CarriedIntegralChainMap
      (smallSingularIncidenceMapOfChoice incidence negative vertices) :=
  (smallSingularIncidenceCarrier incidence negative).extendCarriedVertexMap_carried
    (smallCarrierVerticesOfChoice incidence negative vertices)
    (smallCarrierVerticesOfChoice_compatible incidence negative vertices)

noncomputable def smallSingularIncidenceMap :
    (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) ⟶
      incidenceChains incidence negative :=
  smallSingularIncidenceMapOfChoice incidence negative
    (fun simplex => ⟨smallVertexChoice incidence negative simplex,
      smallVertexChoice_mem incidence negative simplex⟩)

noncomputable def smallSingularIncidenceMap_carried :
    (smallSingularIncidenceCarrier incidence negative).CarriedIntegralChainMap
      (smallSingularIncidenceMap incidence negative) :=
  smallSingularIncidenceMapOfChoice_carried incidence negative _

noncomputable def augmentedSmallSingularSet : SimplicialObject.Augmented Type where
  left := openStarSmallSet incidence negative
  right := Unit
  hom := { app := fun _simplex => ↾fun _value => () }

noncomputable def smallSingularChainAugmentationMap :
    (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering (Type) AddCommGrpCat.{0}).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj (augmentedSmallSingularSet incidence negative))

noncomputable def smallSingularChainAugmentation :
    ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X 0 ⟶
      incidenceAugmentationObject :=
  (smallSingularChainAugmentationMap incidence negative).f 0

omit [Finite Chart] in
theorem smallSingularChainAugmentation_generator
    (simplex : (openStarSmallSet incidence negative) _⦋0⦌) :
    (openStarSmallSet incidence negative).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
      smallSingularChainAugmentation incidence negative =
      Sigma.ι (fun _point : Unit => AddCommGrpCat.of ℤ) () := by
  unfold smallSingularChainAugmentation smallSingularChainAugmentationMap
  rw [AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  change Sigma.ι (fun _simplex : (openStarSmallSet incidence negative) _⦋0⦌ => AddCommGrpCat.of ℤ)
    simplex ≫ Sigma.map' (g := fun _simplex : (openStarSmallSet incidence negative) _⦋0⦌ =>
      AddCommGrpCat.of ℤ) (f := fun _point : Unit => AddCommGrpCat.of ℤ)
      (fun _simplex => ()) (fun _simplex => 𝟙 (AddCommGrpCat.of ℤ)) = _
  simp

theorem smallSingularIncidenceMapOfChoice_augmentation
    (vertices : ∀ simplex : (openStarSmallSet incidence negative) _⦋0⦌,
      {vertex : Chart // vertex ∈ smallSimplexShape incidence negative 0 simplex}) :
    (smallSingularIncidenceMapOfChoice incidence negative vertices).f 0 ≫
      incidenceChainAugmentation incidence negative =
      smallSingularChainAugmentation incidence negative := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc]
  change (openStarSmallSet incidence negative).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
    (smallSingularIncidenceCarrier incidence negative).carrierMapComponent 0
      (smallCarrierVerticesOfChoice incidence negative vertices) ≫
      incidenceChainAugmentation incidence negative = _
  rw [← Category.assoc, IntegralAcyclicCarrier.carrierMapComponent_generator, Category.assoc,
    smallCarrierVerticesOfChoice_augmentation, smallSingularChainAugmentation_generator]

end BondalThomsen.ConvexNerveSmallSingularComparison
