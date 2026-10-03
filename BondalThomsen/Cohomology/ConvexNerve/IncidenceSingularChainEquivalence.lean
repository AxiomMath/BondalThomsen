module

public import BondalThomsen.Cohomology.ConvexNerve.SubdivisionCellExpansion
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveBarycentricHomotopy
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceHomologyComparison
open BondalThomsen.ConvexNerveAcyclicCarrierAssembly
open BondalThomsen.ConvexNerveSmallSingularComparison
open BondalThomsen.ConvexNerveSubdivisionCellExpansion
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveIncidenceSingularChainEquivalence

theorem integralCoefficient_projective : Projective (AddCommGrpCat.of ℤ) where
  factors mapping surjection :=
    ⟨intLiftAlongEpi mapping surjection, intLiftAlongEpi_comp mapping surjection⟩

theorem integralSimplicialChains_projective (simplicial : SSet.{0}) (degree : ℕ) :
    Projective ((simplicial.chainComplex (AddCommGrpCat.of ℤ)).X degree) := by
  let : Projective (AddCommGrpCat.of ℤ) := integralCoefficient_projective
  change Projective (∐ fun _simplex : simplicial _⦋degree⦌ => AddCommGrpCat.of ℤ)
  infer_instance

noncomputable def integralQuasiIsoHomotopyEquiv {source target : SSet.{0}}
    (mapping : source.chainComplex (AddCommGrpCat.of ℤ) ⟶
      target.chainComplex (AddCommGrpCat.of ℤ)) (quasi : QuasiIso mapping) :
    HomotopyEquiv (source.chainComplex (AddCommGrpCat.of ℤ))
      (target.chainComplex (AddCommGrpCat.of ℤ)) := by
  letI : ∀ degree, Projective ((source.chainComplex (AddCommGrpCat.of ℤ)).X degree) :=
    integralSimplicialChains_projective source
  letI : ∀ degree, Projective ((target.chainComplex (AddCommGrpCat.of ℤ)).X degree) :=
    integralSimplicialChains_projective target
  exact ((ChainComplex.quasiIso_iff_of_projective mapping).mp quasi).choose

theorem integralQuasiIsoHomotopyEquiv_hom {source target : SSet.{0}}
    (mapping : source.chainComplex (AddCommGrpCat.of ℤ) ⟶
      target.chainComplex (AddCommGrpCat.of ℤ)) (quasi : QuasiIso mapping) :
    (integralQuasiIsoHomotopyEquiv mapping quasi).hom = mapping := by
  let : ∀ degree, Projective ((source.chainComplex (AddCommGrpCat.of ℤ)).X degree) :=
    integralSimplicialChains_projective source
  let : ∀ degree, Projective ((target.chainComplex (AddCommGrpCat.of ℤ)).X degree) :=
    integralSimplicialChains_projective target
  exact ((ChainComplex.quasiIso_iff_of_projective mapping).mp quasi).choose_spec

section ActualIncidence

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable def smallSingularChainHomotopyEquiv :
    HomotopyEquiv ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ))
      (integralSingularChains (incidenceRealization incidence negative)) :=
  integralQuasiIsoHomotopyEquiv (smallSingularChainInclusion incidence negative)
    (smallSingularChainInclusion_quasiIso incidence negative)

omit [Finite Chart] in
theorem smallSingularChainHomotopyEquiv_hom :
    (smallSingularChainHomotopyEquiv incidence negative).hom =
      smallSingularChainInclusion incidence negative :=
  integralQuasiIsoHomotopyEquiv_hom _ _

noncomputable def singularSmallChainRetraction :
    integralSingularChains (incidenceRealization incidence negative) ⟶
      (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) :=
  (smallSingularChainHomotopyEquiv incidence negative).inv

noncomputable def smallInclusionRetractionHomotopy :
    Homotopy (smallSingularChainInclusion incidence negative ≫
      singularSmallChainRetraction incidence negative)
      (𝟙 ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ))) := by
  simpa only [smallSingularChainHomotopyEquiv_hom, singularSmallChainRetraction] using
    (smallSingularChainHomotopyEquiv incidence negative).homotopyHomInvId

noncomputable def smallRetractionInclusionHomotopy :
    Homotopy (singularSmallChainRetraction incidence negative ≫
      smallSingularChainInclusion incidence negative)
      (𝟙 (integralSingularChains (incidenceRealization incidence negative))) := by
  simpa only [smallSingularChainHomotopyEquiv_hom, singularSmallChainRetraction] using
    (smallSingularChainHomotopyEquiv incidence negative).homotopyInvHomId

noncomputable def singularIncidenceChainMap :
    integralSingularChains (incidenceRealization incidence negative) ⟶
      incidenceChains incidence negative :=
  singularSmallChainRetraction incidence negative ≫ smallSingularIncidenceMap incidence negative

end ActualIncidence

section SingularAugmentation

noncomputable def augmentedSingularSet (Space : Type) [TopologicalSpace Space] :
    SimplicialObject.Augmented Type where
  left := TopCat.toSSet.obj (TopCat.of Space)
  right := Unit
  hom := { app := fun _simplex => ↾fun _value => () }

noncomputable def singularChainAugmentationMap (Space : Type) [TopologicalSpace Space] :
    integralSingularChains Space ⟶
      (ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering (Type) AddCommGrpCat.{0}).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj (augmentedSingularSet Space))

noncomputable def singularChainAugmentation (Space : Type) [TopologicalSpace Space] :
    (integralSingularChains Space).X 0 ⟶ incidenceAugmentationObject :=
  (singularChainAugmentationMap Space).f 0

theorem singularChainAugmentation_generator (Space : Type) [TopologicalSpace Space]
    (simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
      singularChainAugmentation Space =
      Sigma.ι (fun _point : Unit => AddCommGrpCat.of ℤ) () := by
  unfold singularChainAugmentation singularChainAugmentationMap
  rw [AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  change Sigma.ι (fun _simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋0⦌ =>
    AddCommGrpCat.of ℤ) simplex ≫ Sigma.map'
      (g := fun _simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋0⦌ => AddCommGrpCat.of ℤ)
      (f := fun _point : Unit => AddCommGrpCat.of ℤ)
      (fun _simplex => ()) (fun _simplex => 𝟙 (AddCommGrpCat.of ℤ)) = _
  simp

theorem singularChainAugmentation_zero (Space : Type) [TopologicalSpace Space] :
    (integralSingularChains Space).d 1 0 ≫ singularChainAugmentation Space = 0 := by
  have identity := (singularChainAugmentationMap Space).comm 1 0
  rw [HomologicalComplex.single_obj_d, comp_zero] at identity
  exact identity.symm

theorem singularChainAugmentation_naturality {Space Target : Type}
    [TopologicalSpace Space] [TopologicalSpace Target] (mapping : C(Space, Target)) :
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom mapping)) (AddCommGrpCat.of ℤ)).f 0 ≫
      singularChainAugmentation Target = singularChainAugmentation Space := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    singularChainAugmentation_generator, singularChainAugmentation_generator]

theorem singularChainAugmentationMap_naturality {Space Target : Type}
    [TopologicalSpace Space] [TopologicalSpace Target] (mapping : C(Space, Target)) :
    SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom mapping)) (AddCommGrpCat.of ℤ) ≫
      singularChainAugmentationMap Target = singularChainAugmentationMap Space := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  exact singularChainAugmentation_naturality mapping

noncomputable def pointSingularExtraDegeneracy :
    (augmentedSingularSet Unit).ExtraDegeneracy where
  s' := ↾fun _point => (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ ())
  s degree := ↾fun _simplex => (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ ())
  s'_comp_ε := by apply ConcreteCategory.hom_ext; intro point; rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro simplex
    apply (TopCat.toSSetObjEquiv _ _).injective
    exact Subsingleton.elim _ _
  s_comp_δ₀ degree := by
    apply ConcreteCategory.hom_ext
    intro simplex
    apply (TopCat.toSSetObjEquiv _ _).injective
    exact Subsingleton.elim _ _
  s_comp_δ degree deleted := by
    apply ConcreteCategory.hom_ext
    intro simplex
    apply (TopCat.toSSetObjEquiv _ _).injective
    exact Subsingleton.elim _ _
  s_comp_σ degree repeated := by
    apply ConcreteCategory.hom_ext
    intro simplex
    apply (TopCat.toSSetObjEquiv _ _).injective
    exact Subsingleton.elim _ _

noncomputable def pointSingularChainAugmentationHomotopyEquiv :
    HomotopyEquiv (integralSingularChains Unit)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject) :=
  (pointSingularExtraDegeneracy.map (sigmaConst.obj (AddCommGrpCat.of ℤ))).homotopyEquiv

noncomputable def contractibleSingularChainAugmentationHomotopyEquiv
    (Space : Type) [TopologicalSpace Space] [ContractibleSpace Space] :
    HomotopyEquiv (integralSingularChains Space)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject) :=
  (integralSingularChainHomotopyEquiv (ContractibleSpace.hequiv_unit Space).some).trans
    pointSingularChainAugmentationHomotopyEquiv

theorem contractibleSingularChainAugmentationHomotopyEquiv_hom
    (Space : Type) [TopologicalSpace Space] [ContractibleSpace Space] :
    (contractibleSingularChainAugmentationHomotopyEquiv Space).hom =
      singularChainAugmentationMap Space := by
  change SSet.chainComplexMap
    (TopCat.toSSet.map (TopCat.ofHom (ContractibleSpace.hequiv_unit Space).some.toFun))
      (AddCommGrpCat.of ℤ) ≫ singularChainAugmentationMap Unit = _
  exact singularChainAugmentationMap_naturality _

theorem contractibleSingularChains_exactAt_positive
    (Space : Type) [TopologicalSpace Space] [ContractibleSpace Space] (degree : ℕ) :
    (integralSingularChains Space).ExactAt (degree + 1) := by
  have zeroTerm : IsZero
      (((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject).X (degree + 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact (HomologicalComplex.ExactAt.of_isZero zeroTerm).isZero_homology.of_iso
    ((contractibleSingularChainAugmentationHomotopyEquiv Space).toHomologyIso (degree + 1))

theorem contractibleSingularChains_augmentedExact
    (Space : Type) [TopologicalSpace Space] [ContractibleSpace Space] :
    (ShortComplex.mk ((integralSingularChains Space).d 1 0)
      (singularChainAugmentation Space) (singularChainAugmentation_zero Space)).Exact := by
  let equivalence := contractibleSingularChainAugmentationHomotopyEquiv Space
  apply (ShortComplex.ab_exact_iff _).mpr
  intro cycle closed
  refine ⟨-equivalence.homotopyHomInvId.hom 0 1 cycle, ?_⟩
  have identity := ConcreteCategory.congr_hom (equivalence.homotopyHomInvId.comm 0) cycle
  rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex] at identity
  change (equivalence.hom.f 0 ≫ equivalence.inv.f 0) cycle =
    ((equivalence.homotopyHomInvId.hom 0 1 ≫ (integralSingularChains Space).d 1 0) +
      𝟙 ((integralSingularChains Space).X 0)) cycle
    at identity
  have canonical : equivalence.hom.f 0 = singularChainAugmentation Space :=
    congrArg (fun mapping => mapping.f 0)
      (contractibleSingularChainAugmentationHomotopyEquiv_hom Space)
  rw [canonical] at identity
  change (equivalence.inv.f 0).hom ((singularChainAugmentation Space).hom cycle) =
    ((equivalence.homotopyHomInvId.hom 0 1 ≫ (integralSingularChains Space).d 1 0) +
      𝟙 ((integralSingularChains Space).X 0)) cycle at identity
  rw [closed, map_zero] at identity
  have sumZero :
      (integralSingularChains Space).d 1 0 (equivalence.homotopyHomInvId.hom 0 1 cycle) + cycle = 0 := by
    simpa only [AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.id_apply, closed, map_zero] using identity.symm
  simpa only [map_neg, neg_neg] using congrArg Neg.neg (eq_neg_of_add_eq_zero_left sumZero)

end SingularAugmentation

section ClosedStarCarriers

attribute [local instance 2000] Classical.decEq

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable abbrev incidenceClosedStar
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) :=
  RealizedClosedStar (activeNerve (incidencePatches incidence negative)) face

noncomputable def closedStarInclusion
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) :
    C(incidenceClosedStar incidence negative face, incidenceRealization incidence negative) :=
  ⟨Subtype.val, continuous_subtype_val⟩

noncomputable def closedStarSingularInclusion
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) :
    TopCat.toSSet.obj (TopCat.of (incidenceClosedStar incidence negative face)) ⟶
      incidenceSingularSet incidence negative :=
  TopCat.toSSet.map (TopCat.ofHom (closedStarInclusion incidence negative face))

noncomputable def closedStarChainInclusion
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) :
    integralSingularChains (incidenceClosedStar incidence negative face) ⟶
      integralSingularChains (incidenceRealization incidence negative) :=
  SSet.chainComplexMap (closedStarSingularInclusion incidence negative face) (AddCommGrpCat.of ℤ)

omit [Finite Chart] in
theorem closedStarChainInclusion_mono
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) (degree : ℕ) :
    Mono ((closedStarChainInclusion incidence negative face).f degree) := by
  let inclusion := closedStarSingularInclusion incidence negative face
  have componentMono (simplex : SimplexCategoryᵒᵖ) : Mono (inclusion.app simplex) := by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro first second equality
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro point
    apply Subtype.ext
    exact congrArg (fun value => TopCat.toSSetObjEquiv _ _ value point) equality
  let : Mono inclusion := NatTrans.mono_of_mono_app inclusion
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of inclusion).hom
    (AddCommGrpCat.of ℤ)).f degree))

noncomputable def closedStarRefinement
    (smaller larger : Finset (ActiveIndex (incidencePatches incidence negative)))
    (subset : smaller ⊆ larger) :
    C(incidenceClosedStar incidence negative larger, incidenceClosedStar incidence negative smaller) := by
  have stays (point : incidenceClosedStar incidence negative larger) :
      point.val.val.support ∪ smaller ∈ activeNerve (incidencePatches incidence negative) := by
    exact (activeNerve (incidencePatches incidence negative)).isRelLowerSet_faces.mem_of_le
      point.property (Finset.union_subset_union_right subset)
      (((activeNerve (incidencePatches incidence negative)).isRelLowerSet_faces.prop_of_mem
        (AbstractSimplicialComplex.support_mem _ point.val)).mono Finset.subset_union_left)
  exact { toFun := fun point => ⟨point.val, stays point⟩
          continuous_toFun := continuous_subtype_val.subtype_mk stays }

noncomputable def closedStarChainRefinement
    (smaller larger : Finset (ActiveIndex (incidencePatches incidence negative)))
    (subset : smaller ⊆ larger) :
    integralSingularChains (incidenceClosedStar incidence negative larger) ⟶
      integralSingularChains (incidenceClosedStar incidence negative smaller) :=
  SSet.chainComplexMap (TopCat.toSSet.map
    (TopCat.ofHom (closedStarRefinement incidence negative smaller larger subset))) (AddCommGrpCat.of ℤ)

omit [Finite Chart] in
theorem closedStarChainRefinement_inclusion
    (smaller larger : Finset (ActiveIndex (incidencePatches incidence negative)))
    (subset : smaller ⊆ larger) :
    closedStarChainRefinement incidence negative smaller larger subset ≫
      closedStarChainInclusion incidence negative smaller =
      closedStarChainInclusion incidence negative larger := by
  change ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of ℤ)).map _ ≫
      ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of ℤ)).map _ = _
  rw [← Functor.map_comp]
  rfl

noncomputable def smallClosedStarCarrier :
    IntegralAcyclicCarrier (openStarSmallSet incidence negative)
      (integralSingularChains (incidenceRealization incidence negative))
      (singularChainAugmentation (incidenceRealization incidence negative)) where
  complex degree simplex := integralSingularChains (incidenceClosedStar incidence negative
    (commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val))
  inclusion degree simplex := closedStarChainInclusion incidence negative _
  inclusion_mono degree simplex component := closedStarChainInclusion_mono incidence negative _ _
  faceMap degree deleted simplex := closedStarChainRefinement incidence negative _ _
    (commonPositiveVertices_precomp incidence negative (SimplexCategory.δ deleted) simplex.val)
  faceMap_inclusion degree deleted simplex := closedStarChainRefinement_inclusion incidence negative _ _ _
  augmentation_zero degree simplex := by
    rw [closedStarChainInclusion, closedStarSingularInclusion, singularChainAugmentation_naturality]
    exact singularChainAugmentation_zero _
  exact_zero degree simplex := by
    dsimp only [closedStarChainInclusion, closedStarSingularInclusion]
    simp only [singularChainAugmentation_naturality]
    let := realizedClosedStar_contractible (activeNerve (incidencePatches incidence negative))
      ⟨_, commonPositiveVertices_face incidence negative _ simplex.val simplex.property⟩
    exact contractibleSingularChains_augmentedExact _
  exact_positive degree simplex component := by
    let := realizedClosedStar_contractible (activeNerve (incidencePatches incidence negative))
      ⟨_, commonPositiveVertices_face incidence negative _ simplex.val simplex.property⟩
    exact contractibleSingularChains_exactAt_positive _ component

noncomputable def smallSimplexClosedStarMap (degree : ℕ)
    (simplex : (openStarSmallSet incidence negative) _⦋degree⦌) :
    C(Convexity.StdSimplex ℝ (Fin (degree + 1)), incidenceClosedStar incidence negative
      (commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val)) := by
  have stays (point : Convexity.StdSimplex ℝ (Fin (degree + 1))) :
      (singularSimplexMap incidence negative (.op ⦋degree⦌) simplex.val point).val.support ∪
        commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val ∈
          activeNerve (incidencePatches incidence negative) := by
    rw [Finset.union_eq_left.mpr (commonPositiveVertices_support incidence negative _ simplex.val point)]
    exact AbstractSimplicialComplex.support_mem _ _
  exact { toFun := fun point => ⟨singularSimplexMap incidence negative (.op ⦋degree⦌) simplex.val point,
            stays point⟩
          continuous_toFun := (singularSimplexMap incidence negative _ simplex.val).continuous.subtype_mk stays }

noncomputable def smallInclusion_closedStarCarried :
    (smallClosedStarCarrier incidence negative).CarriedIntegralChainMap
      (smallSingularChainInclusion incidence negative) where
  value degree simplex := (TopCat.toSSet.obj (TopCat.of
    (incidenceClosedStar incidence negative
      (commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val)))).ιChainComplex
      (R := AddCommGrpCat.of ℤ)
      ((TopCat.toSSetObjEquiv _ _).symm (smallSimplexClosedStarMap incidence negative degree simplex))
  value_inclusion degree simplex := by
    change _ ≫ (closedStarChainInclusion incidence negative _).f degree = _
    rw [closedStarChainInclusion, SSet.ι_chainComplexMap_f]
    rw [smallSingularChainInclusion, SSet.ι_chainComplexMap_f]
    congr 1

noncomputable def faceTupleClosedStarMap
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) (degree : ℕ)
    (tuple : forbiddenTuple incidence (faceCarrierNegative incidence negative (face.image Subtype.val)) degree) :
    C(Convexity.StdSimplex ℝ (Fin (degree + 1)), incidenceClosedStar incidence negative face) where
  toFun point :=
    ⟨tupleAffineSimplex incidence negative degree
      ⟨tuple.val, by obtain ⟨ray, ⟨negativeRay, _⟩, contains⟩ := tuple.property
                     exact ⟨ray, negativeRay, contains⟩⟩ point, by
      change (_ ∪ face).image Subtype.val ∈ coverNerve (incidencePatches incidence negative)
      rw [Finset.image_union, incidencePatches_coverNerve]
      apply (negativeChartComplex incidence negative).isRelLowerSet_faces.mem_of_le
        ((faceCarrier_tuple_iff incidence negative (face.image Subtype.val) degree tuple.val).mp tuple.property)
      · apply Finset.union_subset_union_left
        change (point.map (tupleActiveVertex incidence negative degree _)).weights.support.image
          Subtype.val ⊆ Finset.univ.image tuple.val
        rw [Convexity.StdSimplex.weights_map]
        apply Finset.Subset.trans (Finset.image_subset_image Finsupp.mapDomain_support)
        rw [Finset.image_image]
        exact Finset.image_subset_image (Finset.subset_univ _)
      · exact (Convexity.StdSimplex.support_weights_nonempty
          (point.map (tupleActiveVertex incidence negative degree _))).image Subtype.val |>.mono
            Finset.subset_union_left⟩
  continuous_toFun := (tupleAffineSimplex incidence negative degree _).continuous.subtype_mk _

noncomputable def faceIncidenceClosedStarSimplicialMap
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) :
    incidenceSimplicialSet incidence (faceCarrierNegative incidence negative (face.image Subtype.val)) ⟶
      TopCat.toSSet.obj (TopCat.of (incidenceClosedStar incidence negative face)) where
  app simplex := ↾fun tuple => (TopCat.toSSetObjEquiv _ _).symm
    (faceTupleClosedStarMap incidence negative face simplex.unop.len tuple)
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro point
    apply Subtype.ext
    change tupleAffineSimplex incidence negative target.unop.len _ point =
      tupleAffineSimplex incidence negative source.unop.len _
        (point.map selection.unop.toOrderHom)
    exact (tupleAffineSimplex_precomp incidence negative selection.unop.toOrderHom
      ⟨tuple.val, by obtain ⟨ray, ⟨negativeRay, _⟩, contains⟩ := tuple.property
                     exact ⟨ray, negativeRay, contains⟩⟩ point)

noncomputable def faceIncidenceClosedStarChainMap
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) :
    incidenceChains incidence (faceCarrierNegative incidence negative (face.image Subtype.val)) ⟶
      integralSingularChains (incidenceClosedStar incidence negative face) :=
  SSet.chainComplexMap (faceIncidenceClosedStarSimplicialMap incidence negative face) (AddCommGrpCat.of ℤ)

theorem faceIncidenceClosedStarChainMap_inclusion
    (face : Finset (ActiveIndex (incidencePatches incidence negative))) :
    faceIncidenceClosedStarChainMap incidence negative face ≫ closedStarChainInclusion incidence negative face =
      faceCarrierChainInclusion incidence negative (face.image Subtype.val) ≫
        affineSingularChainMap incidence negative := by
  apply HomologicalComplex.Hom.ext
  funext degree
  apply SSet.chainComplex_hom_ext
  intro tuple
  change _ ≫ ((faceIncidenceClosedStarChainMap incidence negative face).f degree ≫ _) =
    _ ≫ ((faceCarrierChainInclusion incidence negative _).f degree ≫ _)
  rw [← Category.assoc, faceIncidenceClosedStarChainMap, SSet.ι_chainComplexMap_f,
    closedStarChainInclusion, SSet.ι_chainComplexMap_f]
  rw [← Category.assoc, faceCarrierChainInclusion, SSet.ι_chainComplexMap_f,
    affineSingularChainMap, SSet.ι_chainComplexMap_f]
  congr 1

noncomputable def smallIncidenceAffine_closedStarCarried :
    (smallClosedStarCarrier incidence negative).CarriedIntegralChainMap
      (smallSingularIncidenceMap incidence negative ≫ affineSingularChainMap incidence negative) where
  value degree simplex :=
    (smallSingularIncidenceMap_carried incidence negative).value degree simplex ≫
      (faceIncidenceClosedStarChainMap incidence negative
        (commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val)).f degree
  value_inclusion degree simplex := by
    change _ ≫ (closedStarChainInclusion incidence negative
      (commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val)).f degree = _
    rw [Category.assoc, ← HomologicalComplex.comp_f, faceIncidenceClosedStarChainMap_inclusion,
      HomologicalComplex.comp_f, ← Category.assoc]
    have carried := (smallSingularIncidenceMap_carried incidence negative).value_inclusion degree simplex
    change _ ≫ (faceCarrierChainInclusion incidence negative
      ((commonPositiveVertices incidence negative (.op ⦋degree⦌) simplex.val).image Subtype.val)).f degree = _
      at carried
    rw [carried, Category.assoc]
    rfl

theorem affineSingularChainMap_augmentation :
    (affineSingularChainMap incidence negative).f 0 ≫
      singularChainAugmentation (incidenceRealization incidence negative) =
      incidenceChainAugmentation incidence negative := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  rw [← Category.assoc, affineSingularChainMap, SSet.ι_chainComplexMap_f,
    singularChainAugmentation_generator]
  exact (incidenceChainAugmentation_generator incidence negative tuple).symm

omit [Finite Chart] in
theorem smallSingularChainInclusion_augmentation :
    (smallSingularChainInclusion incidence negative).f 0 ≫
      singularChainAugmentation (incidenceRealization incidence negative) =
      smallSingularChainAugmentation incidence negative := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, smallSingularChainInclusion, SSet.ι_chainComplexMap_f,
    singularChainAugmentation_generator]
  exact (smallSingularChainAugmentation_generator incidence negative simplex).symm

noncomputable def smallIncidenceAffineHomotopy :
    Homotopy (smallSingularIncidenceMap incidence negative ≫ affineSingularChainMap incidence negative)
      (smallSingularChainInclusion incidence negative) :=
  (smallClosedStarCarrier incidence negative).carriedMapsHomotopy
    (smallIncidenceAffine_closedStarCarried incidence negative)
    (smallInclusion_closedStarCarried incidence negative) (by
      rw [HomologicalComplex.comp_f, Category.assoc, affineSingularChainMap_augmentation,
        smallSingularChainInclusion_augmentation]
      exact smallSingularIncidenceMapOfChoice_augmentation incidence negative _)

noncomputable def singularIncidenceAffineHomotopy :
    Homotopy (singularIncidenceChainMap incidence negative ≫ affineSingularChainMap incidence negative)
      (𝟙 (integralSingularChains (incidenceRealization incidence negative))) := by
  have comparison : Homotopy
      (singularIncidenceChainMap incidence negative ≫ affineSingularChainMap incidence negative)
      (singularSmallChainRetraction incidence negative ≫ smallSingularChainInclusion incidence negative) := by
    simpa only [singularIncidenceChainMap, Category.assoc] using
    (smallIncidenceAffineHomotopy incidence negative).compLeft
      (singularSmallChainRetraction incidence negative)
  exact comparison.trans (smallRetractionInclusionHomotopy incidence negative)

theorem affineSingularChainMap_augmentationMap :
    affineSingularChainMap incidence negative ≫
      singularChainAugmentationMap (incidenceRealization incidence negative) =
      incidenceChainAugmentationMap incidence negative := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  exact affineSingularChainMap_augmentation incidence negative

end ClosedStarCarriers

section ConeEquivalences

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
variable (anchor : Chart)
variable (cone : PreAbstractSimplicialComplex.IsCone (negativeChartComplex incidence negative) anchor)

include anchor cone

end ConeEquivalences

end BondalThomsen.ConvexNerveIncidenceSingularChainEquivalence
