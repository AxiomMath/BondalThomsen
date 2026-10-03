module

public import BondalThomsen.Cohomology.ConvexNerve.GlobalCarrierHomotopy
public import BondalThomsen.Toric.Cohomology.NegativeSupportRelativeCohomology
public import BondalThomsen.Cohomology.ClosedCoverReducedZeroCohomology
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveGlobalCarrierHomotopy
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveReducedCochainAcyclicity

section AffineSimplices

variable {Ray : Type*} {Chart : Type} [Finite Chart]

def incidencePatches (incidence : Ray → Chart → Prop) (negative : Ray → Prop) : Chart → Set Ray :=
  fun chart => {ray | negative ray ∧ incidence ray chart}

omit [Finite Chart] in
theorem incidencePatches_coverNerve (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    coverNerve (incidencePatches incidence negative) = negativeChartComplex incidence negative := by
  apply PreAbstractSimplicialComplex.ext
  ext face
  change face ∈ coverNerve (incidencePatches incidence negative) ↔
    face ∈ negativeChartComplex incidence negative
  rw [mem_coverNerve_iff]
  change (face.Nonempty ∧ ∃ ray, ∀ chart ∈ face, negative ray ∧ incidence ray chart) ↔
    face.Nonempty ∧ ∃ ray, negative ray ∧ ∀ chart ∈ face, incidence ray chart
  constructor
  · rintro ⟨nonempty, ray, contains⟩
    obtain ⟨chart, present⟩ := nonempty.exists_mem
    exact ⟨nonempty, ray, (contains chart present).1, fun chart member => (contains chart member).2⟩
  · rintro ⟨nonempty, ray, negative_ray, contains⟩
    exact ⟨nonempty, ray, fun chart member => ⟨negative_ray, contains chart member⟩⟩

noncomputable abbrev incidenceRealization (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :=
  AbstractSimplicialComplex.Realization (activeNerve (incidencePatches incidence negative))

noncomputable def tupleActiveVertex (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) (index : Fin (degree + 1)) :
    ActiveIndex (incidencePatches incidence negative) :=
  ⟨tuple.val index, by
    obtain ⟨ray, negative_ray, contains⟩ := tuple.property
    exact ⟨ray, negative_ray, contains index⟩⟩

noncomputable def tupleAffineSimplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    C(Convexity.StdSimplex ℝ (Fin (degree + 1)), incidenceRealization incidence negative) where
  toFun point := simplexToRealization (activeNerve (incidencePatches incidence negative))
    (point.map (tupleActiveVertex incidence negative degree tuple)) (by
      change (point.map _).weights.support.image Subtype.val ∈ coverNerve (incidencePatches incidence negative)
      rw [incidencePatches_coverNerve]
      apply (negativeChartComplex incidence negative).isRelLowerSet_faces.mem_of_le
        ((tupleForbidden_iff_face incidence negative degree tuple.val).mp tuple.property)
      · rw [Convexity.StdSimplex.weights_map]
        apply Finset.Subset.trans (Finset.image_subset_image Finsupp.mapDomain_support)
        rw [Finset.image_image]
        exact Finset.image_subset_image (Finset.subset_univ _)
      · exact (Convexity.StdSimplex.support_weights_nonempty _).image _)
  continuous_toFun := (continuous_into_realization_iff _ _).mpr fun index =>
    (continuous_apply index).comp
      ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous.comp
        (Convexity.StdSimplex.continuous_map ℝ _))

theorem tupleAffineSimplex_precomp (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {degree next : ℕ} (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : forbiddenTuple incidence negative next) (point : Convexity.StdSimplex ℝ (Fin (degree + 1))) :
    tupleAffineSimplex incidence negative degree
      ⟨tuple.val ∘ selection, tupleForbidden_precomp incidence negative selection tuple.val tuple.property⟩ point =
    tupleAffineSimplex incidence negative next tuple (point.map selection) := by
  apply Subtype.ext
  change (point.map _).weights = ((point.map selection).map _).weights
  rw [← Convexity.StdSimplex.map_comp]
  rfl

end AffineSimplices

section SingularSimplices

variable {Ray : Type*} {Chart : Type} [Finite Chart]

noncomputable def tupleSingularSimplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    (TopCat.toSSet.obj (TopCat.of (incidenceRealization incidence negative))).obj (.op ⦋degree⦌) :=
  (TopCat.toSSetObjEquiv _ _).symm (tupleAffineSimplex incidence negative degree tuple)

theorem tupleSingularSimplex_precomp (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {source target : SimplexCategory} (selection : source ⟶ target)
    (tuple : forbiddenTuple incidence negative target.len) :
    (TopCat.toSSet.obj (TopCat.of (incidenceRealization incidence negative))).map selection.op
      (tupleSingularSimplex incidence negative target.len tuple) =
    tupleSingularSimplex incidence negative source.len
      ⟨tuple.val ∘ selection.toOrderHom,
        tupleForbidden_precomp incidence negative selection.toOrderHom tuple.val tuple.property⟩ := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro point
  exact (tupleAffineSimplex_precomp incidence negative selection.toOrderHom tuple point).symm

end SingularSimplices

section DualSingularComplex

noncomputable abbrev integralSingularChains (Space : Type) [TopologicalSpace Space] :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  (TopCat.toSSet.obj (TopCat.of Space)).chainComplex (AddCommGrpCat.of ℤ)

noncomputable def scalarCoefficientDual : AddCommGrpCat.{0}ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  CategoryTheory.preadditiveYoneda.obj (AddCommGrpCat.of 𝕜)

variable {𝕜} in
instance scalarCoefficientDual_additive : (scalarCoefficientDual 𝕜).Additive :=
  CategoryTheory.additive_yonedaObj' _

noncomputable abbrev dualChainComplex (complex : ChainComplex AddCommGrpCat.{0} ℕ) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  ((scalarCoefficientDual 𝕜).mapHomologicalComplex _).obj complex.op

noncomputable def dualChainMap {source target : ChainComplex AddCommGrpCat.{0} ℕ}
    (mapping : source ⟶ target) : dualChainComplex 𝕜 target ⟶ dualChainComplex 𝕜 source :=
  ((scalarCoefficientDual 𝕜).mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor _ _).map mapping.op)

end DualSingularComplex

section SingularHomotopies

theorem dualChainMap_id (complex : ChainComplex AddCommGrpCat.{0} ℕ) :
    dualChainMap 𝕜 (𝟙 complex) = 𝟙 (dualChainComplex 𝕜 complex) := by
  simp [dualChainMap]

theorem dualChainMap_comp {source middle target : ChainComplex AddCommGrpCat.{0} ℕ}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    dualChainMap 𝕜 (first ≫ second) = dualChainMap 𝕜 second ≫ dualChainMap 𝕜 first := by
  simp [dualChainMap]

noncomputable def dualChainHomotopy {source target : ChainComplex AddCommGrpCat.{0} ℕ}
    {first second : source ⟶ target} (homotopy : Homotopy first second) :
    Homotopy (dualChainMap 𝕜 first) (dualChainMap 𝕜 second) :=
  (scalarCoefficientDual 𝕜).mapHomotopy homotopy.op

noncomputable def dualChainHomotopyEquiv {source target : ChainComplex AddCommGrpCat.{0} ℕ}
    (equivalence : HomotopyEquiv source target) :
    HomotopyEquiv (dualChainComplex 𝕜 source) (dualChainComplex 𝕜 target) where
  hom := dualChainMap 𝕜 equivalence.inv
  inv := dualChainMap 𝕜 equivalence.hom
  homotopyHomInvId := by
    have homotopy := dualChainHomotopy 𝕜 equivalence.homotopyHomInvId
    simpa only [dualChainMap_comp, dualChainMap_id] using homotopy
  homotopyInvHomId := by
    have homotopy := dualChainHomotopy 𝕜 equivalence.homotopyInvHomId
    simpa only [dualChainMap_comp, dualChainMap_id] using homotopy

noncomputable def integralSingularChainHomotopyEquiv {Space Target : Type}
    [TopologicalSpace Space] [TopologicalSpace Target]
    (equivalence : ContinuousMap.HomotopyEquiv Space Target) :
    HomotopyEquiv (integralSingularChains Space) (integralSingularChains Target) := by
  let functor := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
  let source_homotopy := equivalence.left_inv.some
  let target_homotopy := equivalence.right_inv.some
  refine {
    hom := functor.map (TopCat.ofHom equivalence.toFun)
    inv := functor.map (TopCat.ofHom equivalence.invFun)
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_
  }
  · have homotopy : TopCat.Homotopy
        (TopCat.ofHom equivalence.toFun ≫ TopCat.ofHom equivalence.invFun)
        (𝟙 (TopCat.of Space)) := source_homotopy
    have result := homotopy.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)
    change Homotopy (functor.map (TopCat.ofHom equivalence.toFun ≫ TopCat.ofHom equivalence.invFun))
      (functor.map (𝟙 (TopCat.of Space))) at result
    rw [functor.map_comp] at result
    exact result.trans (Homotopy.ofEq (functor.map_id (TopCat.of Space)))
  · have homotopy : TopCat.Homotopy
        (TopCat.ofHom equivalence.invFun ≫ TopCat.ofHom equivalence.toFun)
        (𝟙 (TopCat.of Target)) := target_homotopy
    have result := homotopy.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)
    change Homotopy (functor.map (TopCat.ofHom equivalence.invFun ≫ TopCat.ofHom equivalence.toFun))
      (functor.map (𝟙 (TopCat.of Target))) at result
    rw [functor.map_comp] at result
    exact result.trans (Homotopy.ofEq (functor.map_id (TopCat.of Target)))

end SingularHomotopies

end BondalThomsen.ConvexNerveReducedCochainAcyclicity
