module

public import BondalThomsen.Cohomology.ConvexNerve.SmallSingularComparison
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Algebra.Homology.ConcreteCategory

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
open BondalThomsen.ConvexNerveSmallSingularComparison
open scoped Classical Simplicial unitInterval

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveSmallChainQuasiIso

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

@[instance_reducible] noncomputable def simplexMetricSpace (degree : ℕ) :
    MetricSpace (Convexity.StdSimplex ℝ (Fin (degree + 1))) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (degree + 1))).comapMetricSpace _

attribute [local instance] simplexMetricSpace

omit [Finite Chart] in
theorem singularSimplex_lebesgueNumber (degree : ℕ)
    (simplex : (incidenceSingularSet incidence negative) _⦋degree⦌) :
    ∃ radius > 0, ∀ point : Convexity.StdSimplex ℝ (Fin (degree + 1)),
      ∃ vertex, Metric.ball point radius ⊆
        (singularSimplexMap incidence negative (.op ⦋degree⦌) simplex) ⁻¹'
          realizationOpenStar incidence negative vertex := by
  suffices ∃ radius > 0, ∀ point ∈ (Set.univ : Set (Convexity.StdSimplex ℝ (Fin (degree + 1)))),
      ∃ vertex, Metric.ball point radius ⊆
        (singularSimplexMap incidence negative (.op ⦋degree⦌) simplex) ⁻¹'
          realizationOpenStar incidence negative vertex by
    simpa only [Set.mem_univ, forall_true_left] using this
  apply lebesgue_number_lemma_of_metric isCompact_univ
  · intro vertex
    exact (realizationOpenStar_isOpen incidence negative vertex).preimage
      (singularSimplexMap incidence negative (.op ⦋degree⦌) simplex).continuous
  · intro point _present
    obtain ⟨vertex, positive⟩ := realizationOpenStar_cover incidence negative
      (singularSimplexMap incidence negative (.op ⦋degree⦌) simplex point)
    exact Set.mem_iUnion.mpr ⟨vertex, positive⟩

omit [Finite Chart] in
theorem sufficientlySmallSimplexMap_isSmall {sourceDegree targetDegree : ℕ}
    (simplex : (incidenceSingularSet incidence negative) _⦋targetDegree⦌)
    (radius : ℝ) (lebesgue : ∀ point : Convexity.StdSimplex ℝ (Fin (targetDegree + 1)),
      ∃ vertex, Metric.ball point radius ⊆
        (singularSimplexMap incidence negative (.op ⦋targetDegree⦌) simplex) ⁻¹'
          realizationOpenStar incidence negative vertex)
    (mapping : C(Convexity.StdSimplex ℝ (Fin (sourceDegree + 1)),
      Convexity.StdSimplex ℝ (Fin (targetDegree + 1))))
    (center : Convexity.StdSimplex ℝ (Fin (targetDegree + 1)))
    (smallImage : Set.range mapping ⊆ Metric.ball center radius) :
    IsOpenStarSmall incidence negative (.op ⦋sourceDegree⦌)
      ((TopCat.toSSetObjEquiv _ _).symm
        ((singularSimplexMap incidence negative (.op ⦋targetDegree⦌) simplex).comp mapping)) := by
  obtain ⟨vertex, contains⟩ := lebesgue center
  refine ⟨vertex, fun point => ?_⟩
  exact contains (smallImage (Set.mem_range_self point))

omit [Finite Chart] in
theorem allSingularVertices_small
    (simplex : (incidenceSingularSet incidence negative) _⦋0⦌) :
    IsOpenStarSmall incidence negative (.op ⦋0⦌) simplex := by
  obtain ⟨vertex, positive⟩ := realizationOpenStar_cover incidence negative
    (singularSimplexMap incidence negative (.op ⦋0⦌) simplex (Convexity.StdSimplex.single 0))
  exact ⟨vertex, fun point => by
    rw [Subsingleton.elim point (Convexity.StdSimplex.single 0)]
    exact positive⟩

noncomputable def smallVertexChainInverse :
    (integralSingularChains (incidenceRealization incidence negative)).X 0 ⟶
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X 0 :=
  Sigma.desc fun simplex => (openStarSmallSet incidence negative).ιChainComplex
    ⟨simplex, allSingularVertices_small incidence negative simplex⟩

omit [Finite Chart] in
theorem smallVertexChainInverse_inclusion :
    smallVertexChainInverse incidence negative ≫ (smallSingularChainInclusion incidence negative).f 0 =
      𝟙 ((integralSingularChains (incidenceRealization incidence negative)).X 0) := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  change Sigma.ι _ simplex ≫ (Sigma.desc _ ≫ _) = Sigma.ι _ simplex ≫ 𝟙 _
  rw [← Category.assoc, Sigma.ι_comp_desc]
  simp only [smallSingularChainInclusion, SSet.ι_chainComplexMap_f, Category.comp_id]
  rfl

omit [Finite Chart] in
theorem inclusion_smallVertexChainInverse :
    (smallSingularChainInclusion incidence negative).f 0 ≫ smallVertexChainInverse incidence negative =
      𝟙 (((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X 0) := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc]
  change (openStarSmallSet incidence negative).ιChainComplex simplex ≫
    (SSet.chainComplexMap (openStarSmallSubcomplex incidence negative).ι (AddCommGrpCat.of ℤ)).f 0 ≫
    smallVertexChainInverse incidence negative = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  change Sigma.ι _ simplex.val ≫ Sigma.desc _ = _
  rw [Sigma.ι_comp_desc]
  simp only [Category.comp_id]
  congr 1

noncomputable def singularEdgePath
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) :
    C(unitInterval, incidenceRealization incidence negative) :=
  (singularSimplexMap incidence negative (.op ⦋1⦌) simplex).comp
    ⟨Convexity.StdSimplex.homeomorphI.symm, Convexity.StdSimplex.homeomorphI.symm.continuous⟩

omit [Finite Chart] in
theorem singularEdge_smallPartition
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) :
    ∃ partition : ℕ → unitInterval, partition 0 = 0 ∧ Monotone partition ∧
      (∃ length, ∀ index ≥ length, partition index = 1) ∧
      ∀ index, ∃ vertex, Set.Icc (partition index) (partition (index + 1)) ⊆
        (singularEdgePath incidence negative simplex) ⁻¹' realizationOpenStar incidence negative vertex := by
  apply exists_monotone_Icc_subset_open_cover_unitInterval
  · intro vertex
    exact (realizationOpenStar_isOpen incidence negative vertex).preimage
      (singularEdgePath incidence negative simplex).continuous
  · intro point _present
    obtain ⟨vertex, positive⟩ := realizationOpenStar_cover incidence negative
      (singularEdgePath incidence negative simplex point)
    exact Set.mem_iUnion.mpr ⟨vertex, positive⟩

noncomputable def intervalSubedgeSimplex
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌)
    (left right : unitInterval) : (incidenceSingularSet incidence negative) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm {
    toFun point := singularEdgePath incidence negative simplex
      (Set.Icc.convexComb left right (Convexity.StdSimplex.homeomorphI point))
    continuous_toFun := (singularEdgePath incidence negative simplex).continuous.comp
      ((Set.Icc.continuous_convexComb left right).comp
        Convexity.StdSimplex.homeomorphI.continuous)
  }

omit [Finite Chart] in
theorem intervalSubedgeSimplex_small
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌)
    (left right : unitInterval) (ordered : left ≤ right)
    (vertex : ActiveIndex (incidencePatches incidence negative))
    (contains : Set.Icc left right ⊆
      (singularEdgePath incidence negative simplex) ⁻¹' realizationOpenStar incidence negative vertex) :
    IsOpenStarSmall incidence negative (.op ⦋1⦌)
      (intervalSubedgeSimplex incidence negative simplex left right) := by
  refine ⟨vertex, fun point => ?_⟩
  exact contains ⟨Set.Icc.le_convexComb ordered _, Set.Icc.convexComb_le ordered _⟩

noncomputable def singularPointVertex (point : incidenceRealization incidence negative) :
    (incidenceSingularSet incidence negative) _⦋0⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ point)

omit [Finite Chart] in
theorem intervalSubedgeSimplex_face_zero
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) (left right : unitInterval) :
    (incidenceSingularSet incidence negative).δ 0
      (intervalSubedgeSimplex incidence negative simplex left right) =
    singularPointVertex incidence negative (singularEdgePath incidence negative simplex right) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro point
  have equal : point = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
  subst point
  change singularSimplexMap incidence negative (.op ⦋0⦌)
    ((incidenceSingularSet incidence negative).map (SimplexCategory.δ (0 : Fin 2)).op
      (intervalSubedgeSimplex incidence negative simplex left right))
    (Convexity.StdSimplex.single 0) = _
  rw [singularSimplexMap_precomp, Convexity.StdSimplex.map_single]
  change singularEdgePath incidence negative simplex
    (Set.Icc.convexComb left right (Convexity.StdSimplex.homeomorphI (Convexity.StdSimplex.single 1))) = _
  simp [singularPointVertex]

omit [Finite Chart] in
theorem intervalSubedgeSimplex_face_one
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) (left right : unitInterval) :
    (incidenceSingularSet incidence negative).δ 1
      (intervalSubedgeSimplex incidence negative simplex left right) =
    singularPointVertex incidence negative (singularEdgePath incidence negative simplex left) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro point
  have equal : point = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
  subst point
  change singularSimplexMap incidence negative (.op ⦋0⦌)
    ((incidenceSingularSet incidence negative).map (SimplexCategory.δ (1 : Fin 2)).op
      (intervalSubedgeSimplex incidence negative simplex left right))
    (Convexity.StdSimplex.single 0) = _
  rw [singularSimplexMap_precomp, Convexity.StdSimplex.map_single]
  change singularEdgePath incidence negative simplex
    (Set.Icc.convexComb left right (Convexity.StdSimplex.homeomorphI (Convexity.StdSimplex.single 0))) = _
  simp [singularPointVertex]

omit [Finite Chart] in
theorem singularEdge_face_zero
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) :
    (incidenceSingularSet incidence negative).δ 0 simplex =
      singularPointVertex incidence negative (singularEdgePath incidence negative simplex 1) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro point
  have equal : point = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
  subst point
  change singularSimplexMap incidence negative (.op ⦋0⦌)
    ((incidenceSingularSet incidence negative).map (SimplexCategory.δ (0 : Fin 2)).op simplex)
    (Convexity.StdSimplex.single 0) = _
  rw [singularSimplexMap_precomp, Convexity.StdSimplex.map_single]
  change singularSimplexMap incidence negative (.op ⦋1⦌) simplex
      (Convexity.StdSimplex.single 1) = singularSimplexMap incidence negative (.op ⦋1⦌) simplex
        (Convexity.StdSimplex.homeomorphI.symm 1)
  simp

omit [Finite Chart] in
theorem singularEdge_face_one
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) :
    (incidenceSingularSet incidence negative).δ 1 simplex =
      singularPointVertex incidence negative (singularEdgePath incidence negative simplex 0) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro point
  have equal : point = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
  subst point
  change singularSimplexMap incidence negative (.op ⦋0⦌)
    ((incidenceSingularSet incidence negative).map (SimplexCategory.δ (1 : Fin 2)).op simplex)
    (Convexity.StdSimplex.single 0) = _
  rw [singularSimplexMap_precomp, Convexity.StdSimplex.map_single]
  change singularSimplexMap incidence negative (.op ⦋1⦌) simplex
      (Convexity.StdSimplex.single 0) = singularSimplexMap incidence negative (.op ⦋1⦌) simplex
        (Convexity.StdSimplex.homeomorphI.symm 0)
  simp

omit [Finite Chart] in
theorem singularEdge_chainBoundary
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) :
    (incidenceSingularSet incidence negative).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
      (integralSingularChains (incidenceRealization incidence negative)).d 1 0 =
      (incidenceSingularSet incidence negative).ιChainComplex
        ((incidenceSingularSet incidence negative).δ 0 simplex) -
      (incidenceSingularSet incidence negative).ιChainComplex
        ((incidenceSingularSet incidence negative).δ 1 simplex) := by
  rw [SSet.ιChainComplex_d]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

omit [Finite Chart] in
theorem exists_smallEdgeBoundaryLift
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) :
    ∃ lift : AddCommGrpCat.of ℤ ⟶
        ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X 1,
      lift ≫ ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d 1 0 ≫
        (smallSingularChainInclusion incidence negative).f 0 =
      (incidenceSingularSet incidence negative).ιChainComplex simplex ≫
        (integralSingularChains (incidenceRealization incidence negative)).d 1 0 := by
  obtain ⟨partition, starts, monotone, ⟨length, ends⟩, covers⟩ :=
    singularEdge_smallPartition incidence negative simplex
  let smallEdge (index : ℕ) : (openStarSmallSet incidence negative) _⦋1⦌ :=
    ⟨intervalSubedgeSimplex incidence negative simplex (partition index) (partition (index + 1)),
      intervalSubedgeSimplex_small incidence negative simplex _ _
        (monotone (Nat.le_succ index)) (covers index).choose (covers index).choose_spec⟩
  refine ⟨∑ index ∈ Finset.range length,
    (openStarSmallSet incidence negative).ιChainComplex (smallEdge index), ?_⟩
  rw [← (smallSingularChainInclusion incidence negative).comm 1 0]
  simp only [sum_comp, ← Category.assoc]
  have generator (index : ℕ) :
      (openStarSmallSet incidence negative).ιChainComplex (R := AddCommGrpCat.of ℤ) (smallEdge index) ≫
        (smallSingularChainInclusion incidence negative).f 1 ≫
          (integralSingularChains (incidenceRealization incidence negative)).d 1 0 =
      (incidenceSingularSet incidence negative).ιChainComplex
        (singularPointVertex incidence negative (singularEdgePath incidence negative simplex (partition (index + 1)))) -
      (incidenceSingularSet incidence negative).ιChainComplex
        (singularPointVertex incidence negative (singularEdgePath incidence negative simplex (partition index))) := by
    change (openStarSmallSet incidence negative).ιChainComplex (smallEdge index) ≫
      ((SSet.chainComplexMap (openStarSmallSubcomplex incidence negative).ι (AddCommGrpCat.of ℤ)).f 1 ≫ _) = _
    rw [← Category.assoc, SSet.ι_chainComplexMap_f]
    change (incidenceSingularSet incidence negative).ιChainComplex
      (intervalSubedgeSimplex incidence negative simplex _ _) ≫ _ = _
    rw [singularEdge_chainBoundary, intervalSubedgeSimplex_face_zero, intervalSubedgeSimplex_face_one]
  simp only [Category.assoc, generator]
  rw [Finset.sum_range_sub (fun index =>
    (incidenceSingularSet incidence negative).ιChainComplex (R := AddCommGrpCat.of ℤ)
      (singularPointVertex incidence negative (singularEdgePath incidence negative simplex (partition index)))),
    starts, ends length le_rfl,
    singularEdge_chainBoundary, singularEdge_face_zero, singularEdge_face_one]

noncomputable def smallEdgeBoundaryLift
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) :
    AddCommGrpCat.of ℤ ⟶
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X 1 :=
  (exists_smallEdgeBoundaryLift incidence negative simplex).choose

omit [Finite Chart] in
theorem smallEdgeBoundaryLift_boundary
    (simplex : (incidenceSingularSet incidence negative) _⦋1⦌) :
    smallEdgeBoundaryLift incidence negative simplex ≫
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d 1 0 =
    (incidenceSingularSet incidence negative).ιChainComplex simplex ≫
      (integralSingularChains (incidenceRealization incidence negative)).d 1 0 ≫
        smallVertexChainInverse incidence negative := by
  have equality := congrArg (fun mapping => mapping ≫ smallVertexChainInverse incidence negative)
    (exists_smallEdgeBoundaryLift incidence negative simplex).choose_spec
  simpa only [Category.assoc, inclusion_smallVertexChainInverse, Category.comp_id,
    smallEdgeBoundaryLift] using equality

noncomputable def smallBoundaryChainLift :
    (integralSingularChains (incidenceRealization incidence negative)).X 1 ⟶
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X 1 :=
  Sigma.desc (smallEdgeBoundaryLift incidence negative)

omit [Finite Chart] in
theorem smallBoundaryChainLift_boundary :
    smallBoundaryChainLift incidence negative ≫
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d 1 0 =
    (integralSingularChains (incidenceRealization incidence negative)).d 1 0 ≫
      smallVertexChainInverse incidence negative := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  change Sigma.ι _ simplex ≫ (Sigma.desc _ ≫ _) = _
  rw [← Category.assoc, Sigma.ι_comp_desc, smallEdgeBoundaryLift_boundary]

noncomputable abbrev smallZeroShortComplex : ShortComplex AddCommGrpCat.{0} :=
  HomologicalComplex.sc' ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)) 1 0 0

noncomputable abbrev singularZeroShortComplex : ShortComplex AddCommGrpCat.{0} :=
  HomologicalComplex.sc' (integralSingularChains (incidenceRealization incidence negative)) 1 0 0

noncomputable def smallZeroShortInclusion :
    smallZeroShortComplex incidence negative ⟶ singularZeroShortComplex incidence negative :=
  (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{0} (ComplexShape.down ℕ) 1 0 0).map
    (smallSingularChainInclusion incidence negative)

noncomputable def smallZeroShortInverse :
    singularZeroShortComplex incidence negative ⟶ smallZeroShortComplex incidence negative where
  τ₁ := smallBoundaryChainLift incidence negative
  τ₂ := smallVertexChainInverse incidence negative
  τ₃ := smallVertexChainInverse incidence negative
  comm₁₂ := smallBoundaryChainLift_boundary incidence negative
  comm₂₃ := by
    change smallVertexChainInverse incidence negative ≫
        ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d 0 0 =
      (integralSingularChains (incidenceRealization incidence negative)).d 0 0 ≫
        smallVertexChainInverse incidence negative
    simp

theorem shortHomologyMap_eq_of_middle {source target : ShortComplex AddCommGrpCat.{0}}
    (first second : source ⟶ target) (same : first.τ₂ = second.τ₂) :
    ShortComplex.homologyMap first = ShortComplex.homologyMap second := by
  apply (cancel_epi source.homologyπ).mp
  apply (cancel_mono target.homologyι).mp
  simp only [Category.assoc, ShortComplex.π_homologyMap_ι, same]

omit [Finite Chart] in
theorem smallZeroShortInclusion_inverse_homology :
    ShortComplex.homologyMap (smallZeroShortInclusion incidence negative) ≫
      ShortComplex.homologyMap (smallZeroShortInverse incidence negative) =
      𝟙 ((smallZeroShortComplex incidence negative).homology) := by
  rw [← ShortComplex.homologyMap_comp]
  have same := shortHomologyMap_eq_of_middle
    (smallZeroShortInclusion incidence negative ≫ smallZeroShortInverse incidence negative)
    (𝟙 (smallZeroShortComplex incidence negative)) (inclusion_smallVertexChainInverse incidence negative)
  rw [same, ShortComplex.homologyMap_id]

omit [Finite Chart] in
theorem smallZeroShortInverse_inclusion_homology :
    ShortComplex.homologyMap (smallZeroShortInverse incidence negative) ≫
      ShortComplex.homologyMap (smallZeroShortInclusion incidence negative) =
      𝟙 ((singularZeroShortComplex incidence negative).homology) := by
  rw [← ShortComplex.homologyMap_comp]
  have same := shortHomologyMap_eq_of_middle
    (smallZeroShortInverse incidence negative ≫ smallZeroShortInclusion incidence negative)
    (𝟙 (singularZeroShortComplex incidence negative)) (smallVertexChainInverse_inclusion incidence negative)
  rw [same, ShortComplex.homologyMap_id]

noncomputable def smallZeroShortHomologyIso :
    (smallZeroShortComplex incidence negative).homology ≅
      (singularZeroShortComplex incidence negative).homology where
  hom := ShortComplex.homologyMap (smallZeroShortInclusion incidence negative)
  inv := ShortComplex.homologyMap (smallZeroShortInverse incidence negative)
  hom_inv_id := smallZeroShortInclusion_inverse_homology incidence negative
  inv_hom_id := smallZeroShortInverse_inclusion_homology incidence negative

omit [Finite Chart] in
theorem smallSingularChainInclusion_quasiIsoAt_zero :
    QuasiIsoAt (smallSingularChainInclusion incidence negative) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff]
  exact inferInstanceAs (IsIso (smallZeroShortHomologyIso incidence negative).hom)

end BondalThomsen.ConvexNerveSmallChainQuasiIso
