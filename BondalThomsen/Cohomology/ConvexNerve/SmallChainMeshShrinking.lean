module

public import BondalThomsen.Cohomology.ConvexNerve.SmallChainPositiveComparison
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveAcyclicCarrierAssembly
open BondalThomsen.ConvexNerveSmallSingularComparison
open BondalThomsen.ConvexNerveSmallChainQuasiIso
open BondalThomsen.ConvexNerveSmallChainPositiveComparison
open scoped Classical Simplicial BigOperators

attribute [local instance] Classical.decEq simplexMetricSpace

namespace BondalThomsen.ConvexNerveSmallChainMeshShrinking

noncomputable def contractionFactor (dimension : ℕ) : ℝ :=
  (dimension : ℝ) / (dimension + 1)

theorem contractionFactor_nonneg (dimension : ℕ) :
    0 ≤ contractionFactor dimension := by
  unfold contractionFactor
  positivity

theorem contractionFactor_lt_one (dimension : ℕ) :
    contractionFactor dimension < 1 := by
  unfold contractionFactor
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg dimension : (0 : ℝ) ≤ dimension)]

theorem ratio_le_contractionFactor {initialSegment dimension : ℕ} (bound : initialSegment ≤ dimension) :
    (initialSegment : ℝ) / (initialSegment + 1) ≤ contractionFactor dimension := by
  rw [contractionFactor, div_le_div_iff₀] <;> norm_cast <;> nlinarith

section Normed

variable {Point : Type*} [NormedAddCommGroup Point] [NormedSpace ℝ Point]

noncomputable def stepVertices (dimension : ℕ) (tuple : Fin (dimension + 1) → Point)
    (ordering : Equiv.Perm (Fin (dimension + 1))) : Fin (dimension + 1) → Point :=
  fun initialSegment => ((initialSegment.val + 1 : ℝ))⁻¹ •
    ∑ column ∈ Finset.Iic initialSegment, tuple (ordering column)

omit [NormedSpace ℝ Point] in
theorem isBounded_range (dimension : ℕ) (tuple : Fin (dimension + 1) → Point) :
    Bornology.IsBounded (Set.range tuple) :=
  (Set.finite_range tuple).isBounded

theorem dist_vertex_step_le (dimension : ℕ) (tuple : Fin (dimension + 1) → Point)
    (ordering : Equiv.Perm (Fin (dimension + 1))) (initialSegment column : Fin (dimension + 1))
    (present : column ≤ initialSegment) :
    dist (tuple (ordering column)) (stepVertices dimension tuple ordering initialSegment) ≤
      (initialSegment.val : ℝ) / (initialSegment.val + 1) * Metric.diam (Set.range tuple) := by
  have difference : tuple (ordering column) - stepVertices dimension tuple ordering initialSegment =
      (initialSegment.val + 1 : ℝ)⁻¹ • ∑ index ∈ Finset.Iic initialSegment,
        (tuple (ordering column) - tuple (ordering index)) := by
    simp [stepVertices]
    simp [smul_sub, ← Nat.cast_smul_eq_nsmul ℝ]
    rw [inv_smul_smul₀ (Nat.cast_add_one_ne_zero _)]
  have normBound : ‖∑ index ∈ Finset.Iic initialSegment,
      (tuple (ordering column) - tuple (ordering index))‖ ≤
      initialSegment.val * Metric.diam (Set.range tuple) := by
    have termBound : ∀ index ∈ (Finset.Iic initialSegment).erase column,
        ‖tuple (ordering column) - tuple (ordering index)‖ ≤ Metric.diam (Set.range tuple) := by
      intro index _present
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem (isBounded_range dimension tuple)
        (Set.mem_range_self (ordering column)) (Set.mem_range_self (ordering index))
    have triangle := norm_sum_le (Finset.Iic initialSegment)
      (fun index => tuple (ordering column) - tuple (ordering index))
    have zeroTerm : ‖tuple (ordering column) - tuple (ordering column)‖ = 0 := by simp
    have eraseSum : ∑ index ∈ Finset.Iic initialSegment,
        ‖tuple (ordering column) - tuple (ordering index)‖ =
        ∑ index ∈ (Finset.Iic initialSegment).erase column,
          ‖tuple (ordering column) - tuple (ordering index)‖ := by
      rw [← Finset.sum_erase (Finset.Iic initialSegment) zeroTerm]
    have cardinality : ((Finset.Iic initialSegment).erase column).card = initialSegment.val := by
      rw [Finset.card_erase_of_mem (Finset.mem_Iic.mpr present), Fin.card_Iic,
        Nat.add_sub_cancel]
    have sumBound : ∑ index ∈ (Finset.Iic initialSegment).erase column,
        ‖tuple (ordering column) - tuple (ordering index)‖ ≤
        initialSegment.val * Metric.diam (Set.range tuple) := by
      have estimate := Finset.sum_le_card_nsmul ((Finset.Iic initialSegment).erase column)
        (fun index => ‖tuple (ordering column) - tuple (ordering index)‖)
        (Metric.diam (Set.range tuple)) (fun index included => termBound index included)
      rwa [cardinality, nsmul_eq_mul] at estimate
    linarith
  rw [dist_eq_norm, difference, norm_smul, Real.norm_of_nonneg (by positivity)]
  have inverseNonnegative : 0 ≤ (initialSegment.val + 1 : ℝ)⁻¹ := by positivity
  have estimate := mul_le_mul_of_nonneg_left normBound inverseNonnegative
  have normalization : (initialSegment.val + 1 : ℝ)⁻¹ *
      (initialSegment.val * Metric.diam (Set.range tuple)) =
      (initialSegment.val : ℝ) / (initialSegment.val + 1) * Metric.diam (Set.range tuple) := by ring
  linarith

theorem dist_step_step_le_aux (dimension : ℕ) (tuple : Fin (dimension + 1) → Point)
    (ordering : Equiv.Perm (Fin (dimension + 1))) (first second : Fin (dimension + 1))
    (nested : first ≤ second) :
    dist (stepVertices dimension tuple ordering first)
      (stepVertices dimension tuple ordering second) ≤
      (second.val : ℝ) / (second.val + 1) * Metric.diam (Set.range tuple) := by
  set diameter := Metric.diam (Set.range tuple)
  set initialSegment := Finset.Iic first
  have cardinality : initialSegment.card = first.val + 1 := by simp [initialSegment]
  have difference : stepVertices dimension tuple ordering first -
      stepVertices dimension tuple ordering second =
      (first.val + 1 : ℝ)⁻¹ • ∑ column ∈ initialSegment,
        (tuple (ordering column) - stepVertices dimension tuple ordering second) := by
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, cardinality,
      ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one,
      inv_smul_smul₀ (by positivity : (first.val : ℝ) + 1 ≠ 0)]
    rfl
  have termBound : ∀ column ∈ initialSegment,
      ‖tuple (ordering column) - stepVertices dimension tuple ordering second‖ ≤
      (second.val : ℝ) / (second.val + 1) * diameter := by
    intro column included
    have estimate := dist_vertex_step_le dimension tuple ordering second column
      (le_trans (Finset.mem_Iic.mp included) nested)
    simpa [dist_eq_norm] using estimate
  rw [dist_eq_norm, difference, norm_smul, Real.norm_of_nonneg (by positivity)]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)) ?_
  have sumBound := mul_le_mul_of_nonneg_left (Finset.sum_le_sum termBound)
    (by positivity : 0 ≤ (first.val + 1 : ℝ)⁻¹)
  refine le_trans sumBound ?_
  simp only [Finset.sum_const, nsmul_eq_mul, cardinality]
  push_cast
  have nonzero : (first.val + 1 : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]

theorem dist_step_step_le (dimension : ℕ) (tuple : Fin (dimension + 1) → Point)
    (ordering : Equiv.Perm (Fin (dimension + 1))) (first second : Fin (dimension + 1)) :
    dist (stepVertices dimension tuple ordering first)
      (stepVertices dimension tuple ordering second) ≤
      contractionFactor dimension * Metric.diam (Set.range tuple) := by
  by_cases nested : first ≤ second
  · refine le_trans (dist_step_step_le_aux dimension tuple ordering first second nested) ?_
    exact mul_le_mul_of_nonneg_right
      (ratio_le_contractionFactor (Nat.le_of_lt_succ second.isLt)) Metric.diam_nonneg
  · rw [dist_comm]
    refine le_trans (dist_step_step_le_aux dimension tuple ordering second first
      (le_of_not_ge nested)) ?_
    exact mul_le_mul_of_nonneg_right
      (ratio_le_contractionFactor (Nat.le_of_lt_succ first.isLt)) Metric.diam_nonneg

theorem stepVertices_diam_le (dimension : ℕ) (tuple : Fin (dimension + 1) → Point)
    (ordering : Equiv.Perm (Fin (dimension + 1))) :
    Metric.diam (Set.range (stepVertices dimension tuple ordering)) ≤
      contractionFactor dimension * Metric.diam (Set.range tuple) := by
  refine Metric.diam_le_of_forall_dist_le
    (mul_nonneg (contractionFactor_nonneg dimension) Metric.diam_nonneg) ?_
  rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩
  exact dist_step_step_le dimension tuple ordering first second

end Normed

noncomputable def stdVerts (dimension : ℕ) : Fin (dimension + 1) → (Fin (dimension + 1) → ℝ) :=
  fun column => Pi.single column 1

theorem diam_range_stdVerts_le_one (dimension : ℕ) :
    Metric.diam (Set.range (stdVerts dimension)) ≤ 1 := by
  refine le_trans (Metric.diam_mono ?_
    (Convexity.StdSimplex.isBounded_range_toFun_comp_weights (Fin (dimension + 1))))
    (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall (Fin (dimension + 1)))
  rintro _ ⟨column, rfl⟩
  refine ⟨Convexity.StdSimplex.single column, ?_⟩
  funext index
  simp [stdVerts, Pi.single_apply, Finsupp.single_apply, eq_comm]

section SmallPreservation

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

@[implicit_reducible] noncomputable def smallAffineSingularMap {ambient : ℕ}
    (simplex : (openStarSmallSet incidence negative) _⦋ambient⦌) :
    affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1))) ⟶
      openStarSmallSet incidence negative where
  app degree := ↾fun tuple => ⟨(TopCat.toSSetObjEquiv _ _).symm
    ((singularSimplexMap incidence negative (.op ⦋ambient⦌) simplex.val).comp
      (affineTupleSimplex ambient degree.unop.len tuple)), by
        obtain ⟨vertex, positive⟩ := simplex.property
        exact ⟨vertex, fun point => positive (affineTupleSimplex ambient degree.unop.len tuple point)⟩⟩
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro point
    change singularSimplexMap incidence negative (.op ⦋ambient⦌) simplex.val
      (affineTupleSimplex ambient target.unop.len (tuple ∘ selection.unop.toOrderHom) point) =
      singularSimplexMap incidence negative (.op ⦋ambient⦌) simplex.val
      (affineTupleSimplex ambient source.unop.len tuple (point.map selection.unop.toOrderHom))
    rw [affineTupleSimplex_precomp]

noncomputable def smallAffineEvaluation {ambient : ℕ}
    (simplex : (openStarSmallSet incidence negative) _⦋ambient⦌) :
    affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1))) ⟶
      (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) :=
  SSet.chainComplexMap (smallAffineSingularMap incidence negative simplex) (AddCommGrpCat.of ℤ)

omit [Finite Chart] in
theorem smallAffineEvaluation_inclusion {ambient : ℕ}
    (simplex : (openStarSmallSet incidence negative) _⦋ambient⦌) :
    smallAffineEvaluation incidence negative simplex ≫ smallSingularChainInclusion incidence negative =
      affineTupleEvaluation (singularSimplexMap incidence negative (.op ⦋ambient⦌) simplex.val) := by
  apply HomologicalComplex.Hom.ext
  funext degree
  apply SSet.chainComplex_hom_ext
  intro tuple
  change _ ≫ ((smallAffineEvaluation incidence negative simplex).f degree ≫
    (smallSingularChainInclusion incidence negative).f degree) = _
  rw [← Category.assoc]
  unfold smallAffineEvaluation smallSingularChainInclusion
  rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f, affineTupleEvaluation_generator]
  change (incidenceSingularSet incidence negative).ιChainComplex
    (R := AddCommGrpCat.of ℤ) _ = (incidenceSingularSet incidence negative).ιChainComplex _
  congr 1

noncomputable def smallSubdivisionComponent (degree : ℕ) :
    ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X degree :=
  Sigma.desc fun simplex =>
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 1)))).ιChainComplex
      (standardAffineTuple degree) ≫ (affineBarycentricSubdivision degree).f degree ≫
        (smallAffineEvaluation incidence negative simplex).f degree

noncomputable def smallSubdivisionHomotopyComponent (degree : ℕ) :
    ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X (degree + 1) :=
  Sigma.desc fun simplex =>
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 1)))).ιChainComplex
      (standardAffineTuple degree) ≫ affineSubdivisionHomotopyValues degree degree ≫
        (smallAffineEvaluation incidence negative simplex).f (degree + 1)

omit [Finite Chart] in
theorem smallSubdivisionComponent_inclusion (degree : ℕ) :
    smallSubdivisionComponent incidence negative degree ≫
      (smallSingularChainInclusion incidence negative).f degree =
    (smallSingularChainInclusion incidence negative).f degree ≫
      (singularBarycentricSubdivision
        (Space := incidenceRealization incidence negative)).f degree := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  dsimp only [smallSubdivisionComponent]
  rw [← Category.assoc]
  rw [← Category.assoc]
  simp only [SSet.ιChainComplex, Sigma.ι_comp_desc]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, smallAffineEvaluation_inclusion]
  change _ = (openStarSmallSet incidence negative).ιChainComplex simplex ≫
    ((SSet.chainComplexMap (openStarSmallSubcomplex incidence negative).ι
      (AddCommGrpCat.of ℤ)).f degree ≫ singularSubdivisionComponent degree)
  conv_rhs => rw [← Category.assoc, SSet.ι_chainComplexMap_f, singularSubdivisionComponent_generator]
  rfl

omit [Finite Chart] in
theorem smallSubdivisionHomotopyComponent_inclusion (degree : ℕ) :
    smallSubdivisionHomotopyComponent incidence negative degree ≫
      (smallSingularChainInclusion incidence negative).f (degree + 1) =
    (smallSingularChainInclusion incidence negative).f degree ≫
      singularSubdivisionHomotopyComponent
        (Space := incidenceRealization incidence negative) degree := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  dsimp only [smallSubdivisionHomotopyComponent]
  rw [← Category.assoc]
  rw [← Category.assoc]
  simp only [SSet.ιChainComplex, Sigma.ι_comp_desc]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, smallAffineEvaluation_inclusion]
  change _ = (openStarSmallSet incidence negative).ιChainComplex simplex ≫
    ((SSet.chainComplexMap (openStarSmallSubcomplex incidence negative).ι
      (AddCommGrpCat.of ℤ)).f degree ≫ singularSubdivisionHomotopyComponent degree)
  conv_rhs => rw [← Category.assoc, SSet.ι_chainComplexMap_f, singularSubdivisionHomotopyComponent_generator]
  rfl

noncomputable def smallBarycentricSubdivision :
    (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ) where
  f := smallSubdivisionComponent incidence negative
  comm' source target _related := by
    have mono := smallSingularChainInclusion_mono incidence negative target
    apply (cancel_mono ((smallSingularChainInclusion incidence negative).f target)).mp
    simp only [Category.assoc]
    rw [← (smallSingularChainInclusion incidence negative).comm source target]
    rw [← Category.assoc, smallSubdivisionComponent_inclusion,
      Category.assoc, (singularBarycentricSubdivision
        (Space := incidenceRealization incidence negative)).comm source target]
    rw [smallSubdivisionComponent_inclusion]
    rw [reassoc_of% (smallSingularChainInclusion incidence negative).comm source target]

omit [Finite Chart] in
theorem smallBarycentricSubdivision_inclusion :
    smallBarycentricSubdivision incidence negative ≫ smallSingularChainInclusion incidence negative =
      smallSingularChainInclusion incidence negative ≫
        singularBarycentricSubdivision (Space := incidenceRealization incidence negative) := by
  apply HomologicalComplex.Hom.ext
  funext degree
  exact smallSubdivisionComponent_inclusion incidence negative degree

omit [Finite Chart] in
theorem smallSubdivisionHomotopyComponent_zero :
    smallSubdivisionHomotopyComponent incidence negative 0 = 0 := by
  have mono := smallSingularChainInclusion_mono incidence negative 1
  apply (cancel_mono ((smallSingularChainInclusion incidence negative).f 1)).mp
  rw [smallSubdivisionHomotopyComponent_inclusion, singularSubdivisionHomotopyComponent_zero]
  simp

omit [Finite Chart] in
theorem smallBarycentricSubdivision_zero :
    (smallBarycentricSubdivision incidence negative).f 0 = 𝟙 _ := by
  have mono := smallSingularChainInclusion_mono incidence negative 0
  apply (cancel_mono ((smallSingularChainInclusion incidence negative).f 0)).mp
  change smallSubdivisionComponent incidence negative 0 ≫ _ = _
  rw [smallSubdivisionComponent_inclusion, singularBarycentricSubdivision_zero]
  simp

omit [Finite Chart] in
theorem smallSubdivisionHomotopyComponent_boundary (degree : ℕ) :
    smallSubdivisionHomotopyComponent incidence negative (degree + 1) ≫
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d
        (degree + 2) (degree + 1) =
    𝟙 _ - (smallBarycentricSubdivision incidence negative).f (degree + 1) -
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d
        (degree + 1) degree ≫ smallSubdivisionHomotopyComponent incidence negative degree := by
  have mono := smallSingularChainInclusion_mono incidence negative (degree + 1)
  apply (cancel_mono ((smallSingularChainInclusion incidence negative).f (degree + 1))).mp
  simp only [sub_comp, Category.id_comp, Category.assoc]
  rw [← (smallSingularChainInclusion incidence negative).comm (degree + 2) (degree + 1)]
  rw [← Category.assoc, smallSubdivisionHomotopyComponent_inclusion,
    Category.assoc, singularSubdivisionHomotopyComponent_boundary]
  simp only [comp_sub, Category.comp_id]
  rw [smallSubdivisionHomotopyComponent_inclusion]
  change _ = _ - smallSubdivisionComponent incidence negative (degree + 1) ≫ _ - _
  rw [smallSubdivisionComponent_inclusion,
    reassoc_of% (smallSingularChainInclusion incidence negative).comm (degree + 1) degree]

noncomputable def smallSubdivisionChainHomotopy :
    Homotopy (𝟙 ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)))
      (smallBarycentricSubdivision incidence negative) where
  hom degree := Pi.single (degree + 1) (smallSubdivisionHomotopyComponent incidence negative degree)
  zero source target unrelated := Pi.single_eq_of_ne (Ne.symm unrelated) _
  comm degree := by
    cases degree with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
        simp [smallSubdivisionHomotopyComponent_zero, smallBarycentricSubdivision_zero]
    | succ degree =>
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        simp only [Pi.single_eq_same]
        rw [smallSubdivisionHomotopyComponent_boundary]
        change 𝟙 _ = _
        abel

end SmallPreservation

section IteratedSmallPreservation

noncomputable def chainMapIterates {complex : ChainComplex AddCommGrpCat.{0} ℕ}
    (mapping : complex ⟶ complex) (iterations : ℕ) : complex ⟶ complex :=
  Nat.rec (𝟙 complex) (fun _iterations previous => previous ≫ mapping) iterations

@[simp] theorem chainMapIterates_zero {complex : ChainComplex AddCommGrpCat.{0} ℕ}
    (mapping : complex ⟶ complex) : chainMapIterates mapping 0 = 𝟙 complex := rfl

theorem chainMapIterates_succ {complex : ChainComplex AddCommGrpCat.{0} ℕ}
    (mapping : complex ⟶ complex) (iterations : ℕ) :
    chainMapIterates mapping (iterations + 1) = chainMapIterates mapping iterations ≫ mapping := rfl

noncomputable def chainMapIteratesHomotopy {complex : ChainComplex AddCommGrpCat.{0} ℕ}
    {mapping : complex ⟶ complex} (homotopy : Homotopy (𝟙 complex) mapping) (iterations : ℕ) :
    Homotopy (𝟙 complex) (chainMapIterates mapping iterations) :=
  Nat.rec (Homotopy.refl (𝟙 complex))
    (fun iterations previous => previous.trans
      ((Homotopy.ofEq (Category.comp_id (chainMapIterates mapping iterations)).symm).trans
        (homotopy.compLeft (chainMapIterates mapping iterations)))) iterations

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable abbrev smallIteratedSubdivision (iterations : ℕ) :=
  chainMapIterates (smallBarycentricSubdivision incidence negative) iterations

noncomputable abbrev singularIteratedSubdivision (iterations : ℕ) :=
  chainMapIterates (singularBarycentricSubdivision
    (Space := incidenceRealization incidence negative)) iterations

omit [Finite Chart] in
theorem smallIteratedSubdivision_inclusion (iterations : ℕ) :
    smallIteratedSubdivision incidence negative iterations ≫ smallSingularChainInclusion incidence negative =
      smallSingularChainInclusion incidence negative ≫ singularIteratedSubdivision incidence negative iterations := by
  induction iterations with
  | zero => simp [smallIteratedSubdivision, singularIteratedSubdivision]
  | succ iterations induction =>
      change (smallIteratedSubdivision incidence negative iterations ≫
        smallBarycentricSubdivision incidence negative) ≫ _ = _ ≫
          (singularIteratedSubdivision incidence negative iterations ≫ _)
      rw [Category.assoc, smallBarycentricSubdivision_inclusion,
        ← Category.assoc, induction, Category.assoc]

noncomputable abbrev smallIteratedSubdivisionHomotopy (iterations : ℕ) :=
  chainMapIteratesHomotopy (smallSubdivisionChainHomotopy incidence negative) iterations

noncomputable abbrev singularIteratedSubdivisionHomotopy (iterations : ℕ) :=
  chainMapIteratesHomotopy (singularSubdivisionChainHomotopy
    (Space := incidenceRealization incidence negative)) iterations

end IteratedSmallPreservation

section ModernSimplexMesh

noncomputable def simplexCoordinates (dimension : ℕ)
    (point : Convexity.StdSimplex ℝ (Fin (dimension + 1))) : Fin (dimension + 1) → ℝ :=
  point.weights

theorem simplexCoordinates_affineTuple (ambient degree : ℕ)
    (tuple : Fin (degree + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (point : Convexity.StdSimplex ℝ (Fin (degree + 1))) :
    simplexCoordinates ambient (affineTupleSimplex ambient degree tuple point) =
      ∑ column, point.weights column • simplexCoordinates ambient (tuple column) := by
  change ⇑((Convexity.StdSimplex.affineMapMk (R := ℝ) tuple point).weights) = _
  rw [Convexity.StdSimplex.affineMapMk_apply,
    (Convexity.StdSimplex.isAffineMap_weights ℝ (Fin (ambient + 1))).map_iConvexComb,
    Convexity.iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finsupp.coe_finsetSum, Finsupp.coe_smul, Function.comp_apply, simplexCoordinates]

theorem subBarycenter_weights (dimension : ℕ) (initialSegment : Finset (Fin (dimension + 1)))
    (nonempty : initialSegment.Nonempty) (column : Fin (dimension + 1)) :
    (Convexity.StdSimplex.subBarycenter (K := ℝ) initialSegment nonempty).weights column =
      if column ∈ initialSegment then (initialSegment.card : ℝ)⁻¹ else 0 := by
  simp [Convexity.StdSimplex.weights_subBarycenter, Finsupp.single_apply, eq_comm]

theorem affineTupleSimplex_coordinates_mem_convexHull (ambient degree : ℕ)
    (tuple : Fin (degree + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (point : Convexity.StdSimplex ℝ (Fin (degree + 1))) :
    simplexCoordinates ambient (affineTupleSimplex ambient degree tuple point) ∈
      convexHull ℝ (Set.range (simplexCoordinates ambient ∘ tuple)) := by
  rw [simplexCoordinates_affineTuple]
  apply (convex_convexHull ℝ _).sum_mem
  · intro column _included
    exact point.weights_nonneg column
  · have total := point.total
    rw [Finsupp.sum_fintype _ _ (by simp)] at total
    exact total
  · intro column _included
    exact subset_convexHull ℝ _ (Set.mem_range_self column)

theorem simplex_dist_coordinates (dimension : ℕ)
    (first second : Convexity.StdSimplex ℝ (Fin (dimension + 1))) :
    dist first second = dist (simplexCoordinates dimension first) (simplexCoordinates dimension second) :=
  rfl

end ModernSimplexMesh

end BondalThomsen.ConvexNerveSmallChainMeshShrinking
