module

public import BondalThomsen.Cohomology.ConvexNerve.SmallChainMeshShrinking
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup

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
open BondalThomsen.ConvexNerveSmallChainMeshShrinking
open scoped Classical Simplicial BigOperators

attribute [local instance] Classical.decEq simplexMetricSpace

namespace BondalThomsen.ConvexNerveSubdivisionCellExpansion

@[implicit_reducible] def CellFlag (dimension : ℕ) : Type :=
  Nat.rec Unit (fun dimension previous => Fin (dimension + 2) × previous) dimension

noncomputable instance cellFlagFintype (dimension : ℕ) : Fintype (CellFlag dimension) :=
  Nat.rec (inferInstanceAs (Fintype Unit))
    (fun dimension previous => @instFintypeProd (Fin (dimension + 2)) _ inferInstance previous) dimension

noncomputable def extendOrdering {dimension : ℕ} (deleted : Fin (dimension + 2))
    (ordering : Equiv.Perm (Fin (dimension + 1))) : Equiv.Perm (Fin (dimension + 2)) :=
  (finSuccEquiv' (Fin.last (dimension + 1))).trans
    ((Equiv.optionCongr ordering).trans (finSuccEquiv' deleted).symm)

@[simp] theorem extendOrdering_castSucc {dimension : ℕ} (deleted : Fin (dimension + 2))
    (ordering : Equiv.Perm (Fin (dimension + 1))) (column : Fin (dimension + 1)) :
    extendOrdering deleted ordering column.castSucc = deleted.succAbove (ordering column) := by
  change (finSuccEquiv' deleted).symm
    ((Equiv.optionCongr ordering) ((finSuccEquiv' (Fin.last (dimension + 1))) column.castSucc)) = _
  rw [← Fin.succAbove_last_apply column, finSuccEquiv'_succAbove]
  simp

noncomputable def flagOrdering (dimension : ℕ) : CellFlag dimension → Equiv.Perm (Fin (dimension + 1)) :=
  Nat.rec (fun _flag => Equiv.refl _)
    (fun _dimension previous flag => extendOrdering flag.1 (previous flag.2)) dimension

def flagSign (dimension : ℕ) : CellFlag dimension → ℤ :=
  Nat.rec (fun _flag => 1)
    (fun _dimension previous flag => (-1 : ℤ) ^ flag.1.val * previous flag.2) dimension

noncomputable def flagVertices (ambient : ℕ) : (dimension : ℕ) →
    (Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) →
    CellFlag dimension → (Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :=
  fun dimension => Nat.rec (fun tuple _flag => tuple)
    (fun dimension previous tuple flag =>
      Fin.cons (affineTupleBarycenter ambient (dimension + 1) tuple)
        (previous (tuple ∘ flag.1.succAbove) flag.2)) dimension

theorem affineSubdivision_flag_expansion (ambient dimension : ℕ)
    (tuple : Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex
      (R := AddCommGrpCat.of ℤ) tuple ≫ (affineBarycentricSubdivision ambient).f dimension =
    ∑ flag : CellFlag dimension, flagSign dimension flag •
      (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex
        (flagVertices ambient dimension tuple flag) := by
  induction dimension with
  | zero =>
      change _ ≫ 𝟙 _ = _
      simp [flagSign, flagVertices, CellFlag]
  | succ dimension induction =>
      change _ ≫ affineSubdivisionComponents ambient (dimension + 1) = _
      rw [affineSubdivisionComponents_generator]
      rw [← Category.assoc, ← Category.assoc, SSet.ιChainComplex_d]
      simp only [sum_comp, zsmul_comp, Category.assoc]
      simp_rw [← Category.assoc, show affineSubdivisionComponents ambient dimension =
        (affineBarycentricSubdivision ambient).f dimension from rfl, induction]
      simp only [sum_comp, zsmul_comp, affineTupleCone_generator]
      change _ = ∑ flag : Fin (dimension + 2) × CellFlag dimension,
        ((-1 : ℤ) ^ flag.1.val * flagSign dimension flag.2) •
          (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex
            (Fin.cons (affineTupleBarycenter ambient (dimension + 1) tuple)
              (flagVertices ambient dimension (tuple ∘ flag.1.succAbove) flag.2))
      rw [Fintype.sum_prod_type]
      simp only [Finset.smul_sum, smul_smul]
      rfl

noncomputable def prefixVertices (ambient dimension : ℕ)
    (tuple : Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (ordering : Equiv.Perm (Fin (dimension + 1))) :
    Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)) :=
  fun initialSegment => Convexity.StdSimplex.affineMapMk (R := ℝ) (tuple ∘ ordering)
    (Convexity.StdSimplex.subBarycenter (Finset.Iic initialSegment)
      ⟨initialSegment, Finset.mem_Iic.mpr le_rfl⟩)

theorem prefixVertices_coordinates (ambient dimension : ℕ)
    (tuple : Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (ordering : Equiv.Perm (Fin (dimension + 1))) :
    simplexCoordinates ambient ∘ prefixVertices ambient dimension tuple ordering =
      stepVertices dimension (simplexCoordinates ambient ∘ tuple) ordering := by
  funext initialSegment
  change simplexCoordinates ambient (affineTupleSimplex ambient dimension (tuple ∘ ordering)
    (Convexity.StdSimplex.subBarycenter (Finset.Iic initialSegment)
      ⟨initialSegment, Finset.mem_Iic.mpr le_rfl⟩)) = _
  rw [simplexCoordinates_affineTuple]
  simp only [subBarycenter_weights, Fin.card_Iic, Nat.cast_add, Nat.cast_one,
    ite_smul, zero_smul, Function.comp_apply, stepVertices, Finset.smul_sum]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext column
    simp
  · intro column _included
    rfl

theorem prefixVertices_last (ambient dimension : ℕ)
    (tuple : Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (ordering : Equiv.Perm (Fin (dimension + 1))) :
    prefixVertices ambient dimension tuple ordering (Fin.last dimension) =
      affineTupleBarycenter ambient dimension tuple := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro column
  have coordinates := congrFun
    (prefixVertices_coordinates ambient dimension tuple ordering) (Fin.last dimension)
  have barycenter := simplexCoordinates_affineTuple ambient dimension tuple
    (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (dimension + 1)))
  change (prefixVertices ambient dimension tuple ordering (Fin.last dimension)).weights column =
    (affineTupleSimplex ambient dimension tuple
      (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (dimension + 1)))).weights column
  change simplexCoordinates ambient (prefixVertices ambient dimension tuple ordering
    (Fin.last dimension)) column = simplexCoordinates ambient _ column
  dsimp only [Function.comp_apply] at coordinates
  rw [coordinates, barycenter]
  simp only [stepVertices, Fin.val_last,
    Convexity.StdSimplex.weights_barycenter_apply, Fintype.card_fin,
    Function.comp_apply, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply]
  have interval : Finset.Iic (Fin.last dimension) = Finset.univ := by
    ext index
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    exact Fin.le_last index
  rw [interval]
  simpa only [Finset.sum_apply, Pi.smul_apply, Finset.Iic_top, Nat.cast_add,
    Nat.cast_one] using congrArg (fun value : Fin (ambient + 1) → ℝ => value column)
    ((Equiv.sum_comp ordering (fun index => ((dimension + 1 : ℕ) : ℝ)⁻¹ •
      simplexCoordinates ambient (tuple index))))

theorem prefixVertices_extend_castSucc (ambient dimension : ℕ)
    (tuple : Fin (dimension + 2) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (deleted : Fin (dimension + 2)) (ordering : Equiv.Perm (Fin (dimension + 1)))
    (column : Fin (dimension + 1)) :
    prefixVertices ambient (dimension + 1) tuple (extendOrdering deleted ordering) column.castSucc =
      prefixVertices ambient dimension (tuple ∘ deleted.succAbove) ordering column := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  have left := congrFun (prefixVertices_coordinates ambient (dimension + 1) tuple
    (extendOrdering deleted ordering)) column.castSucc
  have right := congrFun (prefixVertices_coordinates ambient dimension
    (tuple ∘ deleted.succAbove) ordering) column
  change (simplexCoordinates ambient _ : Fin (ambient + 1) → ℝ) coordinate =
    (simplexCoordinates ambient _) coordinate
  dsimp only [Function.comp_apply] at left right
  rw [left, right]
  simp only [stepVertices, Fin.val_castSucc, Fin.sum_Iic_castSucc,
    Function.comp_apply, extendOrdering_castSucc]

theorem flagVertices_rev_eq_prefix (ambient dimension : ℕ)
    (tuple : Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (flag : CellFlag dimension) :
    flagVertices ambient dimension tuple flag ∘ Fin.rev =
      prefixVertices ambient dimension tuple (flagOrdering dimension flag) := by
  induction dimension with
  | zero =>
      funext column
      fin_cases column
      have interval : (Finset.Iic (0 : Fin 1)) = {0} := by ext index; fin_cases index; simp
      simp [flagVertices, prefixVertices, flagOrdering, CellFlag, interval,
        Convexity.StdSimplex.subBarycenter_singleton]
  | succ dimension induction =>
      funext column
      cases column using Fin.lastCases with
      | last =>
          dsimp only [flagVertices, Function.comp_apply]
          simp only [Fin.rev_last, Fin.cons_zero]
          exact (prefixVertices_last ambient (dimension + 1) tuple (flagOrdering _ flag)).symm
      | cast column =>
          dsimp only [flagVertices, Function.comp_apply]
          simp only [Fin.rev_castSucc, Fin.cons_succ]
          change flagVertices ambient dimension (tuple ∘ flag.1.succAbove) flag.2 column.rev = _
          rw [show flagVertices ambient dimension (tuple ∘ flag.1.succAbove) flag.2 column.rev =
              prefixVertices ambient dimension (tuple ∘ flag.1.succAbove)
                (flagOrdering dimension flag.2) column from congrFun (induction _ flag.2) column]
          exact (prefixVertices_extend_castSucc ambient dimension tuple flag.1
            (flagOrdering dimension flag.2) column).symm

theorem simplexCoordinates_isometry (ambient : ℕ) : Isometry (simplexCoordinates ambient) :=
  Isometry.of_dist_eq fun first second => (simplex_dist_coordinates ambient first second).symm

theorem flagVertices_diameter_le (ambient dimension : ℕ)
    (tuple : Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (flag : CellFlag dimension) :
    Metric.diam (Set.range (flagVertices ambient dimension tuple flag)) ≤
      contractionFactor dimension * Metric.diam (Set.range tuple) := by
  have reversedRange : Set.range (flagVertices ambient dimension tuple flag ∘ Fin.rev) =
      Set.range (flagVertices ambient dimension tuple flag) := by
    ext point
    constructor
    · rintro ⟨column, rfl⟩
      exact ⟨column.rev, rfl⟩
    · rintro ⟨column, rfl⟩
      exact ⟨column.rev, by simp⟩
  rw [← reversedRange, flagVertices_rev_eq_prefix]
  rw [← (simplexCoordinates_isometry ambient).diam_image,
    ← (simplexCoordinates_isometry ambient).diam_image (Set.range tuple),
    ← Set.range_comp, ← Set.range_comp, prefixVertices_coordinates]
  exact stepVertices_diam_le dimension (simplexCoordinates ambient ∘ tuple) (flagOrdering dimension flag)

noncomputable def IteratedFlags (dimension : ℕ) (iterations : ℕ) : Type :=
  Nat.rec Unit (fun _iterations previous => previous × CellFlag dimension) iterations

noncomputable instance iteratedFlagsFintype (dimension iterations : ℕ) :
    Fintype (IteratedFlags dimension iterations) :=
  Nat.rec (inferInstanceAs (Fintype Unit))
    (fun _iterations previous => @instFintypeProd _ (CellFlag dimension) previous inferInstance) iterations

noncomputable def iteratedFlagSign (dimension iterations : ℕ) : IteratedFlags dimension iterations → ℤ :=
  Nat.rec (fun _flags => 1)
    (fun _iterations previous flags => previous flags.1 * flagSign dimension flags.2) iterations

noncomputable def iteratedFlagVertices (ambient dimension : ℕ) : (iterations : ℕ) →
    IteratedFlags dimension iterations →
    (Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) →
    (Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :=
  fun iterations => Nat.rec (fun _flags tuple => tuple)
    (fun _iterations previous flags tuple =>
      flagVertices ambient dimension (previous flags.1 tuple) flags.2) iterations

theorem affineSubdivision_iterated_flag_expansion (ambient dimension iterations : ℕ)
    (tuple : Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex
      (R := AddCommGrpCat.of ℤ) tuple ≫
        (chainMapIterates (affineBarycentricSubdivision ambient) iterations).f dimension =
    ∑ flags : IteratedFlags dimension iterations, iteratedFlagSign dimension iterations flags •
      (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex
        (iteratedFlagVertices ambient dimension iterations flags tuple) := by
  induction iterations with
  | zero => simp [chainMapIterates, iteratedFlagSign, iteratedFlagVertices, IteratedFlags]
  | succ iterations induction =>
      rw [chainMapIterates_succ, HomologicalComplex.comp_f, ← Category.assoc, induction]
      simp only [sum_comp, zsmul_comp, affineSubdivision_flag_expansion, Finset.smul_sum, smul_smul]
      change _ = ∑ flags : IteratedFlags dimension iterations × CellFlag dimension,
        (iteratedFlagSign dimension iterations flags.1 * flagSign dimension flags.2) •
          (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex
            (flagVertices ambient dimension
              (iteratedFlagVertices ambient dimension iterations flags.1 tuple) flags.2)
      rw [Fintype.sum_prod_type]

theorem iteratedFlagVertices_diameter_le (ambient dimension iterations : ℕ)
    (flags : IteratedFlags dimension iterations)
    (tuple : Fin (dimension + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    Metric.diam (Set.range (iteratedFlagVertices ambient dimension iterations flags tuple)) ≤
      contractionFactor dimension ^ iterations * Metric.diam (Set.range tuple) := by
  induction iterations with
  | zero => simp [iteratedFlagVertices]
  | succ iterations induction =>
      change Metric.diam (Set.range (flagVertices ambient dimension
        (iteratedFlagVertices ambient dimension iterations flags.1 tuple) flags.2)) ≤ _
      refine le_trans (flagVertices_diameter_le ambient dimension _ flags.2) ?_
      have estimate := mul_le_mul_of_nonneg_left (induction flags.1) (contractionFactor_nonneg dimension)
      rw [pow_succ', mul_assoc]
      exact estimate

theorem affineTupleEvaluation_subdivision {ambient : ℕ} {Space : Type} [TopologicalSpace Space]
    (mapping : C(Convexity.StdSimplex ℝ (Fin (ambient + 1)), Space)) :
    affineTupleEvaluation mapping ≫ singularBarycentricSubdivision =
      affineBarycentricSubdivision ambient ≫ affineTupleEvaluation mapping := by
  apply HomologicalComplex.Hom.ext
  funext dimension
  apply SSet.chainComplex_hom_ext
  intro tuple
  change _ ≫ ((affineTupleEvaluation mapping).f dimension ≫ singularSubdivisionComponent dimension) = _
  rw [← Category.assoc, affineTupleEvaluation_generator, singularSubdivisionComponent_generator]
  simp only [Equiv.apply_symm_apply]
  let selection := Convexity.StdSimplex.affineMapMk (R := ℝ) tuple
  have continuousSelection : Continuous selection := (affineTupleSimplex ambient dimension tuple).continuous
  have naturality := congrArg (fun chainmap => chainmap.f dimension)
    (affineTupleEvaluation_naturality mapping selection continuousSelection)
  rw [HomologicalComplex.comp_f] at naturality
  have mappingEquality : (⟨selection, continuousSelection⟩ :
      C(Convexity.StdSimplex ℝ (Fin (dimension + 1)),
        Convexity.StdSimplex ℝ (Fin (ambient + 1)))) = affineTupleSimplex ambient dimension tuple := by
    ext point
    rfl
  rw [mappingEquality] at naturality
  change _ = _ ≫ ((affineBarycentricSubdivision ambient).f dimension ≫
    (affineTupleEvaluation mapping).f dimension)
  rw [← naturality]
  simp only
  rw [reassoc_of% affineBarycentricSubdivision_naturality selection dimension]
  conv_lhs => rw [← Category.assoc, ← Category.assoc, affineTupleChainMap_generator]
  have tupleEquality : selection ∘ standardAffineTuple dimension = tuple := by
    funext column
    simp [selection, standardAffineTuple]
  rw [tupleEquality]
  simp only [Category.assoc]

theorem affineTupleEvaluation_iteratedSubdivision {ambient : ℕ} {Space : Type} [TopologicalSpace Space]
    (mapping : C(Convexity.StdSimplex ℝ (Fin (ambient + 1)), Space)) (iterations : ℕ) :
    affineTupleEvaluation mapping ≫ chainMapIterates (singularBarycentricSubdivision (Space := Space)) iterations =
      chainMapIterates (affineBarycentricSubdivision ambient) iterations ≫ affineTupleEvaluation mapping := by
  induction iterations with
  | zero => simp
  | succ iterations induction =>
      rw [chainMapIterates_succ, chainMapIterates_succ, ← Category.assoc, induction,
        Category.assoc, affineTupleEvaluation_subdivision, ← Category.assoc]

theorem singularSubdivision_iterated_flag_expansion {Space : Type} [TopologicalSpace Space]
    (dimension iterations : ℕ) (simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋dimension⦌) :
    (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
      (chainMapIterates (singularBarycentricSubdivision (Space := Space)) iterations).f dimension =
    ∑ flags : IteratedFlags dimension iterations, iteratedFlagSign dimension iterations flags •
      (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex
        ((TopCat.toSSetObjEquiv _ _).symm
          ((TopCat.toSSetObjEquiv _ _ simplex).comp (affineTupleSimplex dimension dimension
            (iteratedFlagVertices dimension dimension iterations flags (standardAffineTuple dimension))))) := by
  rw [← standardAffineTuple_evaluation dimension simplex]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, affineTupleEvaluation_iteratedSubdivision,
    HomologicalComplex.comp_f, ← Category.assoc, affineSubdivision_iterated_flag_expansion]
  simp only [sum_comp, zsmul_comp, affineTupleEvaluation_generator]

theorem standardAffineTuple_diameter_le_one (dimension : ℕ) :
    Metric.diam (Set.range (standardAffineTuple dimension)) ≤ 1 := by
  rw [← (simplexCoordinates_isometry dimension).diam_image, ← Set.range_comp]
  have coordinates : simplexCoordinates dimension ∘ standardAffineTuple dimension = stdVerts dimension := by
    funext column index
    simp [simplexCoordinates, standardAffineTuple, stdVerts, Finsupp.single_apply,
      Pi.single_apply, eq_comm]
  rw [coordinates]
  exact diam_range_stdVerts_le_one dimension

noncomputable def iteratedFlagCell (dimension iterations : ℕ)
    (flags : IteratedFlags dimension iterations) :
    C(Convexity.StdSimplex ℝ (Fin (dimension + 1)),
      Convexity.StdSimplex ℝ (Fin (dimension + 1))) :=
  affineTupleSimplex dimension dimension
    (iteratedFlagVertices dimension dimension iterations flags (standardAffineTuple dimension))

theorem iteratedFlagCell_range_ball (dimension iterations : ℕ)
    (flags : IteratedFlags dimension iterations) (radius : ℝ)
    (shrinking : contractionFactor dimension ^ iterations < radius) :
    Set.range (iteratedFlagCell dimension iterations flags) ⊆
      Metric.ball (iteratedFlagCell dimension iterations flags (Convexity.StdSimplex.single 0)) radius := by
  rintro _ ⟨point, rfl⟩
  rw [Metric.mem_ball, simplex_dist_coordinates]
  let tuple := iteratedFlagVertices dimension dimension iterations flags (standardAffineTuple dimension)
  have diameter := iteratedFlagVertices_diameter_le dimension dimension iterations flags (standardAffineTuple dimension)
  have estimate := Metric.dist_le_diam_of_mem
    (isBounded_convexHull.mpr (Set.finite_range (simplexCoordinates dimension ∘ tuple)).isBounded)
    (affineTupleSimplex_coordinates_mem_convexHull dimension dimension tuple point)
    (affineTupleSimplex_coordinates_mem_convexHull dimension dimension tuple (Convexity.StdSimplex.single 0))
  rw [convexHull_diam, Set.range_comp, (simplexCoordinates_isometry dimension).diam_image] at estimate
  exact lt_of_le_of_lt (le_trans estimate (le_trans diameter
    (mul_le_of_le_one_right (pow_nonneg (contractionFactor_nonneg dimension) iterations)
      (standardAffineTuple_diameter_le_one dimension)))) shrinking

section IncidenceSmallness

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable def iteratedFlagSimplex (dimension iterations : ℕ)
    (simplex : (incidenceSingularSet incidence negative) _⦋dimension⦌)
    (flags : IteratedFlags dimension iterations) :
    (incidenceSingularSet incidence negative) _⦋dimension⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm
    ((singularSimplexMap incidence negative (.op ⦋dimension⦌) simplex).comp
      (iteratedFlagCell dimension iterations flags))

omit [Finite Chart] in
theorem eventually_iteratedFlagSimplex_small (dimension : ℕ)
    (simplex : (incidenceSingularSet incidence negative) _⦋dimension⦌) :
    ∃ threshold : ℕ, ∀ iterations ≥ threshold, ∀ flags : IteratedFlags dimension iterations,
      IsOpenStarSmall incidence negative (.op ⦋dimension⦌)
        (iteratedFlagSimplex incidence negative dimension iterations simplex flags) := by
  obtain ⟨radius, positive, lebesgue⟩ := singularSimplex_lebesgueNumber incidence negative dimension simplex
  have convergence := tendsto_pow_atTop_nhds_zero_of_lt_one
    (contractionFactor_nonneg dimension) (contractionFactor_lt_one dimension)
  obtain ⟨threshold, shrinking⟩ := Filter.eventually_atTop.mp (convergence.eventually_lt_const positive)
  refine ⟨threshold, fun iterations later flags => ?_⟩
  exact sufficientlySmallSimplexMap_isSmall incidence negative simplex radius lebesgue
    (iteratedFlagCell dimension iterations flags)
    (iteratedFlagCell dimension iterations flags (Convexity.StdSimplex.single 0))
    (iteratedFlagCell_range_ball dimension iterations flags radius (shrinking iterations later))

omit [Finite Chart] in
theorem singularGenerator_eventually_subdivision_small_lift (dimension : ℕ)
    (simplex : (incidenceSingularSet incidence negative) _⦋dimension⦌) :
    ∃ threshold : ℕ, ∀ iterations ≥ threshold,
      ∃ smallChain : AddCommGrpCat.of ℤ ⟶
        ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X dimension,
        smallChain ≫ (smallSingularChainInclusion incidence negative).f dimension =
          (incidenceSingularSet incidence negative).ιChainComplex simplex ≫
            (singularIteratedSubdivision incidence negative iterations).f dimension := by
  obtain ⟨threshold, small⟩ := eventually_iteratedFlagSimplex_small incidence negative dimension simplex
  refine ⟨threshold, fun iterations later => ?_⟩
  refine ⟨∑ flags : IteratedFlags dimension iterations, iteratedFlagSign dimension iterations flags •
    (openStarSmallSet incidence negative).ιChainComplex
      ⟨iteratedFlagSimplex incidence negative dimension iterations simplex flags,
        small iterations later flags⟩, ?_⟩
  simp only [sum_comp, zsmul_comp]
  change (∑ flags : IteratedFlags dimension iterations, iteratedFlagSign dimension iterations flags •
    (openStarSmallSet incidence negative).ιChainComplex
      ⟨iteratedFlagSimplex incidence negative dimension iterations simplex flags,
        small iterations later flags⟩ ≫
        (SSet.chainComplexMap (openStarSmallSubcomplex incidence negative).ι (AddCommGrpCat.of ℤ)).f dimension) = _
  simp only [SSet.ι_chainComplexMap_f]
  rw [singularSubdivision_iterated_flag_expansion]
  apply Finset.sum_congr rfl
  intro flags _included
  rfl

end IncidenceSmallness

noncomputable def chainToFreeAbelian (simplices : SSet.{0}) (dimension : ℕ) :
    (simplices.chainComplex (AddCommGrpCat.of ℤ)).X dimension ⟶
      AddCommGrpCat.of (FreeAbelianGroup (simplices _⦋dimension⦌)) :=
  Sigma.desc fun simplex => AddCommGrpCat.ofHom
    (zmultiplesHom (FreeAbelianGroup (simplices _⦋dimension⦌)) (FreeAbelianGroup.of simplex))

noncomputable def freeAbelianToChain (simplices : SSet.{0}) (dimension : ℕ) :
    AddCommGrpCat.of (FreeAbelianGroup (simplices _⦋dimension⦌)) ⟶
      (simplices.chainComplex (AddCommGrpCat.of ℤ)).X dimension :=
  AddCommGrpCat.ofHom (FreeAbelianGroup.lift
    (fun simplex => (simplices.ιChainComplex (R := AddCommGrpCat.of ℤ) simplex).hom 1))

theorem chainToFreeAbelian_inverse (simplices : SSet.{0}) (dimension : ℕ) :
    chainToFreeAbelian simplices dimension ≫ freeAbelianToChain simplices dimension = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc]
  dsimp only [chainToFreeAbelian]
  simp only [SSet.ιChainComplex, Sigma.ι_comp_desc]
  apply AddCommGrpCat.int_hom_ext
  change (FreeAbelianGroup.lift
    (fun simplex => (simplices.ιChainComplex (R := AddCommGrpCat.of ℤ) simplex).hom 1))
      ((zmultiplesHom (FreeAbelianGroup (simplices _⦋dimension⦌)) (FreeAbelianGroup.of simplex)) 1) = _
  rw [zmultiplesHom_apply, one_zsmul, FreeAbelianGroup.lift_apply_of]
  rfl

theorem integralChain_finite_generator_sum (simplices : SSet.{0}) (dimension : ℕ)
    (chain : AddCommGrpCat.of ℤ ⟶ (simplices.chainComplex (AddCommGrpCat.of ℤ)).X dimension) :
    ∃ support : Finset (simplices _⦋dimension⦌), ∃ coefficients : simplices _⦋dimension⦌ → ℤ,
      chain = ∑ simplex ∈ support, coefficients simplex • simplices.ιChainComplex simplex := by
  let represented := (chainToFreeAbelian simplices dimension).hom (chain.hom 1)
  refine ⟨represented.support, fun simplex => (FreeAbelianGroup.coeff simplex) represented, ?_⟩
  apply AddCommGrpCat.int_hom_ext
  have inverse := congrArg (fun mapping => mapping.hom (chain.hom 1))
    (chainToFreeAbelian_inverse simplices dimension)
  change (freeAbelianToChain simplices dimension).hom represented = chain.hom 1 at inverse
  calc
    chain.hom 1 = (freeAbelianToChain simplices dimension).hom represented := inverse.symm
    _ = (freeAbelianToChain simplices dimension).hom
        (∑ simplex ∈ represented.support, (FreeAbelianGroup.coeff simplex) represented •
          FreeAbelianGroup.of simplex) :=
      congrArg (freeAbelianToChain simplices dimension).hom
        (FreeAbelianGroup.eq_sum_support_coeff_smul_of represented)
    _ = _ := by
      simp only [map_sum, map_zsmul]
      change (∑ simplex ∈ represented.support, (FreeAbelianGroup.coeff simplex) represented •
        (FreeAbelianGroup.lift
          (fun simplex => (simplices.ιChainComplex (R := AddCommGrpCat.of ℤ) simplex).hom 1))
            (FreeAbelianGroup.of simplex)) = _
      simp only [FreeAbelianGroup.lift_apply_of]
      change _ = (∑ simplex ∈ represented.support,
        (FreeAbelianGroup.coeff simplex) represented •
          simplices.ιChainComplex (R := AddCommGrpCat.of ℤ) simplex).hom 1
      change _ = (AddCommGrpCat.homAddEquiv
        (∑ simplex ∈ represented.support, (FreeAbelianGroup.coeff simplex) represented •
          simplices.ιChainComplex (R := AddCommGrpCat.of ℤ) simplex)) 1
      rw [map_sum]
      simp only [map_zsmul]
      simp
      rfl

section ArbitraryChainSmallness

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

omit [Finite Chart] in
theorem singularChain_eventually_subdivision_small_lift (dimension : ℕ)
    (chain : AddCommGrpCat.of ℤ ⟶
      (integralSingularChains (incidenceRealization incidence negative)).X dimension) :
    ∃ threshold : ℕ, ∀ iterations ≥ threshold,
      ∃ smallChain : AddCommGrpCat.of ℤ ⟶
        ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X dimension,
        smallChain ≫ (smallSingularChainInclusion incidence negative).f dimension =
          chain ≫ (singularIteratedSubdivision incidence negative iterations).f dimension := by
  obtain ⟨support, coefficients, expansion⟩ := integralChain_finite_generator_sum
    (incidenceSingularSet incidence negative) dimension chain
  have eventually : ∀ᶠ iterations in Filter.atTop, ∀ simplex ∈ support,
      ∃ smallChain : AddCommGrpCat.of ℤ ⟶
        ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X dimension,
        smallChain ≫ (smallSingularChainInclusion incidence negative).f dimension =
          (incidenceSingularSet incidence negative).ιChainComplex simplex ≫
            (singularIteratedSubdivision incidence negative iterations).f dimension := by
    apply (Finset.eventually_all support).mpr
    intro simplex _included
    exact Filter.eventually_atTop.mpr
      (singularGenerator_eventually_subdivision_small_lift incidence negative dimension simplex)
  obtain ⟨threshold, generators⟩ := Filter.eventually_atTop.mp eventually
  refine ⟨threshold, fun iterations later => ?_⟩
  let lifted : (simplex : (incidenceSingularSet incidence negative) _⦋dimension⦌) →
      simplex ∈ support → (AddCommGrpCat.of ℤ ⟶
        ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X dimension) :=
    fun simplex included => (generators iterations later simplex included).choose
  refine ⟨∑ simplex ∈ support.attach,
    coefficients simplex.val • lifted simplex.val simplex.property, ?_⟩
  rw [expansion]
  simp only [sum_comp, zsmul_comp]
  have liftEquality : ∀ simplex : {simplex // simplex ∈ support},
      lifted simplex.val simplex.property ≫ (smallSingularChainInclusion incidence negative).f dimension =
        (incidenceSingularSet incidence negative).ιChainComplex simplex.val ≫
          (singularIteratedSubdivision incidence negative iterations).f dimension := by
    intro simplex
    exact (generators iterations later simplex.val simplex.property).choose_spec
  simp_rw [liftEquality]
  exact Finset.sum_attach support
    (fun simplex => coefficients simplex •
      ((incidenceSingularSet incidence negative).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
        (singularIteratedSubdivision incidence negative iterations).f dimension))

end ArbitraryChainSmallness

theorem homotopy_cycle_boundary {complex : ChainComplex AddCommGrpCat.{0} ℕ}
    {mapping : complex ⟶ complex} (homotopy : Homotopy (𝟙 complex) mapping)
    (degree : ℕ) (cycle : AddCommGrpCat.of ℤ ⟶ complex.X (degree + 1))
    (closed : cycle ≫ complex.d (degree + 1) degree = 0) :
    cycle ≫ homotopy.hom (degree + 1) (degree + 2) ≫
      complex.d (degree + 2) (degree + 1) = cycle - cycle ≫ mapping.f (degree + 1) := by
  have equality := congrArg (fun morphism => cycle ≫ morphism) (homotopy.comm (degree + 1))
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at equality
  simp only [comp_add, HomologicalComplex.id_f, Category.comp_id, ← Category.assoc,
    closed, zero_comp] at equality
  apply eq_sub_iff_add_eq.mpr
  simpa only [Category.assoc, zero_add] using equality.symm

section PositiveCycleBoundaryComparison

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

omit [Finite Chart] in
theorem positiveSingularCycle_small_representative (degree : ℕ)
    (cycle : AddCommGrpCat.of ℤ ⟶
      (integralSingularChains (incidenceRealization incidence negative)).X (degree + 1))
    (closed : cycle ≫ (integralSingularChains (incidenceRealization incidence negative)).d
      (degree + 1) degree = 0) :
    ∃ smallCycle : AddCommGrpCat.of ℤ ⟶
        ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X (degree + 1),
      smallCycle ≫ ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d
        (degree + 1) degree = 0 ∧
      ∃ filling : AddCommGrpCat.of ℤ ⟶
        (integralSingularChains (incidenceRealization incidence negative)).X (degree + 2),
        filling ≫ (integralSingularChains (incidenceRealization incidence negative)).d
          (degree + 2) (degree + 1) =
        cycle - smallCycle ≫ (smallSingularChainInclusion incidence negative).f (degree + 1) := by
  obtain ⟨iterations, eventual⟩ := singularChain_eventually_subdivision_small_lift incidence negative (degree + 1) cycle
  obtain ⟨smallCycle, liftEquality⟩ := eventual iterations le_rfl
  refine ⟨smallCycle, ?_, cycle ≫
    (singularIteratedSubdivisionHomotopy incidence negative iterations).hom (degree + 1) (degree + 2), ?_⟩
  · have mono := smallSingularChainInclusion_mono incidence negative degree
    apply (cancel_mono ((smallSingularChainInclusion incidence negative).f degree)).mp
    rw [Category.assoc, ← (smallSingularChainInclusion incidence negative).comm (degree + 1) degree,
      ← Category.assoc, liftEquality, Category.assoc,
      (singularIteratedSubdivision incidence negative iterations).comm (degree + 1) degree,
      ← Category.assoc, closed]
    simp
  · rw [Category.assoc, homotopy_cycle_boundary (singularIteratedSubdivisionHomotopy incidence negative iterations) degree cycle closed,
      liftEquality]

omit [Finite Chart] in
theorem positiveSmallCycle_global_boundary_is_small_boundary (degree : ℕ)
    (cycle : AddCommGrpCat.of ℤ ⟶
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X (degree + 1))
    (closed : cycle ≫ ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d
      (degree + 1) degree = 0)
    (globalFilling : AddCommGrpCat.of ℤ ⟶
      (integralSingularChains (incidenceRealization incidence negative)).X (degree + 2))
    (bounds : globalFilling ≫ (integralSingularChains (incidenceRealization incidence negative)).d
      (degree + 2) (degree + 1) =
        cycle ≫ (smallSingularChainInclusion incidence negative).f (degree + 1)) :
    ∃ smallFilling : AddCommGrpCat.of ℤ ⟶
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).X (degree + 2),
      smallFilling ≫ ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d
        (degree + 2) (degree + 1) = cycle := by
  obtain ⟨iterations, eventual⟩ := singularChain_eventually_subdivision_small_lift incidence negative (degree + 2) globalFilling
  obtain ⟨subdividedFilling, liftEquality⟩ := eventual iterations le_rfl
  have subdividedBoundary : subdividedFilling ≫
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).d
        (degree + 2) (degree + 1) =
      cycle ≫ (smallIteratedSubdivision incidence negative iterations).f (degree + 1) := by
    have mono := smallSingularChainInclusion_mono incidence negative (degree + 1)
    apply (cancel_mono ((smallSingularChainInclusion incidence negative).f (degree + 1))).mp
    rw [Category.assoc, ← (smallSingularChainInclusion incidence negative).comm (degree + 2) (degree + 1),
      ← Category.assoc, liftEquality, Category.assoc,
      (singularIteratedSubdivision incidence negative iterations).comm (degree + 2) (degree + 1),
      ← Category.assoc, bounds]
    simp only [Category.assoc]
    rw [← HomologicalComplex.comp_f, ← smallIteratedSubdivision_inclusion]
    simp only [HomologicalComplex.comp_f]
  refine ⟨subdividedFilling + cycle ≫
    (smallIteratedSubdivisionHomotopy incidence negative iterations).hom (degree + 1) (degree + 2), ?_⟩
  rw [add_comp, subdividedBoundary, Category.assoc,
    homotopy_cycle_boundary (smallIteratedSubdivisionHomotopy incidence negative iterations) degree cycle closed]
  abel

end PositiveCycleBoundaryComparison

noncomputable def intLiftAlongEpi {target source : AddCommGrpCat.{0}}
    (mapping : AddCommGrpCat.of ℤ ⟶ target) (surjection : source ⟶ target) [Epi surjection] :
    AddCommGrpCat.of ℤ ⟶ source :=
  AddCommGrpCat.ofHom (zmultiplesHom source
    (((AddCommGrpCat.epi_iff_surjective surjection).mp inferInstance (mapping.hom 1)).choose))

theorem intLiftAlongEpi_comp {target source : AddCommGrpCat.{0}}
    (mapping : AddCommGrpCat.of ℤ ⟶ target) (surjection : source ⟶ target) [Epi surjection] :
    intLiftAlongEpi mapping surjection ≫ surjection = mapping := by
  apply AddCommGrpCat.int_hom_ext
  change surjection.hom ((zmultiplesHom source _) 1) = mapping.hom 1
  rw [zmultiplesHom_apply, one_zsmul]
  exact ((AddCommGrpCat.epi_iff_surjective surjection).mp inferInstance (mapping.hom 1)).choose_spec

theorem intHomology_cycle_representative (complex : ChainComplex AddCommGrpCat.{0} ℕ)
    (degree : ℕ) (classMap : AddCommGrpCat.of ℤ ⟶ complex.homology (degree + 1)) :
    ∃ cycle : AddCommGrpCat.of ℤ ⟶ complex.X (degree + 1),
      ∃ closed : cycle ≫ complex.d (degree + 1) degree = 0,
      complex.liftCycles cycle degree (by simp) closed ≫ complex.homologyπ (degree + 1) = classMap := by
  let lifted := intLiftAlongEpi classMap (complex.homologyπ (degree + 1))
  have closed : (lifted ≫ complex.iCycles (degree + 1)) ≫ complex.d (degree + 1) degree = 0 := by
    rw [Category.assoc, complex.iCycles_d]
    simp
  refine ⟨lifted ≫ complex.iCycles (degree + 1), closed, ?_⟩
  have liftEquality : complex.liftCycles (lifted ≫ complex.iCycles (degree + 1)) degree
        (by simp) closed = lifted := by
      apply (cancel_mono (complex.iCycles (degree + 1))).mp
      rw [complex.liftCycles_i]
  rw [liftEquality]
  exact intLiftAlongEpi_comp classMap (complex.homologyπ (degree + 1))

theorem intCycle_homology_zero_iff_boundary (complex : ChainComplex AddCommGrpCat.{0} ℕ)
    (degree : ℕ) (cycle : AddCommGrpCat.of ℤ ⟶ complex.X (degree + 1))
    (closed : cycle ≫ complex.d (degree + 1) degree = 0) :
    complex.liftCycles cycle degree (by simp) closed ≫ complex.homologyπ (degree + 1) = 0 ↔
      ∃ filling : AddCommGrpCat.of ℤ ⟶ complex.X (degree + 2),
        filling ≫ complex.d (degree + 2) (degree + 1) = cycle := by
  constructor
  · intro zeroClass
    obtain ⟨refinement, projection, epiProjection, filling, equality⟩ :=
      (complex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
        (degree + 2) (degree + 1) degree (by simp) (by simp) cycle closed).mp zeroClass
    let sectionMap := intLiftAlongEpi (𝟙 (AddCommGrpCat.of ℤ)) projection
    refine ⟨sectionMap ≫ filling, ?_⟩
    calc
      (sectionMap ≫ filling) ≫ complex.d (degree + 2) (degree + 1) =
          sectionMap ≫ projection ≫ cycle := by rw [Category.assoc, ← equality]
      _ = cycle := by rw [← Category.assoc, intLiftAlongEpi_comp, Category.id_comp]
  · rintro ⟨filling, bounds⟩
    exact complex.liftCycles_homologyπ_eq_zero_of_boundary cycle degree (by simp) filling bounds.symm

theorem intCycle_classes_equal_of_boundary (complex : ChainComplex AddCommGrpCat.{0} ℕ)
    (degree : ℕ) (first second : AddCommGrpCat.of ℤ ⟶ complex.X (degree + 1))
    (firstClosed : first ≫ complex.d (degree + 1) degree = 0)
    (secondClosed : second ≫ complex.d (degree + 1) degree = 0)
    (filling : AddCommGrpCat.of ℤ ⟶ complex.X (degree + 2))
    (bounds : filling ≫ complex.d (degree + 2) (degree + 1) = first - second) :
    complex.liftCycles first degree (by simp) firstClosed ≫ complex.homologyπ (degree + 1) =
      complex.liftCycles second degree (by simp) secondClosed ≫ complex.homologyπ (degree + 1) := by
  apply (cancel_mono (complex.homologyι (degree + 1))).mp
  simp only [Category.assoc, complex.homology_π_ι, complex.liftCycles_i_assoc]
  have vanished := congrArg (fun mapping => mapping ≫ complex.pOpcycles (degree + 1)) bounds
  rw [Category.assoc, complex.d_pOpcycles, comp_zero, sub_comp] at vanished
  exact sub_eq_zero.mp vanished.symm

section PositiveHomologyIso

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

omit [Finite Chart] in
theorem smallSingularHomology_positive_surjective (degree : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap
      (smallSingularChainInclusion incidence negative) (degree + 1)).hom := by
  intro homologyClass
  let classMap := AddCommGrpCat.ofHom
    (zmultiplesHom ((integralSingularChains (incidenceRealization incidence negative)).homology (degree + 1)) homologyClass)
  obtain ⟨cycle, closed, representative⟩ := intHomology_cycle_representative
    (integralSingularChains (incidenceRealization incidence negative)) degree classMap
  obtain ⟨smallCycle, smallClosed, filling, bounds⟩ := positiveSingularCycle_small_representative
    incidence negative degree cycle closed
  let smallClassMap := ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).liftCycles
    smallCycle degree (by simp) smallClosed ≫
      ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).homologyπ (degree + 1)
  refine ⟨smallClassMap.hom 1, ?_⟩
  have imageClosed : (smallCycle ≫ (smallSingularChainInclusion incidence negative).f (degree + 1)) ≫
      (integralSingularChains (incidenceRealization incidence negative)).d (degree + 1) degree = 0 := by
    rw [Category.assoc, (smallSingularChainInclusion incidence negative).comm (degree + 1) degree,
      ← Category.assoc, smallClosed]
    simp
  have classEquality := intCycle_classes_equal_of_boundary
    (integralSingularChains (incidenceRealization incidence negative)) degree cycle
    (smallCycle ≫ (smallSingularChainInclusion incidence negative).f (degree + 1))
    closed imageClosed filling bounds
  have mapEquality : smallClassMap ≫ HomologicalComplex.homologyMap
      (smallSingularChainInclusion incidence negative) (degree + 1) = classMap := by
    dsimp only [smallClassMap]
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
      HomologicalComplex.liftCycles_comp_cyclesMap_assoc, ← classEquality, representative]
  have valueEquality := congrArg (fun mapping => mapping.hom 1) mapEquality
  change (HomologicalComplex.homologyMap (smallSingularChainInclusion incidence negative)
    (degree + 1)).hom (smallClassMap.hom 1) = (zmultiplesHom _ homologyClass) 1 at valueEquality
  simpa only [zmultiplesHom_apply, one_zsmul] using valueEquality

omit [Finite Chart] in
theorem smallSingularHomology_positive_kernel_zero (degree : ℕ)
    (homologyClass : (((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).homology (degree + 1)))
    (vanished : (HomologicalComplex.homologyMap
      (smallSingularChainInclusion incidence negative) (degree + 1)).hom homologyClass = 0) :
    homologyClass = 0 := by
  let classMap := AddCommGrpCat.ofHom (zmultiplesHom
    (((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)).homology (degree + 1)) homologyClass)
  obtain ⟨cycle, closed, representative⟩ := intHomology_cycle_representative
    ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)) degree classMap
  have mapZero : classMap ≫ HomologicalComplex.homologyMap
      (smallSingularChainInclusion incidence negative) (degree + 1) = 0 := by
    apply AddCommGrpCat.int_hom_ext
    simpa [classMap, zmultiplesHom_apply] using vanished
  have imageClosed : (cycle ≫ (smallSingularChainInclusion incidence negative).f (degree + 1)) ≫
      (integralSingularChains (incidenceRealization incidence negative)).d (degree + 1) degree = 0 := by
    rw [Category.assoc, (smallSingularChainInclusion incidence negative).comm (degree + 1) degree,
      ← Category.assoc, closed]
    simp
  rw [← representative, Category.assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc] at mapZero
  obtain ⟨globalFilling, bounds⟩ := (intCycle_homology_zero_iff_boundary
    (integralSingularChains (incidenceRealization incidence negative)) degree
    (cycle ≫ (smallSingularChainInclusion incidence negative).f (degree + 1)) imageClosed).mp mapZero
  obtain ⟨smallFilling, smallBounds⟩ := positiveSmallCycle_global_boundary_is_small_boundary
    incidence negative degree cycle closed globalFilling bounds
  have smallClassZero := (intCycle_homology_zero_iff_boundary
    ((openStarSmallSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)) degree cycle closed).mpr
      ⟨smallFilling, smallBounds⟩
  rw [representative] at smallClassZero
  have value := congrArg (fun mapping => mapping.hom 1) smallClassZero
  simpa [classMap, zmultiplesHom_apply] using value

omit [Finite Chart] in
theorem smallSingularHomology_positive_injective (degree : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (smallSingularChainInclusion incidence negative) (degree + 1)).hom := by
  intro first second sameImage
  apply sub_eq_zero.mp
  apply smallSingularHomology_positive_kernel_zero incidence negative degree
  rw [map_sub, sameImage, sub_self]

omit [Finite Chart] in
theorem smallSingularChainInclusion_quasiIsoAt_positive (degree : ℕ) :
    QuasiIsoAt (smallSingularChainInclusion incidence negative) (degree + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let homologyMap := HomologicalComplex.homologyMap (smallSingularChainInclusion incidence negative) (degree + 1)
  have mono : Mono homologyMap := (AddCommGrpCat.mono_iff_injective homologyMap).mpr
    (smallSingularHomology_positive_injective incidence negative degree)
  have epi : Epi homologyMap := (AddCommGrpCat.epi_iff_surjective homologyMap).mpr
    (smallSingularHomology_positive_surjective incidence negative degree)
  exact isIso_of_mono_of_epi homologyMap

omit [Finite Chart] in
theorem smallSingularChainInclusion_quasiIso :
    QuasiIso (smallSingularChainInclusion incidence negative) := by
  rw [quasiIso_iff]
  intro degree
  cases degree with
  | zero => exact smallSingularChainInclusion_quasiIsoAt_zero incidence negative
  | succ degree => exact smallSingularChainInclusion_quasiIsoAt_positive incidence negative degree

end PositiveHomologyIso

end BondalThomsen.ConvexNerveSubdivisionCellExpansion
