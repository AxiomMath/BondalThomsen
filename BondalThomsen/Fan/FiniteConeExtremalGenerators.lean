module

public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Analysis.Convex.Cone.Closure
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators

namespace BondalThomsen.FiniteConeExtremalGenerators

variable {Index Space : Type*} [AddCommGroup Space] [Module ℝ Space]

theorem hull_eq_nonnegative_combinations {generators : Set Space} [Fintype generators] :
    (PointedCone.hull ℝ generators : Set Space) =
      {vector | ∃ coefficients : generators → ℝ,
        (∀ generator, 0 ≤ coefficients generator) ∧
        ∑ generator, coefficients generator • (generator : Space) = vector} := by
  classical
  apply Set.Subset.antisymm
  · intro vector membership
    induction membership using Submodule.span_induction with
    | mem vector membership =>
        refine ⟨fun generator =>
          if generator = (⟨vector, membership⟩ : generators) then 1 else 0, ?_, ?_⟩
        · intro generator
          dsimp only
          split_ifs <;> norm_num
        · simp [Finset.sum_ite_eq']
    | zero => exact ⟨0, fun _ => le_refl 0, by simp⟩
    | add first second _ _ firstCombination secondCombination =>
        obtain ⟨firstCoefficients, firstNonnegative, rfl⟩ := firstCombination
        obtain ⟨secondCoefficients, secondNonnegative, rfl⟩ := secondCombination
        exact ⟨fun generator => firstCoefficients generator + secondCoefficients generator,
          fun generator => add_nonneg (firstNonnegative generator) (secondNonnegative generator),
          by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul scalar vector _ combination =>
        obtain ⟨coefficients, nonnegative, rfl⟩ := combination
        refine ⟨fun generator => (scalar : ℝ) * coefficients generator,
          fun generator => mul_nonneg scalar.2 (nonnegative generator), ?_⟩
        change ∑ generator, ((scalar : ℝ) * coefficients generator) • (generator : Space) =
          (scalar : ℝ) • ∑ generator, coefficients generator • (generator : Space)
        simp [Finset.smul_sum, smul_smul]
  · rintro vector ⟨coefficients, nonnegative, rfl⟩
    exact (PointedCone.hull ℝ generators).sum_mem fun generator _ =>
      (PointedCone.hull ℝ generators).smul_mem (nonnegative generator)
        (PointedCone.subset_hull generator.2)

theorem face_eq_hull_inter {generators : Set Space} (finite : generators.Finite)
    {face : PointedCone ℝ Space} (isFace : face.IsFaceOf (PointedCone.hull ℝ generators)) :
    face = PointedCone.hull ℝ (generators ∩ (face : Set Space)) := by
  classical
  let : Fintype generators := finite.fintype
  apply le_antisymm
  · intro vector membership
    have hullMembership := isFace.le membership
    rw [← SetLike.mem_coe, hull_eq_nonnegative_combinations] at hullMembership
    obtain ⟨coefficients, nonnegative, equality⟩ := hullMembership
    rw [← equality]
    apply (PointedCone.hull ℝ (generators ∩ (face : Set Space))).sum_mem
    intro generator _
    by_cases positive : 0 < coefficients generator
    · exact (PointedCone.hull ℝ (generators ∩ (face : Set Space))).smul_mem
        (nonnegative generator) (PointedCone.subset_hull ⟨generator.2,
          isFace.mem_of_sum_smul_mem (fun other => PointedCone.subset_hull other.2)
            nonnegative (equality ▸ membership) generator positive⟩)
    · have zero : coefficients generator = 0 := le_antisymm
        (le_of_not_gt positive) (nonnegative generator)
      simp [zero]
  · exact Submodule.span_le.mpr fun _ membership => membership.2

theorem irredundant_generator_isFace {generators : Set Space} {generator : Space}
    (salient : (PointedCone.hull ℝ (insert generator generators) : ConvexCone ℝ Space).Salient)
    (irredundant : generator ∉ PointedCone.hull ℝ generators) :
    (PointedCone.hull ℝ {generator}).IsFaceOf
      (PointedCone.hull ℝ (insert generator generators)) := by
  let cone := PointedCone.hull ℝ (insert generator generators)
  let remainder := PointedCone.hull ℝ generators
  have remainder_le : remainder ≤ cone := Submodule.span_mono (Set.subset_insert _ _)
  have generatorMembership : generator ∈ cone :=
    PointedCone.subset_hull (Set.mem_insert _ _)
  refine ⟨Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)), ?_⟩
  intro first second scalar firstMembership secondMembership positive sumMembership
  obtain ⟨firstScalar, firstRemainder, firstRemainderMembership, firstEquality⟩ :=
    Submodule.mem_span_insert.mp firstMembership
  obtain ⟨secondScalar, secondRemainder, secondRemainderMembership, secondEquality⟩ :=
    Submodule.mem_span_insert.mp secondMembership
  obtain ⟨rayScalar, rayNonnegative, rayEquality⟩ :=
    PointedCone.mem_hull_singleton.mp sumMembership
  let residual : ℝ := rayScalar - scalar * (firstScalar : ℝ) - (secondScalar : ℝ)
  have residualEquality : residual • generator = scalar • firstRemainder + secondRemainder := by
    rw [firstEquality, secondEquality] at rayEquality
    change rayScalar • generator =
      scalar • ((firstScalar : ℝ) • generator + firstRemainder) +
        ((secondScalar : ℝ) • generator + secondRemainder) at rayEquality
    dsimp [residual]
    rw [sub_smul, sub_smul, mul_smul]
    rw [rayEquality]
    simp only [smul_add, smul_smul]
    rw [add_add_add_comm, sub_sub]
    exact add_sub_cancel_left
      ((scalar * (firstScalar : ℝ)) • generator + (secondScalar : ℝ) • generator)
      (scalar • firstRemainder + secondRemainder)
  have residualNonpositive : residual ≤ 0 := by
    by_contra notNonpositive
    have residualPositive : 0 < residual := lt_of_not_ge notNonpositive
    apply irredundant
    have membership : residual • generator ∈ remainder := by
      rw [residualEquality]
      exact remainder.add_mem (remainder.smul_mem positive.le firstRemainderMembership)
        secondRemainderMembership
    have scaled := remainder.smul_mem (inv_nonneg.mpr residualPositive.le) membership
    simpa [smul_smul, residualPositive.ne'] using scaled
  have negMembership : -(scalar • firstRemainder) ∈ cone := by
    have equality : -(scalar • firstRemainder) =
        secondRemainder + (-residual) • generator := by
      rw [neg_smul, residualEquality]
      abel
    rw [equality]
    exact cone.add_mem (remainder_le secondRemainderMembership)
      (cone.smul_mem (neg_nonneg.mpr residualNonpositive) generatorMembership)
  have scaledZero : scalar • firstRemainder = 0 := by
    by_contra nonzero
    exact salient (scalar • firstRemainder)
      (cone.smul_mem positive.le (remainder_le firstRemainderMembership)) nonzero negMembership
  have remainderZero : firstRemainder = 0 :=
    (smul_eq_zero.mp scaledZero).resolve_left positive.ne'
  apply PointedCone.mem_hull_singleton.mpr
  exact ⟨firstScalar, firstScalar.2,
    by simpa only [remainderZero, add_zero, Nonneg.coe_smul] using firstEquality.symm⟩

theorem hull_eq_hull_extreme_generators {generators : Set Space} (finite : generators.Finite)
    (salient : (PointedCone.hull ℝ generators : ConvexCone ℝ Space).Salient) :
    PointedCone.hull ℝ generators = PointedCone.hull ℝ
      {generator ∈ generators | generator ≠ 0 ∧
        (PointedCone.hull ℝ {generator}).IsFaceOf (PointedCone.hull ℝ generators)} := by
  classical
  obtain ⟨minimal, minimalMembership, minimalCard⟩ := Finset.exists_min_image
    (finite.toFinset.powerset.filter fun (subset : Finset Space) =>
      PointedCone.hull ℝ (subset : Set Space) = PointedCone.hull ℝ generators)
    Finset.card ⟨finite.toFinset, by simp⟩
  obtain ⟨minimalSubset, minimalHull⟩ := Finset.mem_filter.mp minimalMembership
  have subset : (minimal : Set Space) ⊆ generators := by
    simpa using Finset.mem_powerset.mp minimalSubset
  rw [← minimalHull]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro generator membership
    have generatorMembership : generator ∈ minimal := membership
    have insertEquality : insert generator (↑(minimal.erase generator) : Set Space) =
        (minimal : Set Space) := by
      rw [← Finset.coe_insert, Finset.insert_erase generatorMembership]
    have irredundant : generator ∉ PointedCone.hull ℝ (↑(minimal.erase generator) : Set Space) := by
      intro redundant
      have sameHull : PointedCone.hull ℝ (↑(minimal.erase generator) : Set Space) =
          PointedCone.hull ℝ generators := by
        calc
          PointedCone.hull ℝ (↑(minimal.erase generator) : Set Space) =
              PointedCone.hull ℝ (insert generator (↑(minimal.erase generator) : Set Space)) :=
            (Submodule.span_insert_eq_span redundant).symm
          _ = PointedCone.hull ℝ (minimal : Set Space) := by rw [insertEquality]
          _ = PointedCone.hull ℝ generators := minimalHull
      have bound := minimalCard (minimal.erase generator)
        (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
          ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp minimalSubset)), sameHull⟩)
      have strict := Finset.card_erase_lt_of_mem generatorMembership
      omega
    have nonzero : generator ≠ 0 := by
      intro zero
      apply irredundant
      simp [zero]
    have salientMinimal : (PointedCone.hull ℝ
        (insert generator (↑(minimal.erase generator) : Set Space)) : ConvexCone ℝ Space).Salient := by
      rw [insertEquality, minimalHull]
      exact salient
    have isFace := irredundant_generator_isFace salientMinimal irredundant
    rw [insertEquality, minimalHull] at isFace
    exact PointedCone.subset_hull ⟨subset membership, nonzero, by simpa [minimalHull] using isFace⟩
  · exact Submodule.span_le.mpr fun _ membership => by
      rw [minimalHull]
      exact PointedCone.subset_hull membership.1

theorem nonnegative_on_hull_iff {generators : Set Space} (functional : Space →ₗ[ℝ] ℝ) :
    (∀ vector ∈ PointedCone.hull ℝ generators, 0 ≤ functional vector) ↔
      ∀ generator ∈ generators, 0 ≤ functional generator := by
  constructor
  · exact fun nonnegative _ membership => nonnegative _ (PointedCone.subset_hull membership)
  · intro nonnegative vector membership
    induction membership using Submodule.span_induction with
    | mem vector membership => exact nonnegative vector membership
    | zero => simp
    | add first second _ _ firstNonnegative secondNonnegative =>
        simpa using add_nonneg firstNonnegative secondNonnegative
    | smul scalar vector _ vectorNonnegative =>
        change 0 ≤ functional ((scalar : ℝ) • vector)
        simpa using mul_nonneg scalar.2 vectorNonnegative

theorem positive_on_hull {generators : Set Space} (functional : Space →ₗ[ℝ] ℝ)
    (positive : ∀ generator ∈ generators, generator ≠ 0 → 0 < functional generator)
    {vector : Space} (membership : vector ∈ PointedCone.hull ℝ generators)
    (nonzero : vector ≠ 0) : 0 < functional vector := by
  have zeroOrPositive : vector = 0 ∨ 0 < functional vector := by
    clear nonzero
    induction membership using Submodule.span_induction with
    | mem generator generatorMembership =>
        by_cases zero : generator = 0
        · exact Or.inl zero
        · exact Or.inr (positive generator generatorMembership zero)
    | zero => exact Or.inl rfl
    | add first second _ _ firstAlternative secondAlternative =>
        rcases firstAlternative with firstZero | firstPositive
        · simpa [firstZero] using secondAlternative
        · rcases secondAlternative with secondZero | secondPositive
          · exact Or.inr (by simpa [secondZero] using firstPositive)
          · exact Or.inr (by simpa using add_pos firstPositive secondPositive)
    | smul scalar vector _ vectorAlternative =>
        rcases vectorAlternative with vectorZero | vectorPositive
        · exact Or.inl (by simp [vectorZero])
        · by_cases scalarZero : (scalar : ℝ) = 0
          · exact Or.inl (by
              rw [← Nonneg.coe_smul, scalarZero, zero_smul])
          · right
            change 0 < functional ((scalar : ℝ) • vector)
            simpa using mul_pos (lt_of_le_of_ne scalar.2 (Ne.symm scalarZero)) vectorPositive
  exact zeroOrPositive.resolve_left nonzero

theorem salient_of_positive_functional {generators : Set Space}
    (functional : Space →ₗ[ℝ] ℝ)
    (positive : ∀ generator ∈ generators, generator ≠ 0 → 0 < functional generator) :
    (PointedCone.hull ℝ generators : ConvexCone ℝ Space).Salient := by
  intro vector membership nonzero negMembership
  have firstPositive := positive_on_hull functional positive membership nonzero
  have negPositive := positive_on_hull functional positive negMembership (neg_ne_zero.mpr nonzero)
  rw [map_neg] at negPositive
  linarith

theorem nonnegative_iff_on_extreme_generators {generators : Set Space}
    (finite : generators.Finite)
    (salient : (PointedCone.hull ℝ generators : ConvexCone ℝ Space).Salient)
    (functional : Space →ₗ[ℝ] ℝ) :
    (∀ vector ∈ PointedCone.hull ℝ generators, 0 ≤ functional vector) ↔
      ∀ generator ∈ generators, generator ≠ 0 →
        (PointedCone.hull ℝ {generator}).IsFaceOf (PointedCone.hull ℝ generators) →
        0 ≤ functional generator := by
  nth_rw 1 [hull_eq_hull_extreme_generators finite salient]
  rw [nonnegative_on_hull_iff]
  simp only [Set.mem_ofPred_eq, and_imp]

end BondalThomsen.FiniteConeExtremalGenerators

namespace BondalThomsen.FiniteConeExtremalGenerators

variable {Index Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

lemma simplicial_cone_isClosed
    (vectors : Index → Space) (support : Finset Index) (hli : LinearIndepOn ℝ vectors support) :
    IsClosed {target : Space |
      ∃ coefficients : Index → ℝ, (∀ index, 0 ≤ coefficients index) ∧ (∀ index ∉ support, coefficients index = 0) ∧ ∑ index ∈ support, coefficients index • vectors index = target} := by
  classical
  set combinationMap : (support → ℝ) →ₗ[ℝ] Space :=
    ∑ index : support, LinearMap.smulRight (LinearMap.proj index) (vectors index) with hL_def
  have hLval : ∀ coefficients : support → ℝ, combinationMap coefficients = ∑ index : support, coefficients index • vectors index := by
    intro coefficients
    simp [hL_def, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hLinj : Function.Injective combinationMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro input hm
    rw [hLval] at hm
    funext index; exact Fintype.linearIndependent_iff.mp hli input hm index
  have hclosedmap : IsClosedMap combinationMap :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot_of_injective hLinj)).isClosedMap
  have hO : IsClosed {coefficients : support → ℝ | ∀ index, 0 ≤ coefficients index} := by
    have : {coefficients : support → ℝ | ∀ index, 0 ≤ coefficients index} = ⋂ index, {coefficients : support → ℝ | 0 ≤ coefficients index} := by ext coefficients; simp
    rw [this]
    exact isClosed_iInter (fun index => isClosed_le continuous_const (continuous_apply index))
  have hclosed := hclosedmap _ hO
  convert hclosed using 1
  ext target
  constructor
  · rintro ⟨coefficients, hc0, hcoff, rfl⟩
    refine ⟨fun index : support => coefficients index, fun index => hc0 _, ?_⟩
    rw [hLval, ← Finset.sum_attach support (fun j => coefficients j • vectors j)]
    rfl
  · rintro ⟨coefficients, hc0, rfl⟩
    refine ⟨fun j => if h : j ∈ support then coefficients ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
    · intro index; dsimp only; split_ifs with h
      · exact hc0 _
      · exact le_refl 0
    · intro index hk; simp [hk]
    · rw [hLval, ← Finset.sum_attach support (fun j => (if h : j ∈ support then coefficients ⟨j, h⟩ else 0) • vectors j)]
      apply Finset.sum_congr rfl
      intro index _
      simp [index.2]

lemma conic_caratheodory {Scalar Ambient : Type*} [Field Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    [AddCommGroup Ambient] [Module Scalar Ambient] [Fintype Index]
    (vectors : Index → Ambient) (coefficients : Index → Scalar) (hc : ∀ index, 0 ≤ coefficients index) :
    ∃ (reducedCoefficients : Index → Scalar) (support : Finset Index), (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ support, reducedCoefficients index = 0) ∧
      LinearIndepOn Scalar vectors support ∧ (∑ index ∈ support, reducedCoefficients index • vectors index) = ∑ index, coefficients index • vectors index := by
  classical
  obtain ⟨support, hs⟩ : ∃ support : Finset Index,
      (∃ reducedCoefficients : Index → Scalar, (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ support, reducedCoefficients index = 0) ∧
        (∑ index ∈ support, reducedCoefficients index • vectors index = ∑ index, coefficients index • vectors index)) ∧
      ∀ smallerSupport : Finset Index, (∃ reducedCoefficients : Index → Scalar, (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ smallerSupport, reducedCoefficients index = 0) ∧
        (∑ index ∈ smallerSupport, reducedCoefficients index • vectors index = ∑ index, coefficients index • vectors index)) → support.card ≤ smallerSupport.card := by
    apply_rules [Set.exists_min_image]
    · exact Set.toFinite _
    · exact ⟨Finset.univ, ⟨coefficients, hc, fun index hk => False.elim <| hk <| Finset.mem_univ _, by
        simp⟩⟩
  by_cases h_lin_dep : ¬ LinearIndepOn Scalar vectors support
  · obtain ⟨reducedCoefficients, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨dependency, ha_nonzero, ha_support, ha_sum⟩ : ∃ dependency : Index → Scalar,
        (∃ index ∈ support, dependency index ≠ 0) ∧ (∀ index ∉ support, dependency index = 0) ∧
        (∑ index ∈ support, dependency index • vectors index = 0) ∧ (∃ index ∈ support, dependency index > 0) := by
      obtain ⟨dependency, ha_nonzero, ha_sum⟩ : ∃ dependency : Index → Scalar,
          (∃ index ∈ support, dependency index ≠ 0) ∧ (∀ index ∉ support, dependency index = 0) ∧
          (∑ index ∈ support, dependency index • vectors index = 0) := by
        rw [linearIndepOn_iff'] at h_lin_dep
        push Not at h_lin_dep
        obtain ⟨smallerSupport, weights, ht, hg, chosenIndex, hi, hi'⟩ := h_lin_dep
        refine ⟨fun index => if index ∈ smallerSupport then weights index else 0, ⟨chosenIndex, ht hi, by simpa [hi] using hi'⟩,
          fun index hk => by
            change (if index ∈ smallerSupport then weights index else 0) = 0
            split
            · rename_i hkt
              exact (hk (ht hkt)).elim
            · rfl, ?_⟩
        calc ∑ index ∈ support, (if index ∈ smallerSupport then weights index else 0) • vectors index
            = ∑ index ∈ support, if index ∈ smallerSupport then weights index • vectors index else 0 := by
              refine Finset.sum_congr rfl (fun index _ => ?_); rw [ite_smul, zero_smul]
          _ = ∑ index ∈ support ∩ smallerSupport, weights index • vectors index := Finset.sum_ite_mem support smallerSupport _
          _ = ∑ index ∈ smallerSupport, weights index • vectors index := by rw [Finset.inter_eq_right.mpr ht]
          _ = 0 := hg
      by_cases h_neg : ∀ index ∈ support, dependency index ≤ 0
      · obtain ⟨index, hks, hk⟩ := ha_nonzero
        exact ⟨fun index => -dependency index, ⟨index, hks, neg_ne_zero.mpr hk⟩,
          fun index hk => by simp only [ha_sum.1 index hk, neg_zero],
          by simp [neg_smul, ha_sum.2],
          ⟨index, hks, neg_pos.mpr (lt_of_le_of_ne (h_neg index hks) hk)⟩⟩
      · exact ⟨dependency, ha_nonzero, ha_sum.1, ha_sum.2, by
          push Not at h_neg
          exact h_neg⟩
    obtain ⟨step, hθ_min⟩ : ∃ step,
        (∀ index ∈ support, reducedCoefficients index - step * dependency index ≥ 0) ∧ (∃ index ∈ support, reducedCoefficients index - step * dependency index = 0) := by
      obtain ⟨minimumIndex, hk₀⟩ : ∃ minimumIndex ∈ support, dependency minimumIndex > 0 ∧
          ∀ index ∈ support, dependency index > 0 → reducedCoefficients index / dependency index ≥ reducedCoefficients minimumIndex / dependency minimumIndex := by
        obtain ⟨positiveIndex, hkp⟩ := ha_sum.2
        obtain ⟨minimumIndex, hk₀f, hk₀min⟩ :=
          Finset.exists_min_image (support.filter (fun index => dependency index > 0)) (fun index => reducedCoefficients index / dependency index)
            ⟨positiveIndex, Finset.mem_filter.mpr hkp⟩
        obtain ⟨hk₀s, hk₀pos⟩ := Finset.mem_filter.mp hk₀f
        exact ⟨minimumIndex, hk₀s, hk₀pos, fun index hk hk' =>
          hk₀min index (Finset.mem_filter.mpr ⟨hk, hk'⟩)⟩
      refine ⟨reducedCoefficients minimumIndex / dependency minimumIndex, ?_, minimumIndex, hk₀.1, ?_⟩
      · intro index hk
        by_cases hk' : dependency index > 0
        · have hle : reducedCoefficients minimumIndex / dependency minimumIndex * dependency index ≤ reducedCoefficients index :=
            (le_div_iff₀ hk').1 (hk₀.2.2 index hk hk')
          linarith
        · have h2 : reducedCoefficients minimumIndex / dependency minimumIndex * dependency index ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hd_nonneg _) hk₀.2.1.le)
              (le_of_not_gt hk')
          linarith [hd_nonneg index]
      · rw [div_mul_cancel₀ _ hk₀.2.1.ne', sub_self]
    set smallerSupport := support.filter (fun index => reducedCoefficients index - step * dependency index ≠ 0) with ht_def
    have h_t_support : ∀ index, 0 ≤ reducedCoefficients index - step * dependency index := by
      exact fun index => if hk : index ∈ support then hθ_min.1 index hk else by
        simp [hd_zero index hk, ha_support index hk]
    have h_t_zero : ∀ index ∉ smallerSupport, reducedCoefficients index - step * dependency index = 0 := by
      intro index hk
      by_cases hks : index ∈ support
      · by_contra hP
        exact hk (by rw [ht_def]; exact Finset.mem_filter.mpr ⟨hks, hP⟩)
      · rw [hd_zero index hks, ha_support index hks]
        ring
    have h_t_sum : ∑ index ∈ smallerSupport, (reducedCoefficients index - step * dependency index) • vectors index = ∑ index, coefficients index • vectors index := by
      convert congr_arg (fun vector => vector - step • ∑ index ∈ support, dependency index • vectors index) hd_sum using 1
      · rw [Finset.sum_filter_of_ne]
        · simp [sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
        · exact fun index _ hk' hk'' => hk' <| by rw [hk'', zero_smul]
      · simp [ha_sum.1]
    contrapose! hs
    refine fun _ => ⟨smallerSupport, ⟨fun index => reducedCoefficients index - step * dependency index, h_t_support, h_t_zero, h_t_sum⟩, ?_⟩
    refine Finset.card_lt_card ?_
    rw [ht_def]
    obtain ⟨k₁, hk₁s, hk₁0⟩ := hθ_min.2
    exact ⟨Finset.filter_subset _ _, fun hsub => (Finset.mem_filter.mp (hsub hk₁s)).2 hk₁0⟩
  · exact ⟨hs.1.choose, support, hs.1.choose_spec.1, hs.1.choose_spec.2.1,
      Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2⟩

lemma fg_cone_isClosed [Fintype Index] (vectors : Index → Space) :
    IsClosed {target : Space | ∃ coefficients : Index → ℝ, (∀ index, 0 ≤ coefficients index) ∧ ∑ index, coefficients index • vectors index = target} := by
  classical
  have hset : {target : Space | ∃ coefficients : Index → ℝ, (∀ index, 0 ≤ coefficients index) ∧ ∑ index, coefficients index • vectors index = target}
      = ⋃ support : Finset Index, ⋃ (_ : LinearIndepOn ℝ vectors support),
          {target : Space | ∃ coefficients : Index → ℝ, (∀ index, 0 ≤ coefficients index) ∧ (∀ index ∉ support, coefficients index = 0) ∧
            ∑ index ∈ support, coefficients index • vectors index = target} := by
    ext target
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨coefficients, hc0, rfl⟩
      obtain ⟨reducedCoefficients, support, hd0, hdoff, hindep, hsum⟩ := conic_caratheodory vectors coefficients hc0
      exact ⟨support, hindep, reducedCoefficients, hd0, hdoff, hsum⟩
    · rintro ⟨support, hindep, coefficients, hc0, hcoff, rfl⟩
      refine ⟨coefficients, hc0, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ support)]
      intro index _ hks; rw [hcoff index hks, zero_smul]
  rw [hset]
  exact isClosed_iUnion_of_finite fun support =>
    isClosed_iUnion_of_finite fun h => simplicial_cone_isClosed vectors support h

theorem hull_isClosed_of_finite {generators : Set Space} (finite : generators.Finite) :
    IsClosed (PointedCone.hull ℝ generators : Set Space) := by
  classical
  let : Fintype generators := finite.fintype
  rw [hull_eq_nonnegative_combinations]
  exact fg_cone_isClosed (fun generator : generators => (generator : Space))

end BondalThomsen.FiniteConeExtremalGenerators
