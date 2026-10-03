module

public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open scoped BigOperators

namespace LeanPool.Erdos81PaperIContrib

variable {κ ι : Type*} {Ambient : Type*} [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]

lemma simplicial_cone_isClosed
    (vectors : κ → Ambient) (generators : Finset κ) (hli : LinearIndepOn ℝ vectors generators) :
    IsClosed {point : Ambient |
      ∃ coefficients : κ → ℝ, (∀ index, 0 ≤ coefficients index) ∧ (∀ index ∉ generators, coefficients index = 0) ∧ ∑ index ∈ generators, coefficients index • vectors index = point} := by
  classical
  set combination : (generators → ℝ) →ₗ[ℝ] Ambient :=
    ∑ index : generators, LinearMap.smulRight (LinearMap.proj index) (vectors index) with hL_def
  have hLval : ∀ coefficients : generators → ℝ, combination coefficients = ∑ index : generators, coefficients index • vectors index := by
    intro coefficients
    simp [hL_def, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hLinj : Function.Injective combination := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro coefficients hm
    rw [hLval] at hm
    funext index; exact Fintype.linearIndependent_iff.mp hli coefficients hm index
  have hclosedmap : IsClosedMap combination :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot_of_injective hLinj)).isClosedMap
  have hO : IsClosed {coefficients : generators → ℝ | ∀ index, 0 ≤ coefficients index} := by
    have : {coefficients : generators → ℝ | ∀ index, 0 ≤ coefficients index} = ⋂ index, {coefficients : generators → ℝ | 0 ≤ coefficients index} := by ext coefficients; simp
    rw [this]
    exact isClosed_iInter (fun index => isClosed_le continuous_const (continuous_apply index))
  have hclosed := hclosedmap _ hO
  convert hclosed using 1
  ext point
  constructor
  · rintro ⟨coefficients, hc0, hcoff, rfl⟩
    refine ⟨fun index : generators => coefficients index, fun index => hc0 _, ?_⟩
    rw [hLval, ← Finset.sum_attach generators (fun label => coefficients label • vectors label)]
    rfl
  · rintro ⟨coefficients, hc0, rfl⟩
    refine ⟨fun label => if member : label ∈ generators then coefficients ⟨label, member⟩ else 0, ?_, ?_, ?_⟩
    · intro index; dsimp only; split_ifs with member
      · exact hc0 _
      · exact le_refl 0
    · intro index hk; simp [hk]
    · rw [hLval, ← Finset.sum_attach generators (fun label => (if member : label ∈ generators then coefficients ⟨label, member⟩ else 0) • vectors label)]
      apply Finset.sum_congr rfl
      intro index _
      simp [index.2]

lemma conic_caratheodory {Scalar ModuleSpace : Type*} [Field Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    [AddCommGroup ModuleSpace] [Module Scalar ModuleSpace] [Fintype κ]
    (vectors : κ → ModuleSpace) (coefficients : κ → Scalar) (hc : ∀ index, 0 ≤ coefficients index) :
    ∃ (weights : κ → Scalar) (generators : Finset κ), (∀ index, 0 ≤ weights index) ∧ (∀ index ∉ generators, weights index = 0) ∧
      LinearIndepOn Scalar vectors generators ∧ (∑ index ∈ generators, weights index • vectors index) = ∑ index, coefficients index • vectors index := by
  classical
  obtain ⟨generators, hs⟩ : ∃ generators : Finset κ,
      (∃ weights : κ → Scalar, (∀ index, 0 ≤ weights index) ∧ (∀ index ∉ generators, weights index = 0) ∧
        (∑ index ∈ generators, weights index • vectors index = ∑ index, coefficients index • vectors index)) ∧
      ∀ subfamily : Finset κ, (∃ weights : κ → Scalar, (∀ index, 0 ≤ weights index) ∧ (∀ index ∉ subfamily, weights index = 0) ∧
        (∑ index ∈ subfamily, weights index • vectors index = ∑ index, coefficients index • vectors index)) → generators.card ≤ subfamily.card := by
    apply_rules [Set.exists_min_image]
    · exact Set.toFinite _
    · exact ⟨Finset.univ, ⟨coefficients, hc, fun index hk => False.elim <| hk <| Finset.mem_univ _, by
        simp⟩⟩
  by_cases h_lin_dep : ¬ LinearIndepOn Scalar vectors generators
  · obtain ⟨weights, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨relation, ha_nonzero, ha_support, ha_sum⟩ : ∃ relation : κ → Scalar,
        (∃ index ∈ generators, relation index ≠ 0) ∧ (∀ index ∉ generators, relation index = 0) ∧
        (∑ index ∈ generators, relation index • vectors index = 0) ∧ (∃ index ∈ generators, relation index > 0) := by
      obtain ⟨relation, ha_nonzero, ha_sum⟩ : ∃ relation : κ → Scalar,
          (∃ index ∈ generators, relation index ≠ 0) ∧ (∀ index ∉ generators, relation index = 0) ∧
          (∑ index ∈ generators, relation index • vectors index = 0) := by
        rw [linearIndepOn_iff'] at h_lin_dep
        push Not at h_lin_dep
        obtain ⟨subfamily, scalars, ht, hg, chosen, hi, hi'⟩ := h_lin_dep
        refine ⟨fun index => if index ∈ subfamily then scalars index else 0, ⟨chosen, ht hi, by simpa [hi] using hi'⟩,
          fun index hk => by
            change (if index ∈ subfamily then scalars index else 0) = 0
            split
            · rename_i hkt
              exact (hk (ht hkt)).elim
            · rfl, ?_⟩
        calc ∑ index ∈ generators, (if index ∈ subfamily then scalars index else 0) • vectors index
            = ∑ index ∈ generators, if index ∈ subfamily then scalars index • vectors index else 0 := by
              refine Finset.sum_congr rfl (fun index _ => ?_); rw [ite_smul, zero_smul]
          _ = ∑ index ∈ generators ∩ subfamily, scalars index • vectors index := Finset.sum_ite_mem generators subfamily _
          _ = ∑ index ∈ subfamily, scalars index • vectors index := by rw [Finset.inter_eq_right.mpr ht]
          _ = 0 := hg
      by_cases h_neg : ∀ index ∈ generators, relation index ≤ 0
      · obtain ⟨index, hks, hk⟩ := ha_nonzero
        exact ⟨fun index => -relation index, ⟨index, hks, neg_ne_zero.mpr hk⟩,
          fun index hk => by simp only [ha_sum.1 index hk, neg_zero],
          by simp [neg_smul, ha_sum.2],
          ⟨index, hks, neg_pos.mpr (lt_of_le_of_ne (h_neg index hks) hk)⟩⟩
      · exact ⟨relation, ha_nonzero, ha_sum.1, ha_sum.2, by
          push Not at h_neg
          exact h_neg⟩
    obtain ⟨θ, memberθ_min⟩ : ∃ θ,
        (∀ index ∈ generators, weights index - θ * relation index ≥ 0) ∧ (∃ index ∈ generators, weights index - θ * relation index = 0) := by
      obtain ⟨index₀, hk₀⟩ : ∃ index₀ ∈ generators, relation index₀ > 0 ∧
          ∀ index ∈ generators, relation index > 0 → weights index / relation index ≥ weights index₀ / relation index₀ := by
        obtain ⟨kp, hkp⟩ := ha_sum.2
        obtain ⟨index₀, hk₀f, hk₀min⟩ :=
          Finset.exists_min_image (generators.filter (fun index => relation index > 0)) (fun index => weights index / relation index)
            ⟨kp, Finset.mem_filter.mpr hkp⟩
        obtain ⟨hk₀generators, hk₀pos⟩ := Finset.mem_filter.mp hk₀f
        exact ⟨index₀, hk₀generators, hk₀pos, fun index hk hk' =>
          hk₀min index (Finset.mem_filter.mpr ⟨hk, hk'⟩)⟩
      refine ⟨weights index₀ / relation index₀, ?_, index₀, hk₀.1, ?_⟩
      · intro index hk
        by_cases hk' : relation index > 0
        · have hle : weights index₀ / relation index₀ * relation index ≤ weights index :=
            (le_div_iff₀ hk').1 (hk₀.2.2 index hk hk')
          linarith
        · have h2 : weights index₀ / relation index₀ * relation index ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hd_nonneg _) hk₀.2.1.le)
              (le_of_not_gt hk')
          linarith [hd_nonneg index]
      · rw [div_mul_cancel₀ _ hk₀.2.1.ne', sub_self]
    set subfamily := generators.filter (fun index => weights index - θ * relation index ≠ 0) with ht_def
    have h_t_support : ∀ index, 0 ≤ weights index - θ * relation index := by
      exact fun index => if hk : index ∈ generators then memberθ_min.1 index hk else by
        simp [hd_zero index hk, ha_support index hk]
    have h_t_zero : ∀ index ∉ subfamily, weights index - θ * relation index = 0 := by
      intro index hk
      by_cases hks : index ∈ generators
      · by_contra hP
        exact hk (by rw [ht_def]; exact Finset.mem_filter.mpr ⟨hks, hP⟩)
      · rw [hd_zero index hks, ha_support index hks]
        ring
    have h_t_sum : ∑ index ∈ subfamily, (weights index - θ * relation index) • vectors index = ∑ index, coefficients index • vectors index := by
      convert congr_arg (fun vector => vector - θ • ∑ index ∈ generators, relation index • vectors index) hd_sum using 1
      · rw [Finset.sum_filter_of_ne]
        · simp [sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
        · exact fun index _ hk' hk'' => hk' <| by rw [hk'', zero_smul]
      · simp [ha_sum.1]
    contrapose! hs
    refine fun _ => ⟨subfamily, ⟨fun index => weights index - θ * relation index, h_t_support, h_t_zero, h_t_sum⟩, ?_⟩
    refine Finset.card_lt_card ?_
    rw [ht_def]
    obtain ⟨index₁, hk₁generators, hk₁0⟩ := memberθ_min.2
    exact ⟨Finset.filter_subset _ _, fun hsub => (Finset.mem_filter.mp (hsub hk₁generators)).2 hk₁0⟩
  · exact ⟨hs.1.choose, generators, hs.1.choose_spec.1, hs.1.choose_spec.2.1,
      Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2⟩

lemma fg_cone_isClosed [Fintype κ] (vectors : κ → Ambient) :
    IsClosed {point : Ambient | ∃ coefficients : κ → ℝ, (∀ index, 0 ≤ coefficients index) ∧ ∑ index, coefficients index • vectors index = point} := by
  classical
  have hset : {point : Ambient | ∃ coefficients : κ → ℝ, (∀ index, 0 ≤ coefficients index) ∧ ∑ index, coefficients index • vectors index = point}
      = ⋃ generators : Finset κ, ⋃ (_ : LinearIndepOn ℝ vectors generators),
          {point : Ambient | ∃ coefficients : κ → ℝ, (∀ index, 0 ≤ coefficients index) ∧ (∀ index ∉ generators, coefficients index = 0) ∧
            ∑ index ∈ generators, coefficients index • vectors index = point} := by
    ext point
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨coefficients, hc0, rfl⟩
      obtain ⟨weights, generators, hd0, hdoff, hindep, hsum⟩ := conic_caratheodory vectors coefficients hc0
      exact ⟨generators, hindep, weights, hd0, hdoff, hsum⟩
    · rintro ⟨generators, hindep, coefficients, hc0, hcoff, rfl⟩
      refine ⟨coefficients, hc0, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ generators)]
      intro index _ hks; rw [hcoff index hks, zero_smul]
  rw [hset]
  exact isClosed_iUnion_of_finite fun generators =>
    isClosed_iUnion_of_finite fun member => simplicial_cone_isClosed vectors generators member

open scoped BigOperators

private lemma hull_eq_engine {generators : Set Ambient} [Fintype generators] :
    (PointedCone.hull ℝ generators : Set Ambient)
      = {point : Ambient | ∃ coefficients : ↥generators → ℝ, (∀ index, 0 ≤ coefficients index) ∧ ∑ index, coefficients index • (index : Ambient) = point} := by
  classical
  apply Set.Subset.antisymm
  ·
    intro vector hx
    induction hx using Submodule.span_induction with
    | mem vector member =>
        refine ⟨fun index => if index = (⟨vector, member⟩ : generators) then (1 : ℝ) else 0, ?_, ?_⟩
        · intro index; dsimp only; split_ifs <;> norm_num
        · simp [Finset.sum_ite_eq']
    | zero => exact ⟨0, fun _ => le_refl 0, by simp⟩
    | add vector point _ _ ihx ihy =>
        obtain ⟨cx, hcx, rfl⟩ := ihx
        obtain ⟨cy, hcy, rfl⟩ := ihy
        exact ⟨fun index => cx index + cy index, fun index => add_nonneg (hcx index) (hcy index), by
          simp [add_smul, Finset.sum_add_distrib]⟩
    | smul relation vector _ ih =>
        obtain ⟨coefficients, hc, rfl⟩ := ih
        refine ⟨fun index => (relation : ℝ) * coefficients index, fun index => mul_nonneg relation.2 (hc index), ?_⟩
        have : (relation • ∑ index, coefficients index • (index : Ambient)) = (relation : ℝ) • ∑ index, coefficients index • (index : Ambient) := rfl
        rw [this, Finset.smul_sum]
        exact Finset.sum_congr rfl (fun index _ => by rw [smul_smul])
  ·
    rintro vector ⟨coefficients, hc, rfl⟩
    refine sum_mem (fun index _ => ?_)
    have hk : (index : Ambient) ∈ PointedCone.hull ℝ generators := PointedCone.subset_hull index.2
    have hsm : coefficients index • (index : Ambient) = (⟨coefficients index, hc index⟩ : {coefficients : ℝ // 0 ≤ coefficients}) • (index : Ambient) := rfl
    rw [hsm]
    exact Submodule.smul_mem _ _ hk

theorem hull_isClosed_of_finite {generators : Set Ambient} (hs : generators.Finite) :
    IsClosed (PointedCone.hull ℝ generators : Set Ambient) := by
  classical
  let _ : Fintype generators := hs.fintype
  rw [hull_eq_engine]
  exact fg_cone_isClosed (fun index : generators => (index : Ambient))

theorem PointedCone.FG.isClosed {C : PointedCone ℝ Ambient} (hC : C.FG) :
    IsClosed (C : Set Ambient) := by
  obtain ⟨generators, rfl⟩ := hC
  exact hull_isClosed_of_finite generators.finite_toSet

end LeanPool.Erdos81PaperIContrib
