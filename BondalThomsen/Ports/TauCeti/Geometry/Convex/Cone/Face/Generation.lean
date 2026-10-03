module

public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

namespace PointedCone

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] {C : PointedCone R M}

theorem hull_singleton_isFaceOf_of_notMem_hull (hC : (C : ConvexCone R M).Salient)
    {s : Set M} (hs : hull R s = C) {v : M} (hv : v ∈ s) (hvs : v ∉ hull R (s \ {v})) :
    (R ∙₊ v).IsFaceOf C := by
  have hsal : ∀ x ∈ C, -x ∈ C → x = 0 := fun x hx hnx ↦ by
    by_contra h
    exact hC x hx h hnx
  have hvC : v ∈ C := hs ▸ subset_hull hv
  have hsup : C = hull R (s \ {v}) ⊔ R ∙₊ v := by
    rw [← hs, ← Submodule.span_union, Set.sdiff_union_self, Set.union_singleton,
      Set.insert_eq_of_mem hv]
  refine ⟨hs ▸ Submodule.span_mono (Set.singleton_subset_iff.2 hv),
    fun {x y a} hx hy ha hxy ↦ ?_⟩
  rw [hsup] at hx hy
  obtain ⟨d₁, hd₁, w₁, hw₁, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨d₂, hd₂, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨p, hp, rfl⟩ := mem_hull_singleton.1 hw₁
  obtain ⟨q, -, rfl⟩ := mem_hull_singleton.1 hw₂
  obtain ⟨t, -, htv⟩ := mem_hull_singleton.1 hxy
  have hdC : ∀ d ∈ hull R (s \ {v}), d ∈ C := fun d hd ↦
    hs ▸ Submodule.span_mono Set.sdiff_subset hd
  have hd : a • d₁ + d₂ = (t - a * p - q) • v := by
    rw [sub_smul, sub_smul, htv, mul_smul]
    module
  have hc : t - a * p - q ≤ 0 := by
    by_contra hc
    refine hvs ?_
    have hmem : (t - a * p - q)⁻¹ • (a • d₁ + d₂) ∈ hull R (s \ {v}) :=
      smul_mem _ (inv_nonneg.2 (le_of_not_ge hc)) (add_mem (smul_mem _ ha.le hd₁) hd₂)
    rwa [hd, smul_smul, inv_mul_cancel₀ (ne_of_gt (lt_of_not_ge hc)), one_smul] at hmem
  have hneg : -(a • d₁) ∈ C := by
    have h : -(a • d₁) = d₂ + (-(t - a * p - q)) • v := by
      rw [neg_smul, ← hd]
      abel
    rw [h]
    exact add_mem (hdC _ hd₂) (smul_mem _ (neg_nonneg.2 hc) hvC)
  have hzero : a • d₁ = 0 := hsal _ (smul_mem _ ha.le (hdC _ hd₁)) hneg
  rw [(smul_eq_zero.1 hzero).resolve_left ha.ne', zero_add]
  exact mem_hull_singleton.2 ⟨p, hp, rfl⟩

theorem FG.exists_finset_hull_eq_isFaceOf (hfg : C.FG) (hC : (C : ConvexCone R M).Salient) :
    ∃ s : Finset M, hull R (s : Set M) = C ∧ ∀ v ∈ s, v ≠ 0 ∧ (R ∙₊ v).IsFaceOf C := by
  classical
  have hex : ∃ n, ∃ s : Finset M, s.card = n ∧ hull R (s : Set M) = C := by
    obtain ⟨s, hs⟩ := hfg
    exact ⟨_, s, rfl, hs⟩
  obtain ⟨s, hsn, hs⟩ := Nat.find_spec hex
  have hmin : ∀ v ∈ s, v ∉ hull R ((s : Set M) \ {v}) := by
    intro v hv hvs
    refine (Nat.find_min hex (m := (s.erase v).card) ?_) ⟨s.erase v, rfl, ?_⟩
    · rw [← hsn]
      exact Finset.card_erase_lt_of_mem hv
    · rw [Finset.coe_erase]
      refine le_antisymm (hs ▸ Submodule.span_mono Set.sdiff_subset) (hs ▸ Submodule.span_le.2 ?_)
      intro w hw
      by_cases hwv : w = v
      · exact hwv ▸ hvs
      · exact subset_hull ⟨hw, hwv⟩
  refine ⟨s, hs, fun v hv ↦ ⟨?_, hull_singleton_isFaceOf_of_notMem_hull hC hs hv (hmin v hv)⟩⟩
  rintro rfl
  exact hmin 0 hv (zero_mem _)

end PointedCone
