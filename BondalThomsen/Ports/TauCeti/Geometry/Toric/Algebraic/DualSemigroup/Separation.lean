module

public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Alternative
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Face
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic

@[expose] public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ τ : PointedCone ℝ V}

theorem hull_inf_ker_eq_of_sum_nsmul_mem (hi : IsIntegralLattice i) {s : Finset N}
    {F : PointedCone ℝ V} (hF : F.IsFaceOf (PointedCone.hull ℝ (i '' s))) {m : N →+ ℤ}
    (hm : ∀ a ∈ s, 0 ≤ m a) (hmF : ∀ v ∈ F, hi.realCharacter m v = 0) (c : s → ℕ)
    (hc : ∑ a : s, c a • i a ∈ F) (hpos : ∀ a : s, m a = 0 → 0 < c a) :
    PointedCone.hull ℝ (i '' s) ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) =
      F := by
  refine PointedCone.inf_ker_eq_of_eq_hull rfl hF ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [hi.realCharacter_apply]
    exact_mod_cast hm a ha
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨fun h0 ↦ ?_, hmF _⟩
    rw [hi.realCharacter_apply, Int.cast_eq_zero] at h0
    refine hF.mem_of_sum_smul_mem
      (fun a : s ↦ PointedCone.subset_hull (Set.mem_image_of_mem i a.2))
      (fun _ ↦ Nat.cast_nonneg _) ?_ ⟨a, ha⟩ (Nat.cast_pos.2 (hpos ⟨a, ha⟩ h0))
    simpa only [Nat.cast_smul_eq_nsmul] using hc

theorem exists_mem_dualSemigroup_neg_mem_dualSemigroup_inf_ker_eq (hi : IsIntegralLattice i)
    (hσ : IsLatticeRational i σ) (hτ : IsLatticeRational i τ) (hστ : (σ ⊓ τ).IsFaceOf σ)
    (hτσ : (σ ⊓ τ).IsFaceOf τ) :
    ∃ m ∈ dualSemigroup hi σ, -m ∈ dualSemigroup hi τ ∧
      σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = σ ⊓ τ ∧
      τ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = σ ⊓ τ := by
  have := hi.free
  have := hi.finite
  obtain ⟨s, rfl⟩ := isLatticeRational_iff.1 hσ
  obtain ⟨t, rfl⟩ := isLatticeRational_iff.1 hτ
  obtain ⟨x, m, hsum, hm, hpos⟩ :=
    exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos
      (Sum.elim (fun a : s ↦ (a : N)) fun b : t ↦ -(b : N))
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, smul_neg, Finset.sum_neg_distrib,
    ← sub_eq_add_neg, sub_eq_zero] at hsum
  have hms : ∀ a ∈ s, 0 ≤ m a := fun a ha ↦ by simpa using hm (.inl ⟨a, ha⟩)
  have hmt : ∀ b ∈ t, 0 ≤ (-m) b := fun b hb ↦ by simpa using hm (.inr ⟨b, hb⟩)
  have hF : ∀ v ∈ PointedCone.hull ℝ (i '' s) ⊓ PointedCone.hull ℝ (i '' t),
      hi.realCharacter m v = 0 := fun v hv ↦ by
    have h₁ := (mem_dualSemigroup hi m).1 ((mem_dualSemigroup_hull_image hi _ m).2 hms) hv.1
    have h₂ := (mem_dualSemigroup hi (-m)).1 ((mem_dualSemigroup_hull_image hi _ _).2 hmt) hv.2
    rw [map_neg, LinearMap.neg_apply, neg_nonneg] at h₂
    exact le_antisymm h₂ h₁
  have heq : ∑ a : s, x (.inl a) • i a = ∑ b : t, x (.inr b) • i b := by
    simp only [← map_nsmul, ← map_sum, hsum]
  have hw : ∑ a : s, x (.inl a) • i a ∈
      PointedCone.hull ℝ (i '' s) ⊓ PointedCone.hull ℝ (i '' t) := by
    refine ⟨?_, heq ▸ ?_⟩ <;>
      exact Submodule.sum_mem _ fun a _ ↦
        nsmul_mem (PointedCone.subset_hull (Set.mem_image_of_mem i a.2)) _
  refine ⟨m, (mem_dualSemigroup_hull_image hi _ m).2 hms,
    (mem_dualSemigroup_hull_image hi _ _).2 hmt,
    hull_inf_ker_eq_of_sum_nsmul_mem hi hστ hms hF _ hw fun a ha ↦ by
      simpa [ha] using hpos (.inl a), ?_⟩
  rw [← LinearMap.ker_neg, ← map_neg]
  refine hull_inf_ker_eq_of_sum_nsmul_mem hi hτσ hmt (fun v hv ↦ ?_) _ (heq ▸ hw) fun b hb ↦ ?_
  · rw [map_neg, LinearMap.neg_apply, hF v hv, neg_zero]
  · simpa [neg_eq_zero.1 hb] using hpos (.inr b)

theorem dualSemigroup_inf_eq_sup (hi : IsIntegralLattice i) (hσ : IsLatticeRational i σ)
    (hτ : IsLatticeRational i τ) (hστ : (σ ⊓ τ).IsFaceOf σ) (hτσ : (σ ⊓ τ).IsFaceOf τ) :
    dualSemigroup hi (σ ⊓ τ) = dualSemigroup hi σ ⊔ dualSemigroup hi τ := by
  refine le_antisymm ?_ (sup_le (dualSemigroup_anti hi inf_le_left)
    (dualSemigroup_anti hi inf_le_right))
  obtain ⟨m, hm, hm', hσm, -⟩ :=
    exists_mem_dualSemigroup_neg_mem_dualSemigroup_inf_ker_eq hi hσ hτ hστ hτσ
  rw [← hσm, dualSemigroup_inf_ker_eq_sup hi hσ.fg hm]
  exact sup_le_sup_left (AddSubmonoid.closure_le.2 (Set.singleton_subset_iff.2 hm')) _

theorem Fan.dualSemigroup_inf_eq_sup (Φ : Fan i) (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) :
    dualSemigroup Φ.lattice (σ ⊓ τ) = dualSemigroup Φ.lattice σ ⊔ dualSemigroup Φ.lattice τ :=
  TauCeti.Toric.dualSemigroup_inf_eq_sup Φ.lattice (Φ.isToricCone hσ).rational
    (Φ.isToricCone hτ).rational (Φ.inf_isFaceOf_left hσ hτ) (Φ.inf_isFaceOf_right hσ hτ)

end TauCeti.Toric
