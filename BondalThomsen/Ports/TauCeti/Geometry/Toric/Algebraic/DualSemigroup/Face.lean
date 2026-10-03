module

public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Exposed
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Regular
public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Generation

@[expose] public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

theorem neg_mem_dualSemigroup_inf_ker (hi : IsIntegralLattice i) (σ : PointedCone ℝ V)
    (m : N →+ ℤ) :
    -m ∈ dualSemigroup hi (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) := by
  rw [mem_dualSemigroup]
  intro x hx
  have hmx : hi.realCharacter m x = 0 := hx.2
  simp [hmx]

theorem exists_add_nsmul_mem_dualSemigroup (hi : IsIntegralLattice i) (hσ : σ.FG)
    {m : N →+ ℤ} (hm : m ∈ dualSemigroup hi σ) {u : N →+ ℤ}
    (hu : u ∈ dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :
    ∃ n : ℕ, u + n • m ∈ dualSemigroup hi σ := by
  obtain ⟨n, hn⟩ := PointedCone.FG.exists_nonneg_add_nsmul hσ ((mem_dualSemigroup hi m).1 hm)
    fun x hx hmx ↦ (mem_dualSemigroup hi u).1 hu ⟨hx, hmx⟩
  refine ⟨n, (mem_dualSemigroup hi _).2 fun x hx ↦ ?_⟩
  simpa using hn x hx

theorem dualSemigroup_inf_ker_eq_sup (hi : IsIntegralLattice i) (hσ : σ.FG)
    {m : N →+ ℤ} (hm : m ∈ dualSemigroup hi σ) :
    dualSemigroup hi (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) =
      dualSemigroup hi σ ⊔ AddSubmonoid.closure {-m} := by
  refine le_antisymm (fun u hu ↦ ?_) (sup_le (dualSemigroup_anti hi inf_le_left) ?_)
  · obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ hm hu
    refine AddSubmonoid.mem_sup.2 ⟨u + n • m, hn, n • -m,
      AddSubmonoid.mem_closure_singleton.2 ⟨n, rfl⟩, ?_⟩
    rw [smul_neg, add_neg_cancel_right]
  · rw [AddSubmonoid.closure_le, Set.singleton_subset_iff]
    exact neg_mem_dualSemigroup_inf_ker hi σ m

theorem IsRegularCone.exists_mem_dualSemigroup_inf_ker_eq (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {τ : PointedCone ℝ V} (hτ : τ.IsFaceOf σ) :
    ∃ m ∈ dualSemigroup hi σ,
      σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ := by
  classical
  obtain ⟨n, b, r, hb⟩ := hσ.exists_basis
  let m : N →+ ℤ :=
    (b.constr ℤ fun j ↦ if j ∈ Set.range r ∧ i (b j) ∉ τ then 1 else 0).toAddMonoidHom
  have hm : ∀ ρ, m (b (r ρ)) = if i (b (r ρ)) ∈ τ then 0 else 1 := fun ρ ↦ by
    simp only [m, LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis, Set.mem_range_self,
      true_and]
    by_cases h : i (b (r ρ)) ∈ τ <;> simp [h]
  have hgen : σ = PointedCone.hull ℝ (Set.range fun ρ ↦ i (b (r ρ))) := by
    refine (hσ.toIsToricCone.hull_primitiveGenerator hi).symm.trans ?_
    rw [← Set.range_comp]
    congr 2
    funext ρ
    simp [(hb.isPrimitiveGenerator_apply ρ).eq_primitiveGenerator hi hσ.toIsToricCone]
  refine ⟨m, (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ.toIsToricCone
    hb.isPrimitiveGenerator_apply m).2 fun ρ ↦ ?_, ?_⟩
  · rw [hm]
    split_ifs <;> simp
  refine PointedCone.inf_ker_eq_of_eq_hull hgen hτ ?_ ?_
  · rintro _ ⟨ρ, rfl⟩
    rw [hi.realCharacter_apply, hm]
    split_ifs <;> simp
  · rintro _ ⟨ρ, rfl⟩
    rw [hi.realCharacter_apply, hm]
    split_ifs with h <;> simp [h]

end TauCeti.Toric
