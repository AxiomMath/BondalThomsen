module

public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Generation

@[expose] public section

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

variable (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
  (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))

noncomputable def regularDualSemigroupEquiv :
    dualSemigroup hi σ ≃+ (ToricRay σ →₀ ℕ) × (ι →₀ ℤ) :=
  have := ToricRay.finite_of_fg hσ.fg
  have := hi.finite
  have := Module.Finite.finite_basis b
  have : Finite ι := Finite.of_injective (Sum.inr : ι → ToricRay σ ⊕ ι) Sum.inr_injective
  { toFun m := (Finsupp.equivFunOnFinite.symm fun ρ ↦ ((m : N →+ ℤ) (b (Sum.inl ρ))).toNat,
      Finsupp.equivFunOnFinite.symm fun j ↦ (m : N →+ ℤ) (b (Sum.inr j)))
    invFun p := ⟨(b.constr ℤ (Sum.elim (fun ρ ↦ (p.1 ρ : ℤ)) p.2)).toAddMonoidHom,
      (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb _).2 fun ρ ↦ by simp⟩
    left_inv m := by
      have hm := (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb m).1 m.2
      refine Subtype.ext <| AddMonoidHom.toIntLinearMap_injective <| b.ext fun k ↦ ?_
      rcases k with ρ | j
      · simp [hm ρ]
      · simp
    right_inv p := by
      ext ρ <;> simp
    map_add' m m' := by
      have hm := (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb m).1 m.2
      have hm' := (mem_dualSemigroup_iff_of_isPrimitiveGenerator hi hσ hb m').1 m'.2
      refine Prod.ext ?_ ?_
      · ext ρ
        simp [Int.toNat_add (hm ρ) (hm' ρ)]
      · ext j
        simp }

namespace IsRegularCone

theorem nonempty_dualSemigroup_addEquiv (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) :
    Nonempty (dualSemigroup hi σ ≃+
      (ToricRay σ →₀ ℕ) × (Fin (Module.finrank ℤ N - Nat.card (ToricRay σ)) →₀ ℤ)) := by
  classical
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  let _ := ToricRay.finite_of_fg hσ.fg
  let _ := Fintype.ofFinite (ToricRay σ)
  have hl : l = Module.finrank ℤ N - Nat.card (ToricRay σ) := by
    have hrank : Module.finrank ℤ N = Nat.card (ToricRay σ) + l := by
      simpa [Nat.card_sum] using Module.finrank_eq_card_basis b
    omega
  let e := Equiv.sumCongr (Equiv.refl (ToricRay σ)) (finCongr hl)
  exact ⟨regularDualSemigroupEquiv hi hσ.toIsToricCone (b := b.reindex e)
    fun ρ ↦ by simpa [e] using hb ρ⟩

theorem fg_dualSemigroup (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) :
    AddMonoid.FG (dualSemigroup hi σ) := by
  obtain ⟨e⟩ := hσ.nonempty_dualSemigroup_addEquiv hi
  have := ToricRay.finite_of_fg hσ.fg
  have : AddMonoid.FG (Fin (Module.finrank ℤ N - Nat.card (ToricRay σ)) →₀ ℤ) := by
    rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
    infer_instance
  have : AddMonoid.FG (ToricRay σ →₀ ℕ) := by
    rw [← Module.Finite.iff_addMonoid_fg]
    infer_instance
  exact AddMonoid.fg_of_surjective e.symm.toAddMonoidHom e.symm.surjective

end IsRegularCone

end TauCeti.Toric
