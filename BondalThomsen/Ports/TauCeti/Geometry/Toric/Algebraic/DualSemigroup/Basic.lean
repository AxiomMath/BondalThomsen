module

public import Mathlib.Geometry.Convex.Cone.Dual
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice

@[expose] public section

namespace TauCeti.Toric

variable {N N' N'' V V' V'' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'} {υ : PointedCone ℝ V''}

noncomputable def dualSemigroup (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    AddSubmonoid (N →+ ℤ) :=
  (PointedCone.dual (Module.Dual.eval ℝ V) σ).toAddSubmonoid.comap hi.realCharacter

theorem dualSemigroup_def (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    dualSemigroup hi σ =
      (PointedCone.dual (Module.Dual.eval ℝ V) σ).toAddSubmonoid.comap hi.realCharacter :=
  (rfl)

@[simp]
theorem mem_dualSemigroup (hi : IsIntegralLattice i) (m : N →+ ℤ) :
    m ∈ dualSemigroup hi σ ↔ ∀ ⦃x⦄, x ∈ σ → 0 ≤ hi.realCharacter m x :=
  Iff.rfl

@[gcongr]
theorem dualSemigroup_anti (hi : IsIntegralLattice i) {σ τ : PointedCone ℝ V} (h : σ ≤ τ) :
    dualSemigroup hi τ ≤ dualSemigroup hi σ := by
  intro m hm x hx
  exact hm (h hx)

@[simp]
theorem dualSemigroup_bot (hi : IsIntegralLattice i) :
    dualSemigroup hi (⊥ : PointedCone ℝ V) = ⊤ := by
  ext m
  simp

theorem mem_dualSemigroup_hull_image (hi : IsIntegralLattice i) (s : Set N)
    (m : N →+ ℤ) :
    m ∈ dualSemigroup hi (PointedCone.hull ℝ (i '' s)) ↔
      ∀ n ∈ s, 0 ≤ m n := by
  rw [dualSemigroup_def, AddSubmonoid.mem_comap, PointedCone.dual_hull]
  simp

noncomputable def dualSemigroupMap (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) : dualSemigroup hi' τ →+ dualSemigroup hi σ :=
  (AddMonoidHom.compHom' f).restrict fun m hm ↦ by
    have hcomp : AddMonoidHom.compHom' f m = m.comp f := by
      ext n
      simp
    rw [SetLike.mem_coe, hcomp, mem_dualSemigroup, hi.realCharacter_comp hi' f g hfg]
    intro x hx
    exact (mem_dualSemigroup hi' m).1 hm (hστ hx)

@[simp]
theorem dualSemigroupMap_apply (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) (m : dualSemigroup hi' τ) (n : N) :
    (dualSemigroupMap hi hi' f g hfg hστ m : N →+ ℤ) n = (m : N' →+ ℤ) (f n) :=
  by simp [dualSemigroupMap, AddMonoidHom.restrict]

@[simp]
theorem coe_dualSemigroupMap_id (hi : IsIntegralLattice i) {σ' : PointedCone ℝ V}
    (hσσ' : Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) σ σ') (m : dualSemigroup hi σ') :
    (dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) hσσ' m : N →+ ℤ) =
      m := by
  ext n
  simp

@[simp]
theorem dualSemigroupMap_id (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      (Set.mapsTo_id _) = AddMonoidHom.id (dualSemigroup hi σ) := by
  ext m n
  simp only [dualSemigroupMap_apply, AddMonoidHom.id_apply]

theorem dualSemigroupMap_comp (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (hi'' : IsIntegralLattice i'') (f : N →+ N') (f' : N' →+ N'')
    (g : V →ₗ[ℝ] V') (g' : V' →ₗ[ℝ] V'')
    (hfg : ∀ n, g (i n) = i' (f n)) (hf'g' : ∀ n, g' (i' n) = i'' (f' n))
    (hστ : Set.MapsTo g σ τ) (hτυ : Set.MapsTo g' τ υ) :
    dualSemigroupMap hi hi'' (f'.comp f) (g'.comp g)
        (fun n ↦ by simp [hfg, hf'g']) (hτυ.comp hστ) =
      (dualSemigroupMap hi hi' f g hfg hστ).comp
        (dualSemigroupMap hi' hi'' f' g' hf'g' hτυ) := by
  ext m n
  simp only [dualSemigroupMap_apply, AddMonoidHom.comp_apply]

end TauCeti.Toric
