module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

namespace ConvexCone.Salient

variable {R V V' : Type*} [Semiring R] [PartialOrder R] [AddCommGroup V] [AddCommGroup V']
  [Module R V] [Module R V']

theorem map {C : ConvexCone R V} {g : V →ₗ[R] V'} (hC : C.Salient)
    (hg : Function.Injective g) : (C.map g).Salient := by
  rintro _ ⟨x, hx, rfl⟩ hne hneg
  obtain ⟨y, hy, hgy⟩ := hneg
  have hyx : y = -x := hg (by rw [map_neg]; exact hgy)
  exact hC x hx (fun h ↦ hne (by simp [h])) (hyx ▸ hy)

theorem prod [IsOrderedRing R] {σ : PointedCone R V} {τ : PointedCone R V'}
    (hσ : (σ : ConvexCone R V).Salient) (hτ : (τ : ConvexCone R V').Salient) :
    ((σ.prod τ : PointedCone R (V × V')) : ConvexCone R (V × V')).Salient := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩ hne ⟨hnx, hny⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact hτ y hy (fun h ↦ hne (by simp [h])) hny
  · exact hσ x hx hx0 hnx

end ConvexCone.Salient

namespace PointedCone

section Hull

variable {R V : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup V] [Module R V]

theorem finrank_span_coe_hull_singleton {x : V} (hx : x ≠ 0) :
    Module.finrank R (Submodule.span R ((hull R {x} : PointedCone R V) : Set V)) = 1 := by
  rw [Submodule.span_span_of_tower (Nonneg R) R, finrank_span_singleton hx]

end Hull

section Prod

variable {R V V' : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid V] [Module R V] [AddCommMonoid V'] [Module R V']

theorem finrank_span_coe_prod_bot (p : PointedCone R V) :
    Module.finrank R (Submodule.span R
        ((p.prod (⊥ : PointedCone R V') : PointedCone R (V × V')) : Set (V × V')))
      = Module.finrank R (Submodule.span R (p : Set V)) := by
  rw [Submodule.prod_coe, Submodule.span_prod_eq R p.zero_mem (Submodule.zero_mem _),
    Submodule.bot_coe, Submodule.span_zero_singleton, ← Submodule.map_inl]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective
    (Submodule.span R (p : Set V))).finrank_eq.symm

theorem finrank_span_coe_bot_prod (q : PointedCone R V') :
    Module.finrank R (Submodule.span R
        (((⊥ : PointedCone R V).prod q : PointedCone R (V × V')) : Set (V × V')))
      = Module.finrank R (Submodule.span R (q : Set V')) := by
  rw [Submodule.prod_coe, Submodule.span_prod_eq R (Submodule.zero_mem _) q.zero_mem,
    Submodule.bot_coe, Submodule.span_zero_singleton, ← Submodule.map_inr]
  exact (Submodule.equivMapOfInjective _ LinearMap.inr_injective
    (Submodule.span R (q : Set V'))).finrank_eq.symm

end Prod

end PointedCone
