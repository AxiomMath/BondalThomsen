module

public import Mathlib.Geometry.Convex.Cone.Face.Basic

@[expose] public section

namespace ConvexCone.Salient

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup V]
  [Module R V] [NoZeroSMulDivisors R V] {C : PointedCone R V}

theorem bot_isFaceOf (hC : (C : ConvexCone R V).Salient) :
    (⊥ : PointedCone R V).IsFaceOf C := by
  refine ⟨bot_le, fun {x y a} hx hy ha hxy ↦ ?_⟩
  rw [Submodule.mem_bot] at hxy ⊢
  rw [eq_neg_of_add_eq_zero_right hxy] at hy
  have hzero : a • x = 0 := by
    by_contra h
    exact hC _ (C.smul_mem ha.le hx) h hy
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hzero).resolve_left ha.ne'

end ConvexCone.Salient
