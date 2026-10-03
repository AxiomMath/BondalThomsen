module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice

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

@[simp]
theorem mem_dualSemigroup (hi : IsIntegralLattice i) (m : N →+ ℤ) :
    m ∈ dualSemigroup hi σ ↔ ∀ ⦃x⦄, x ∈ σ → 0 ≤ hi.realCharacter m x :=
  sorry

@[simp]
theorem dualSemigroup_bot (hi : IsIntegralLattice i) :
    dualSemigroup hi (⊥ : PointedCone ℝ V) = ⊤ :=
  sorry

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

end TauCeti.Toric
end
