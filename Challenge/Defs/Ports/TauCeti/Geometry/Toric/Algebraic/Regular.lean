module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Challenge.Defs.Ports.TauCeti.Algebra.Module.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive

@[expose] public section
namespace TauCeti.Toric
variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {σ τ : PointedCone ℝ V}
structure IsExtendingBasis (i : N →+ V) {σ : PointedCone ℝ V} {n : ℕ}
    (b : Module.Basis (Fin n) ℤ N) (r : ToricRay σ ↪ Fin n) : Prop where

  isPrimitiveGenerator_apply : ∀ ρ : ToricRay σ, IsPrimitiveGenerator i ρ (b (r ρ))

structure IsRegularCone (i : N →+ V) (σ : PointedCone ℝ V) : Prop extends IsToricCone i σ where

  exists_basis : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (r : ToricRay σ ↪ Fin n),
    IsExtendingBasis i b r

namespace IsRegularCone
end IsRegularCone
namespace IsExtendingBasis
variable {n n' : ℕ} {b : Module.Basis (Fin n) ℤ N} {b' : Module.Basis (Fin n') ℤ N}
  {r : ToricRay σ ↪ Fin n} {r' : ToricRay σ ↪ Fin n'}
end IsExtendingBasis
namespace IsRegularCone
end IsRegularCone
namespace Fan
def IsRegular (Φ : Fan i) : Prop := ∀ ⦃σ⦄, σ ∈ Φ.cones → IsRegularCone i σ

@[simp]
theorem isRegular_iff {Φ : Fan i} :
    Φ.IsRegular ↔ ∀ σ ∈ Φ.cones, IsRegularCone i σ :=
  sorry

end Fan
end TauCeti.Toric
end
