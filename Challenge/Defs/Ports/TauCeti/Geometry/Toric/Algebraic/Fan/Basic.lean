module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice

@[expose] public section
namespace TauCeti.Toric
variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {σ τ : PointedCone ℝ V}
structure Fan (i : N →+ V) where

  lattice : IsIntegralLattice i

  cones : Set (PointedCone ℝ V)

  finite_cones : cones.Finite

  isToricCone : ∀ ⦃σ⦄, σ ∈ cones → IsToricCone i σ

  mem_of_isFaceOf : ∀ ⦃σ τ⦄, σ ∈ cones → τ.IsFaceOf σ → τ ∈ cones

  inf_isFaceOf_left : ∀ ⦃σ τ⦄, σ ∈ cones → τ ∈ cones → (σ ⊓ τ).IsFaceOf σ

namespace Fan
variable (Φ : Fan i)
theorem inf_mem (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) :
    σ ⊓ τ ∈ Φ.cones :=
  sorry

instance : SemilatticeInf Φ.cones :=
  Subtype.semilatticeInf fun _ _ ↦ Φ.inf_mem

instance : Finite Φ.cones :=
  sorry

theorem isFaceOf_of_le (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) (h : τ ≤ σ) : τ.IsFaceOf σ :=
  sorry

theorem bot_mem (hσ : σ ∈ Φ.cones) : (⊥ : PointedCone ℝ V) ∈ Φ.cones :=
  sorry

def support : Set V := ⋃ σ ∈ Φ.cones, (σ : Set V)

def IsComplete : Prop := Φ.support = Set.univ

end Fan
namespace FanHom
variable {Φ : Fan i} {Ψ : Fan i'}
section Comp
variable {N'' V'' : Type*} [AddCommGroup N''] [AddCommGroup V''] [Module ℝ V'']
  {i'' : N'' →+ V''} {Ω : Fan i''}
variable {N''' V''' : Type*} [AddCommGroup N'''] [AddCommGroup V'''] [Module ℝ V''']
  {i''' : N''' →+ V'''} {Θ : Fan i'''}
end Comp
end FanHom
end TauCeti.Toric
end
