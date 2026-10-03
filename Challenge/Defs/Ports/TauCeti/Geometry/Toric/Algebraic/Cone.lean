module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section
namespace TauCeti.Toric
variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {σ τ : PointedCone ℝ V}
def IsLatticeRational (i : N →+ V) (σ : PointedCone ℝ V) : Prop :=
  ∃ s : Finset N, σ = PointedCone.hull ℝ (i '' (s : Set N))

structure IsToricCone (i : N →+ V) (σ : PointedCone ℝ V) : Prop where

  rational : IsLatticeRational i σ

  salient : (σ : ConvexCone ℝ V).Salient

section Map
variable {f : N →+ N'} {g : V →ₗ[ℝ] V'}
end Map
end TauCeti.Toric
end
