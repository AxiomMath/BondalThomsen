module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.AffineScheme
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice

@[expose] public section
open AlgebraicGeometry Multiplicative
variable (𝕜 : Type) [Field 𝕜]
namespace TauCeti.Toric
universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}
noncomputable abbrev denseTorusScheme (hi : IsIntegralLattice i) : Scheme :=
  affineToricScheme 𝕜 hi (⊥ : PointedCone ℝ V)

end TauCeti.Toric
end
