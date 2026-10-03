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
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice

@[expose] public section
open AlgebraicGeometry CategoryTheory Multiplicative
variable (𝕜 : Type) [Field 𝕜]
namespace TauCeti.Toric
universe u
variable {V V' V'' : Type*} [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'} {υ : PointedCone ℝ V''}
section CoordinateRing
variable {N N' N'' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
abbrev affineCoordinateRing (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :=
  MonoidAlgebra 𝕜 (Multiplicative (dualSemigroup hi σ))

noncomputable def affineCoordinateRingMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) :
    affineCoordinateRing 𝕜 hi' τ →ₐ[𝕜] (affineCoordinateRing 𝕜) hi σ :=
  MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜
    (AddMonoidHom.toMultiplicative (dualSemigroupMap hi hi' f g hfg hστ))

end CoordinateRing
section Scheme
variable {N N' N'' : Type u} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
noncomputable abbrev affineToricScheme (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    Scheme :=
  Spec (.of (affineCoordinateRing 𝕜 hi σ))

noncomputable def affineToricSchemeMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) :
    affineToricScheme 𝕜 hi σ ⟶ affineToricScheme 𝕜 hi' τ :=
  Spec.map (CommRingCat.ofHom (affineCoordinateRingMap 𝕜 hi hi' f g hfg hστ).toRingHom)

end Scheme
end TauCeti.Toric
end
