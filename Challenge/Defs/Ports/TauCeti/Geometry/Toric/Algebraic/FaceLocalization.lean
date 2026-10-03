module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Challenge.Defs.Ports.TauCeti.Algebra.Module.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.AffineScheme
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Regular

@[expose] public section
open AlgebraicGeometry CategoryTheory Multiplicative
variable (𝕜 : Type) [Field 𝕜]
namespace TauCeti.Toric
universe u
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ : PointedCone ℝ V}
variable {τ υ : PointedCone ℝ V}
noncomputable def faceAffineCoordinateRingMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) : affineCoordinateRing 𝕜 hi σ →ₐ[𝕜] (affineCoordinateRing 𝕜) hi τ :=
  affineCoordinateRingMap 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
    fun _ hx ↦ hτσ.le hx

noncomputable def faceAffineToricSchemeMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) : affineToricScheme 𝕜 hi τ ⟶ affineToricScheme 𝕜 hi σ :=
  affineToricSchemeMap 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
    (show Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) (τ : Set V) (σ : Set V) from
      fun _ hx ↦ hτσ.le hx)

theorem faceAffineToricSchemeMap_def (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap 𝕜 hi hτσ =
      Spec.map (CommRingCat.ofHom (faceAffineCoordinateRingMap 𝕜 hi hτσ).toRingHom) :=
  sorry

@[simp]
theorem faceAffineToricSchemeMap_id (hi : IsIntegralLattice i) :
    faceAffineToricSchemeMap 𝕜 hi (PointedCone.IsFaceOf.refl σ) =
      𝟙 (affineToricScheme 𝕜 hi σ) :=
  sorry

@[simp]
theorem faceAffineToricSchemeMap_comp (hi : IsIntegralLattice i)
    (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap 𝕜 hi hυτ ≫ faceAffineToricSchemeMap 𝕜 hi hτσ =
      faceAffineToricSchemeMap 𝕜 hi (hυτ.trans hτσ) :=
  sorry

namespace IsRegularCone
variable {τ : PointedCone ℝ V}
end IsRegularCone
namespace Fan
variable (Φ : Fan i)
noncomputable abbrev affineToricChart (σ : Φ.cones) : Scheme :=
  affineToricScheme 𝕜 Φ.lattice σ

end Fan
end TauCeti.Toric
end
