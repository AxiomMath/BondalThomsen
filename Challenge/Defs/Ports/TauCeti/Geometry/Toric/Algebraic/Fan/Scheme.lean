module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.AlgebraicGeometry.Gluing
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
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.FaceLocalization
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Regular

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits Multiplicative
variable (𝕜 : Type) [Field 𝕜]
namespace TauCeti.Toric.Fan
universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)
noncomputable def affineToricDiagram : Φ.cones ⥤ Scheme where
  obj σ := Φ.affineToricChart 𝕜 σ
  map {τ σ} f := faceAffineToricSchemeMap 𝕜 Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f))
  map_id _ := faceAffineToricSchemeMap_id 𝕜 _
  map_comp _ _ := (faceAffineToricSchemeMap_comp 𝕜 ..).symm

variable {Φ}
theorem isOpenImmersion_affineToricDiagram_map {τ σ : Φ.cones} (hσ : IsRegularCone i σ.1)
    (f : τ ⟶ σ) : IsOpenImmersion ((Φ.affineToricDiagram 𝕜).map f) :=
  sorry

theorem isLocallyDirected_affineToricDiagram (hΦ : Φ.IsRegular) :
    (Φ.affineToricDiagram 𝕜 ⋙ Scheme.forget).IsLocallyDirected :=
  sorry

variable (Φ)
noncomputable def algebraicRealization (hΦ : Φ.IsRegular) : Scheme :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit (Φ.affineToricDiagram 𝕜)

noncomputable def affineToricChartι (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    Φ.affineToricChart 𝕜 σ ⟶ Φ.algebraicRealization 𝕜 hΦ :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit.ι (Φ.affineToricDiagram 𝕜) σ

noncomputable def affineToricCocone (hΦ : Φ.IsRegular) :
    Cocone (Φ.affineToricDiagram 𝕜) :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit.cocone (Φ.affineToricDiagram 𝕜)

noncomputable def isColimitAffineToricCocone (hΦ : Φ.IsRegular) :
    IsColimit (Φ.affineToricCocone 𝕜 hΦ) :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit.isColimit (Φ.affineToricDiagram 𝕜)

variable {Φ}
variable {𝕜} in
instance isOpenImmersion_affineToricChartι (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    IsOpenImmersion (Φ.affineToricChartι 𝕜 hΦ σ) :=
  sorry

end TauCeti.Toric.Fan
namespace TauCeti.Toric.Fan
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)
end TauCeti.Toric.Fan
namespace TauCeti.Toric.FanHom
universe u
variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V}
  {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
section
variable {N'' : Type u} {V'' : Type*} [AddCommGroup N''] [AddCommGroup V''] [Module ℝ V'']
  {i'' : N'' →+ V''} {Ω : Fan i''}
end
end FanHom
end Toric
end TauCeti
