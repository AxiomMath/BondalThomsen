module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Rat.Floor
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
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
public import Mathlib.Tactic
public import Challenge.Defs.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Module.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.AffineScheme
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.DenseTorus
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.FaceLocalization
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Regular
public import Challenge.Defs.Toric.Divisor.DivisorArithmetic

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits Multiplicative
variable (𝕜 : Type) [Field 𝕜]
namespace TauCeti.Toric.Fan
variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}
noncomputable def chartGlobalSections (fan : Fan embedding) (regular : fan.IsRegular)
    (cone : fan.cones) :
    Γ(fan.algebraicRealization 𝕜 regular, ⊤) →+* affineCoordinateRing 𝕜 fan.lattice cone.val :=
  (Scheme.ΓSpecIso (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val))).hom.hom.comp
    (fan.affineToricChartι 𝕜 regular cone).appTop.hom

noncomputable def structureCocone (fan : Fan embedding) :
    Cocone (fan.affineToricDiagram 𝕜) where
  pt := Spec (CommRingCat.of 𝕜)
  ι := {
    app := fun cone => Spec.map
      (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val)))
    naturality := by
      intro first second inclusion
      change faceAffineToricSchemeMap 𝕜 fan.lattice
        (fan.isFaceOf_of_le second.property first.property (leOfHom inclusion)) ≫
          Spec.map _ = _ ≫ 𝟙 _
      rw [Category.comp_id, faceAffineToricSchemeMap_def, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro coefficient
      exact (faceAffineCoordinateRingMap 𝕜 fan.lattice
        (fan.isFaceOf_of_le second.property first.property (leOfHom inclusion))).commutes coefficient }

noncomputable def structureMap (fan : Fan embedding) (regular : fan.IsRegular) :
    fan.algebraicRealization 𝕜 regular ⟶ Spec (CommRingCat.of 𝕜) :=
  (fan.isColimitAffineToricCocone 𝕜 regular).desc (fan.structureCocone 𝕜)

noncomputable def scalarGlobalSections (fan : Fan embedding) (regular : fan.IsRegular) :
    𝕜 →+* Γ(fan.algebraicRealization 𝕜 regular, ⊤) :=
  (fan.structureMap 𝕜 regular).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv.hom

theorem scalarGlobalSections_bijective (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) : Function.Bijective (fan.scalarGlobalSections 𝕜 regular) :=
  sorry

noncomputable def scalarGlobalFunctionsEquiv (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) : 𝕜 ≃+* Γ(fan.algebraicRealization 𝕜 regular, ⊤) :=
  RingEquiv.ofBijective (fan.scalarGlobalSections 𝕜 regular)
    (fan.scalarGlobalSections_bijective 𝕜 complete regular)

end TauCeti.Toric.Fan
end
