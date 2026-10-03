module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Set.Finite.Basic
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
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.Lemmas
public import Challenge.Defs.DeepFan.CriterionConverse
public import Challenge.Defs.Fan.Basic
public import Challenge.Defs.Fan.Completeness
public import Challenge.Defs.Fan.PrimitiveCollectionBoundary
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
public import Challenge.Defs.Toric.Divisor.CartierData
public import Challenge.Defs.Toric.Divisor.DivisorArithmetic

@[expose] public section
variable (𝕜 : Type) [Field 𝕜]
namespace TauCeti.Toric
open Multiplicative
variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}
noncomputable def dualCharacterUnit (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    (Multiplicative (dualSemigroup lattice cone))ˣ where
  val := ofAdd ⟨character, positive⟩
  inv := ofAdd ⟨-character, negative⟩
  val_inv := by
    change (⟨character, positive⟩ : dualSemigroup lattice cone) + ⟨-character, negative⟩ = 0
    apply Subtype.ext
    exact add_neg_cancel character
  inv_val := by
    change (⟨-character, negative⟩ : dualSemigroup lattice cone) + ⟨character, positive⟩ = 0
    apply Subtype.ext
    exact neg_add_cancel character

noncomputable def toricMonomialUnit (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    (affineCoordinateRing 𝕜 lattice cone)ˣ :=
  Units.map (MonoidAlgebra.of 𝕜 _) (dualCharacterUnit lattice cone character positive negative)

namespace Fan
open Module Set
end Fan
end TauCeti.Toric
end
