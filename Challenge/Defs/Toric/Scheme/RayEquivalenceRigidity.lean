module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Matrix.Basic
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
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Order.Basic
public import Challenge.Defs.DeepFan.CriterionConverse
public import Challenge.Defs.Fan.Basic
public import Challenge.Defs.Fan.Completeness
public import Challenge.Defs.Fan.PrimitiveCollectionBoundary
public import Challenge.Defs.Ports.TauCeti.Algebra.Module.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Regular
public import Challenge.Defs.ProjectiveBundle.Combinatorics
public import Challenge.Defs.ProjectiveBundle.Fan
public import Challenge.Defs.Toric.Divisor.CartierData
public import Challenge.Defs.Toric.Divisor.DivisorArithmetic

@[expose] public section
namespace BondalThomsen.ToricTransport
open Module Set
variable {SourceLattice TargetLattice SourceAmbient TargetAmbient : Type*}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    {source_embedding : SourceLattice →+ SourceAmbient}
    {target_embedding : TargetLattice →+ TargetAmbient}
structure IntegralRayFanEquiv
    (source : TauCeti.Toric.Fan source_embedding)
    (target : TauCeti.Toric.Fan target_embedding) where
  lattice : SourceLattice ≃ₗ[ℤ] TargetLattice
  ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient
  embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector)
  rays : source.Ray ≃ target.Ray
  ray_vectors : ∀ ray : source.Ray, lattice ray.val = (rays ray).val
  cones : ∀ cone : PointedCone ℝ SourceAmbient,
    cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones

variable {source : TauCeti.Toric.Fan source_embedding}
    {target : TauCeti.Toric.Fan target_embedding}
theorem map_symm_map (linear : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (cone : PointedCone ℝ SourceAmbient) :
    PointedCone.map linear.symm.toLinearMap (PointedCone.map linear.toLinearMap cone) = cone :=
  sorry

def IntegralRayFanEquiv.symm (equivalence : IntegralRayFanEquiv source target) :
    IntegralRayFanEquiv target source where
  lattice := equivalence.lattice.symm
  ambient := equivalence.ambient.symm
  embeddings vector := by
    have equality := equivalence.embeddings (equivalence.lattice.symm vector)
    rw [LinearEquiv.apply_symm_apply] at equality
    rw [← equality, LinearEquiv.symm_apply_apply]
  rays := equivalence.rays.symm
  ray_vectors ray := by
    have equality := equivalence.ray_vectors (equivalence.rays.symm ray)
    rw [Equiv.apply_symm_apply] at equality
    rw [← equality, LinearEquiv.symm_apply_apply]
  cones cone := by
    have membership := equivalence.cones (PointedCone.map equivalence.ambient.symm.toLinearMap cone)
    have inverse_map := map_symm_map equivalence.ambient.symm cone
    simp only [LinearEquiv.symm_symm] at inverse_map
    rw [inverse_map] at membership
    exact membership.symm

section Support
end Support
end BondalThomsen.ToricTransport
end
