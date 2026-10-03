module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Geometry.Convex.Cone.Simplicial
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
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Tactic
public import Challenge.Defs.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Module.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Regular

@[expose] public section
open Set Module
namespace BondalThomsen
end BondalThomsen
namespace TauCeti.Toric.Fan
variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}
def finiteRayHull (fan : TauCeti.Toric.Fan embedding) (rays : Finset fan.Ray) :
    PointedCone ℝ Ambient :=
  PointedCone.hull ℝ ((fun ray : fan.Ray => embedding ray.val) '' (rays : Set fan.Ray))

def IsPrimitiveCollection (fan : TauCeti.Toric.Fan embedding) (rays : Finset fan.Ray) : Prop :=
  rays.Nonempty ∧ fan.finiteRayHull rays ∉ fan.cones ∧
    ∀ subset : Finset fan.Ray, subset.Nonempty → subset ⊂ rays →
      fan.finiteRayHull subset ∈ fan.cones

end TauCeti.Toric.Fan
end
