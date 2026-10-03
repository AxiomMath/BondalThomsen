module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.Geometry.Convex.Cone.Pointed
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
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Tactic
public import Challenge.Defs.Ports.TauCeti.Algebra.Module.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Regular

namespace BondalThomsen end BondalThomsen
namespace TauCeti end TauCeti
namespace TauCeti.Toric end TauCeti.Toric

@[expose] public section
open Set Module TauCeti.Toric BondalThomsen
open scoped TensorProduct
variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}
namespace TauCeti.Toric.Fan
variable (fan : TauCeti.Toric.Fan embedding)
def Ray := {vector : Lattice // TauCeti.IsPrimitive vector ∧
  PointedCone.hull ℝ {embedding vector} ∈ fan.cones}

instance finiteRay : Finite fan.Ray :=
  sorry

def IsConeBasis {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice) : Prop :=
  PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones

noncomputable def basisRay {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (index : Fin dimension) : fan.Ray := by
  refine ⟨basis index, basis.isPrimitive index, ?_⟩
  have independent : LinearIndependent ℝ (fun index => embedding (basis index)) := by
    convert (fan.lattice.isBaseChange.basis basis).linearIndependent using 1
    funext index
    exact (fan.lattice.isBaseChange.basis_apply basis index).symm
  have face := PointedCone.isFaceOf_hull_image independent rfl {index}
  exact fan.mem_of_isFaceOf cone_basis (by simpa using face)

end TauCeti.Toric.Fan
end
