module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Rat.Floor
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.GroupTheory.QuotientGroup.Basic
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
public import Challenge.Defs.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Module.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
public import Challenge.Defs.Ports.TauCeti.Geometry.Toric.Algebraic.Regular

@[expose] public section
namespace TauCeti.Toric.Fan
variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}
abbrev InvariantRayDivisor (fan : TauCeti.Toric.Fan embedding) := fan.Ray →₀ ℤ

noncomputable def invariantDivisorOfCoefficients (fan : TauCeti.Toric.Fan embedding)
    (coefficients : fan.Ray → ℤ) : fan.InvariantRayDivisor :=
  Finsupp.equivFunOnFinite.symm coefficients

noncomputable def principalRayDivisor (fan : TauCeti.Toric.Fan embedding) :
    (Lattice →+ ℤ) →+ fan.InvariantRayDivisor where
  toFun character := fan.invariantDivisorOfCoefficients (fun ray => character ray.val)
  map_zero' := by ext ray; rfl
  map_add' first second := by ext ray; rfl

noncomputable def floorRayDivisor (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) : fan.InvariantRayDivisor :=
  fan.invariantDivisorOfCoefficients (fun ray => ⌊pairing ray.val⌋)

abbrev InvariantRayDivisorClass (fan : TauCeti.Toric.Fan embedding) :=
  fan.InvariantRayDivisor ⧸ fan.principalRayDivisor.range

noncomputable def invariantRayDivisorClass (fan : TauCeti.Toric.Fan embedding) :
    fan.InvariantRayDivisor →+ fan.InvariantRayDivisorClass :=
  QuotientAddGroup.mk' fan.principalRayDivisor.range

noncomputable def floorRayDivisorClass (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) : fan.InvariantRayDivisorClass :=
  fan.invariantRayDivisorClass (fan.floorRayDivisor pairing)

end TauCeti.Toric.Fan
end
