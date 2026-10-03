module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section
namespace PointedCone
variable {R M ι : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  {v : ι → M} {A : Set ι} {x : M}
section AddCommMonoid
variable [AddCommMonoid M] [Module R M]
end AddCommMonoid
section AddCommGroup
variable [AddCommGroup M] [Module R M] {C : PointedCone R M}
theorem isFaceOf_hull_image [NoZeroDivisors R] (hv : LinearIndependent R v)
    (hC : C = hull R (Set.range v)) (A : Set ι) : (hull R (v '' A)).IsFaceOf C :=
  sorry

end AddCommGroup
end PointedCone
end
