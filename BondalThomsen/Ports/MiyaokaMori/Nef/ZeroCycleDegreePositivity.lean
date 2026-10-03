module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ZeroCycleDegree

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

universe u

noncomputable section

namespace AlgebraicGeometry.Intersection

theorem rawZeroCycleDegree_nonneg_of_nonneg {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} (structureMap : scheme ⟶ Spec (CommRingCat.of baseField))
    [IsProper structureMap] (cycle : DimensionCycle scheme 0)
    (nonnegative : ∀ point, 0 ≤ cycle.1 point) :
    0 ≤ rawZeroCycleDegree structureMap cycle := by
  rw [rawZeroCycleDegree_eq_sum]
  exact Finset.sum_nonneg fun point _ =>
    mul_nonneg (nonnegative point) (Int.natCast_nonneg _)

end AlgebraicGeometry.Intersection
