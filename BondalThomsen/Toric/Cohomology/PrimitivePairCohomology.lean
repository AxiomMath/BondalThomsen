module

public import BondalThomsen.Toric.Divisor.DivisorExtCohomology
public import BondalThomsen.Toric.Positivity.PrimitivePairHom

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
  TauCeti.AlgebraicGeometry.Scheme.Modules

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

open scoped Classical

def PrimitiveBoundaryCohomologyNonvanishing (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  ∀ left : Finset fan.Ray, fan.IsPrimitiveCollection left →
    Nontrivial (Cohomology (fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ left then -1 else 0))).obj
      (left.card - 1))

theorem primitiveFloorPair_positiveExt_of_cohomology (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (left : Finset fan.Ray) (pairing moved : Lattice →+ ℚ)
    (difference : fan.floorRayDivisor moved - fan.floorRayDivisor pairing =
      fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ left then -1 else 0))
    (nonvanishing : Nontrivial (Cohomology (fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ left then -1 else 0))).obj
      (left.card - 1))) :
    ∃ extension : Ext
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular (fan.floorRayDivisorClass pairing)).obj
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular (fan.floorRayDivisorClass moved)).obj
      (left.card - 1), extension ≠ 0 := by
  let statement : fan.InvariantRayDivisor → Prop := fun divisor =>
    Nontrivial (Cohomology (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
      (left.card - 1))
  have actual_nonvanishing : statement (fan.floorRayDivisor moved - fan.floorRayDivisor pairing) :=
    difference.symm ▸ nonvanishing
  have divisor_nontrivial := (fan.invariantDivisorExt_nontrivial_iff 𝕜 complete regular
    (fan.floorRayDivisor pairing) (fan.floorRayDivisor moved) (left.card - 1)).mpr
      actual_nonvanishing
  obtain ⟨source_iso⟩ := fan.invariantClassInvertibleSheaf_iso_divisor 𝕜 complete regular
    (fan.floorRayDivisor pairing)
  obtain ⟨target_iso⟩ := fan.invariantClassInvertibleSheaf_iso_divisor 𝕜 complete regular
    (fan.floorRayDivisor moved)
  let source_comparison := ((Abelian.extFunctor (left.card - 1)).mapIso source_iso.op).app
    (fan.invariantClassInvertibleSheaf 𝕜 complete regular (fan.floorRayDivisorClass moved)).obj
  let target_comparison := ((Abelian.extFunctor (left.card - 1)).obj
    (Opposite.op (fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.floorRayDivisor pairing)).obj)).mapIso target_iso
  let comparison := (source_comparison.symm ≪≫ target_comparison).addCommGroupIsoToAddEquiv
  let : Nontrivial (Ext
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular (fan.floorRayDivisorClass pairing)).obj
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular (fan.floorRayDivisorClass moved)).obj
      (left.card - 1)) := comparison.toEquiv.nontrivial_congr.mpr divisor_nontrivial
  exact exists_ne 0

theorem primitiveFloorPairPositiveExt_of_boundaryCohomology (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (boundary_cohomology : fan.PrimitiveBoundaryCohomologyNonvanishing 𝕜 complete regular) :
    fan.PrimitiveFloorPairPositiveExt 𝕜 complete regular := by
  intro left primitive pairing moved difference
  exact fan.primitiveFloorPair_positiveExt_of_cohomology 𝕜 complete regular left pairing moved
    difference (boundary_cohomology left primitive)

theorem primitiveFloorPairSheafComparison_of_boundaryCohomology (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (boundary_cohomology : fan.PrimitiveBoundaryCohomologyNonvanishing 𝕜 complete regular) :
    BondalThomsen.PrimitiveFloorPairSheafComparison fan (fan.algebraicRealization 𝕜 regular)
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular) :=
  fan.primitiveFloorPairSheafComparison_of_positiveExt 𝕜 complete regular
    (fan.primitiveFloorPairPositiveExt_of_boundaryCohomology 𝕜 complete regular boundary_cohomology)

end TauCeti.Toric.Fan
