module

public import BondalThomsen.Toric.Divisor.DivisorInternalHom
public import BondalThomsen.Derived.SheafExtCohomologyDimensionShift

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
  TauCeti.AlgebraicGeometry.Scheme.Modules

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def invariantDivisorExtCohomologyEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor) (degree : ℕ) :
    Abelian.Ext (fan.invariantDivisorLineBundle 𝕜 complete regular first).obj
        (fan.invariantDivisorLineBundle 𝕜 complete regular second).obj degree ≃+
      Cohomology (fan.invariantDivisorLineBundle 𝕜 complete regular (second - first)).obj degree := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (BondalThomsen.SheafExtCohomologyDimensionShift.invertibleSheafExtCohomologyEquiv
      (fan.invariantDivisorLineBundle 𝕜 complete regular first)
      (fan.invariantDivisorLineBundle 𝕜 complete regular second).obj degree).trans
    (((cohomologyFunctor (fan.algebraicRealization 𝕜 regular) degree).mapIso
      (fan.invariantDivisorInternalHomDifferenceIso 𝕜 complete regular first second))
        |>.addCommGroupIsoToAddEquiv)

theorem invariantDivisorExt_nontrivial_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor) (degree : ℕ) :
    Nontrivial (Abelian.Ext (fan.invariantDivisorLineBundle 𝕜 complete regular first).obj
      (fan.invariantDivisorLineBundle 𝕜 complete regular second).obj degree) ↔
    Nontrivial (Cohomology
      (fan.invariantDivisorLineBundle 𝕜 complete regular (second - first)).obj degree) :=
  (fan.invariantDivisorExtCohomologyEquiv 𝕜 complete regular first second degree).toEquiv.nontrivial_congr

end TauCeti.Toric.Fan
