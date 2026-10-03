module

public import BondalThomsen.Toric.Divisor.DivisorTensorEquivalence
public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Derived.InvertibleSheafExtCohomology
public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CartierDivisorHomSections

universe schemeUniverse

variable {scheme : Scheme.{schemeUniverse}} [IsIntegral scheme]

noncomputable def internalHomTensorInverseIso
    (divisor : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor scheme) :
    ihom divisor.sheaf ≅ tensorLeft (-divisor).sheaf :=
  (ihom.adjunction divisor.sheaf).rightAdjointUniq
    (CartierDivisorTensorEquivalence.tensorEquivalence divisor).toAdjunction

noncomputable def internalHomDifferenceIso
    (first second : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor scheme) :
    (ihom first.sheaf).obj second.sheaf ≅ (second - first).sheaf :=
  (internalHomTensorInverseIso first).app second.sheaf ≪≫
    CartierDivisorTensorEquivalence.tensorAddIso (-first) second ≪≫
    eqToIso (congrArg (fun divisor => divisor.sheaf) (neg_add_eq_sub first second))

end BondalThomsen.CartierDivisorHomSections

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def invariantDivisorInternalHomDifferenceIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor) :
    (ihom (fan.invariantDivisorLineBundle 𝕜 complete regular first).obj).obj
        (fan.invariantDivisorLineBundle 𝕜 complete regular second).obj ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular (second - first)).obj := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact BondalThomsen.CartierDivisorHomSections.internalHomDifferenceIso
      (fan.invariantDivisorCartier 𝕜 complete regular first)
      (fan.invariantDivisorCartier 𝕜 complete regular second) ≪≫
    eqToIso (congrArg (fun divisor => divisor.sheaf)
      (map_sub (fan.invariantDivisorCartierHom 𝕜 complete regular) second first).symm)

end TauCeti.Toric.Fan
