module

public import BondalThomsen.Toric.Positivity.AmpleGlobalGenerationCriterion
public import BondalThomsen.Toric.RankOne.PicardCohomology
public import BondalThomsen.Toric.Positivity.StrictSupportAmple
public import BondalThomsen.Toric.Scheme.BasisChart
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import BondalThomsen.Toric.Divisor.DivisorTensorEquivalence

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

def negativeRayTwistDivisor (fan : Fan embedding) (divisor : fan.InvariantRayDivisor)
    (ray : fan.Ray) (exponent : ℕ) : fan.InvariantRayDivisor :=
  exponent • divisor - Finsupp.single ray 1

theorem negativeRayTwistDivisor_at_ray (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray) (exponent : ℕ) :
    fan.negativeRayTwistDivisor divisor ray exponent ray =
      (exponent : ℤ) * divisor ray - 1 := by
  simp [negativeRayTwistDivisor]

theorem negativeRayTwist_coneCharacter (fan : Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (ray : fan.Ray) (outside : ray.val ∉ Set.range basis) (exponent : ℕ) :
    fan.coneDivisorCharacter basis coneBasis
        (fan.negativeRayTwistDivisor divisor ray exponent) =
      exponent • fan.coneDivisorCharacter basis coneBasis divisor := by
  classical
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro coordinate
  have distinct : fan.basisRay basis coneBasis coordinate ≠ ray := by
    intro same
    exact outside ⟨coordinate, congrArg Subtype.val same⟩
  change fan.coneDivisorCharacter basis coneBasis
    (fan.negativeRayTwistDivisor divisor ray exponent) (basis coordinate) =
      (exponent • fan.coneDivisorCharacter basis coneBasis divisor) (basis coordinate)
  simp [fan.coneDivisorCharacter_basis, negativeRayTwistDivisor,
    distinct]

variable [FiniteDimensional ℝ Ambient]

theorem negativeRayTwist_not_globallyGenerated_of_supportEquality
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (ray : fan.Ray) (outside : ray.val ∉ Set.range basis)
    (equal : fan.coneDivisorCharacter basis coneBasis divisor ray.val = -divisor ray)
    (exponent : ℕ) :
    ¬ Nonempty (fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.negativeRayTwistDivisor divisor ray exponent)).obj.GeneratingSections := by
  rintro ⟨generators⟩
  have support := fan.hasRaySupportInequalities_of_generatingSections 𝕜 complete regular _ generators
  have impossible := support dimension basis coneBasis ray
  rw [fan.negativeRayTwist_coneCharacter basis coneBasis divisor ray outside exponent] at impossible
  simp only [fan.negativeRayTwistDivisor_at_ray, AddMonoidHom.nsmul_apply,
    equal, Int.nsmul_eq_mul] at impossible
  rw [mul_neg] at impossible
  omega

end TauCeti.Toric.Fan
