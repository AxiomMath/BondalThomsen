module

public import BondalThomsen.Toric.Divisor.PicardCharacterGluing
public import BondalThomsen.ProjectiveBundle.DivisorClasses
public import BondalThomsen.ProjectiveBundle.Scheme

@[expose] public section

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def invariantDivisorPicardEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    fan.InvariantRayDivisorClass ≃+
      Additive (TauCeti.AlgebraicGeometry.LineBundleClass (fan.algebraicRealization 𝕜 regular)) :=
  AddEquiv.ofBijective (fan.invariantDivisorPicardRealization 𝕜 complete regular)
    ⟨fan.invariantDivisorPicardRealization_injective 𝕜 complete regular,
      fan.invariantDivisorPicardRealization_surjective 𝕜 complete regular⟩

@[simp] theorem invariantDivisorPicardEquiv_apply (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor_class : fan.InvariantRayDivisorClass) :
    fan.invariantDivisorPicardEquiv 𝕜 complete regular divisor_class =
      fan.invariantDivisorPicardRealization 𝕜 complete regular divisor_class := rfl

theorem invariantDivisorPicard_coefficients_surjective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    Function.Surjective (fun divisor : fan.InvariantRayDivisor =>
      fan.invariantDivisorPicardRealization 𝕜 complete regular (fan.invariantRayDivisorClass divisor)) :=
  (fan.invariantDivisorPicardRealization_surjective 𝕜 complete regular).comp
    QuotientAddGroup.mk_surjective

end TauCeti.Toric.Fan

