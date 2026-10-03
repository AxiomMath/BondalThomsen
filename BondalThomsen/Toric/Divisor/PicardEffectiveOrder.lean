module

public import BondalThomsen.Toric.Divisor.PicardEquivalence
public import BondalThomsen.Toric.Divisor.DivisorTensorEquivalence
public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Derived.InvertibleSheafExtCohomology
public import BondalThomsen.Fan.EffectiveRayDivisors

@[expose] public section

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem invertibleSheaf_exists_invariantDivisorRepresentative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    ∃ divisor : fan.InvariantRayDivisor,
      Nonempty (bundle.obj ≅ (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) := by
  obtain ⟨divisor, equality⟩ := fan.invariantDivisorPicard_coefficients_surjective 𝕜
    complete regular (Additive.ofMul (TauCeti.AlgebraicGeometry.LineBundleClass.mk bundle))
  dsimp only at equality
  rw [fan.invariantDivisorPicardRealization_apply 𝕜] at equality
  have class_equality := congrArg Additive.toMul equality
  exact ⟨divisor, TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mp
    class_equality.symm⟩

end TauCeti.Toric.Fan
