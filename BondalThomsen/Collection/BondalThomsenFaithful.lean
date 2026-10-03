module

public import BondalThomsen.Toric.Divisor.PicardFaithfulness
public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import BondalThomsen.Collection.DerivedExceptionalOrder

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

universe derivedUniverse

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def invariantClassInvertibleSheaf (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor_class : fan.InvariantRayDivisorClass) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular) :=
  (TauCeti.AlgebraicGeometry.LineBundleClass.mk_surjective
    (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisor_class))).choose

theorem invariantClassInvertibleSheaf_class (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor_class : fan.InvariantRayDivisorClass) :
    TauCeti.AlgebraicGeometry.LineBundleClass.mk
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class) =
      Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisor_class) :=
  (TauCeti.AlgebraicGeometry.LineBundleClass.mk_surjective _).choose_spec

end TauCeti.Toric.Fan
