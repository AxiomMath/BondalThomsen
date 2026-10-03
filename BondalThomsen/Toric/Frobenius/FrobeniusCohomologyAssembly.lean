module

public import BondalThomsen.Collection.BondalThomsenPushforwardExt
public import BondalThomsen.Toric.Divisor.ClassTensorDuality

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def ToricMultiplicationInvertibleProjectionFormula (fan : Fan embedding)
    (regular : fan.IsRegular) : Prop :=
  ∀ degree : ℕ, 0 < degree →
    ∀ bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular),
      Nonempty ((Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).obj
          ((Scheme.Modules.pullback (fan.toricMultiplication 𝕜 regular degree)).obj bundle.obj) ≅
        bundle.obj ⊗ fan.toricMultiplicationPushforward 𝕜 regular degree)

def ToricMultiplicationInvariantClassPullback (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  ∀ degree : ℕ, 0 < degree → ∀ divisor_class : fan.InvariantRayDivisorClass,
    Nonempty ((Scheme.Modules.pullback (fan.toricMultiplication 𝕜 regular degree)).obj
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj ≅
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular
        ((degree : ℤ) • divisor_class)).obj)

def ToricMultiplicationInvariantClassCohomologyTransport (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  ∀ degree : ℕ, 0 < degree → ∀ divisor_class : fan.InvariantRayDivisorClass,
    ∀ cohomology_degree : ℕ,
      Nonempty (Cohomology
        ((Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).obj
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj)
        cohomology_degree ≃+
        Cohomology (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj
          cohomology_degree)

noncomputable def toricMultiplicationInternalHomNegativePowerIso
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projection : fan.ToricMultiplicationInvertibleProjectionFormula 𝕜 regular)
    (pullback : fan.ToricMultiplicationInvariantClassPullback 𝕜 complete regular)
    {degree : ℕ} (positive : 0 < degree) (divisor_class : fan.InvariantRayDivisorClass) :
    (ihom (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj).obj
        (fan.toricMultiplicationPushforward 𝕜 regular degree) ≅
      (Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).obj
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular
          (-((degree : ℤ) • divisor_class))).obj :=
  (fan.invariantClassInternalHomTensorInverseIso 𝕜 complete regular divisor_class).app
      (fan.toricMultiplicationPushforward 𝕜 regular degree) ≪≫
    (projection degree positive
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular (-divisor_class))).some.symm ≪≫
    (Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).mapIso
      ((pullback degree positive (-divisor_class)).some ≪≫
        eqToIso (congrArg (fun member =>
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular member).obj)
            (smul_neg (degree : ℤ) divisor_class)))

noncomputable def toricFrobeniusExtDecomposition_of_geometric_steps
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (thomsen : fan.ToricMultiplicationResidueDecomposition 𝕜 complete regular)
    (projection : fan.ToricMultiplicationInvertibleProjectionFormula 𝕜 regular)
    (pullback : fan.ToricMultiplicationInvariantClassPullback 𝕜 complete regular)
    (transport : fan.ToricMultiplicationInvariantClassCohomologyTransport 𝕜 complete regular) :
    BondalThomsen.ToricFrobeniusExtDecomposition fan (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass => member)
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular) := by
  let witness := fan.toricMultiplicationPushforward_internalHom_cohomology_decomposition 𝕜
    complete regular thomsen
  let degree := witness.choose
  have positive : 0 < degree := witness.choose_spec.1
  let multiplicity := witness.choose_spec.2.choose
  have multiplicities_positive : ∀ member, 0 < multiplicity member :=
    witness.choose_spec.2.choose_spec.1
  have comparisons := witness.choose_spec.2.choose_spec.2.2
  refine
    { multiplication := degree
      multiplication_positive := positive
      multiplicity := multiplicity
      multiplicity_positive := multiplicities_positive
      cohomology_equiv := ?_ }
  intro source cohomology_degree
  let internalHom_negativePower :=
    fan.toricMultiplicationInternalHomNegativePowerIso 𝕜 complete regular projection
      pullback positive source.val
  let cohomology_comparison :=
    ((cohomologyFunctor (fan.algebraicRealization 𝕜 regular) cohomology_degree).mapIso
      internalHom_negativePower).addCommGroupIsoToAddEquiv
  exact ((transport degree positive (-((degree : ℤ) • source.val))
    cohomology_degree).some.symm.trans cohomology_comparison.symm).trans
      (comparisons (fan.invariantClassInvertibleSheaf 𝕜 complete regular source.val)
        cohomology_degree).some

end TauCeti.Toric.Fan
