module

public import BondalThomsen.Toric.Frobenius.MultiplicationLineBundlePullback
public import BondalThomsen.Toric.Frobenius.FrobeniusCohomologyAssembly
public import BondalThomsen.Toric.Positivity.PrimitivePairHom

@[expose] public section

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def toricMultiplicationClassPullbackIso
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (divisor_class : fan.InvariantRayDivisorClass) :
    (Scheme.Modules.pullback (fan.toricMultiplication 𝕜 regular degree)).obj
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj ≅
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular
        ((degree : ℤ) • divisor_class)).obj := by
  let divisor := QuotientAddGroup.mk_surjective divisor_class |>.choose
  have representative : fan.invariantRayDivisorClass divisor = divisor_class :=
    (QuotientAddGroup.mk_surjective divisor_class).choose_spec
  have source_iso : (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj :=
    eqToIso (congrArg (fun member =>
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular member).obj) representative.symm) ≪≫
      (fan.invariantClassInvertibleSheaf_iso_divisor 𝕜 complete regular divisor).some
  have target_class : fan.invariantRayDivisorClass (degree • divisor) =
      (degree : ℤ) • divisor_class := by
    rw [map_nsmul, representative, natCast_zsmul]
  exact (Scheme.Modules.pullback (fan.toricMultiplication 𝕜 regular degree)).mapIso source_iso ≪≫
    fan.toricMultiplicationLineBundlePullbackIso 𝕜 complete regular positive divisor ≪≫
    (fan.invariantClassInvertibleSheaf_iso_divisor 𝕜 complete regular (degree • divisor)).some.symm ≪≫
    eqToIso (congrArg (fun member =>
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular member).obj) target_class)

theorem toricMultiplicationInvariantClassPullback
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    fan.ToricMultiplicationInvariantClassPullback 𝕜 complete regular := by
  intro degree positive divisor_class
  exact ⟨fan.toricMultiplicationClassPullbackIso 𝕜 complete regular positive divisor_class⟩

noncomputable def toricFrobeniusExtDecomposition_of_splitting_projection_transport
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (thomsen : fan.ToricMultiplicationResidueDecomposition 𝕜 complete regular)
    (projection : fan.ToricMultiplicationInvertibleProjectionFormula 𝕜 regular)
    (transport : fan.ToricMultiplicationInvariantClassCohomologyTransport 𝕜 complete regular) :
    BondalThomsen.ToricFrobeniusExtDecomposition fan (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass => member)
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular) :=
  fan.toricFrobeniusExtDecomposition_of_geometric_steps 𝕜 complete regular thomsen projection
    (fan.toricMultiplicationInvariantClassPullback 𝕜 complete regular) transport

end TauCeti.Toric.Fan
