module

public import BondalThomsen.Toric.Cohomology.InvertibleProjectionFormula
public import BondalThomsen.Toric.Frobenius.MultiplicationClassPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def toricFrobeniusExtDecomposition_of_splitting_transport
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (thomsen : fan.ToricMultiplicationResidueDecomposition 𝕜 complete regular)
    (transport : fan.ToricMultiplicationInvariantClassCohomologyTransport 𝕜 complete regular) :
    BondalThomsen.ToricFrobeniusExtDecomposition fan (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass => member)
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular) :=
  fan.toricFrobeniusExtDecomposition_of_splitting_projection_transport 𝕜 complete regular
    thomsen (fan.toricMultiplicationInvertibleProjectionFormula 𝕜 regular) transport

end TauCeti.Toric.Fan
