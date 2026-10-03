module

public import BondalThomsen.LineBundle.PicardGeometricNef
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryDerivedCohomology
public import BondalThomsen.Classical.Statements
public import BondalThomsen.Collection.FaithfulCollection

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

def DemazureVanishing : Prop :=
  ∀ (Lattice Ambient : Type) [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] (embedding : Lattice →+ Ambient)
    (fan : TauCeti.Toric.Fan embedding) (_complete : fan.IsComplete) (regular : fan.IsRegular),
    letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
      ⟨fan.structureMap 𝕜 regular⟩
    ∀ bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular),
      AlgebraicGeometry.IsNef (baseField := 𝕜) bundle.obj →
      ∀ degree : ℕ, 0 < degree →
        Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology bundle.obj degree)

end BondalThomsen
