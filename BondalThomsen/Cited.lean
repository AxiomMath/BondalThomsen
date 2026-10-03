module

public import BondalThomsen.Collection.FaithfulCollection
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

set_option autoImplicit false

namespace BondalThomsen

def BondalThomsenGeneration (𝕜 : Type) [Field 𝕜] [IsAlgClosed 𝕜] [CharZero 𝕜] : Prop :=
  ∀ (Lattice Ambient : Type) [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (embedding : Lattice →+ Ambient) (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular),
    FaithfulCollection.fullGeneration 𝕜 fan complete regular

end BondalThomsen
