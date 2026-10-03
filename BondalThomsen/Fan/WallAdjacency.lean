module

public import BondalThomsen.Fan.Basic
public import BondalThomsen.DeepFan.Matrices

@[expose] public section

namespace BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

def FanWallAdjacency (fan : TauCeti.Toric.Fan embedding) (dimension : ℕ) : Prop :=
  ∀ basis : Module.Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis basis →
    ∀ index, ∃ adjacent : Module.Basis (Fin dimension) ℤ Lattice,
      fan.IsConeBasis adjacent ∧ ∀ vector : Lattice,
        adjacent.repr vector index = -basis.repr vector index

def FanGenericPositiveCone (fan : TauCeti.Toric.Fan embedding) (dimension : ℕ) : Prop :=
  ∀ rays : Fin dimension → fan.Ray,
    LinearIndependent ℤ (fun index => (rays index).val) →
      ∃ basis : Module.Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis basis ∧
        ∃ weights : Fin dimension → ℝ,
          PositiveCombination (basis.toMatrix (fun index => (rays index).val)) weights

end BondalThomsen
