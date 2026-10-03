module

public import BondalThomsen.Fan.Interior
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem ambient_finrank_eq_basis_card (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) : finrank ℝ Ambient = dimension := by
  rw [← fan.lattice.finrank_eq, finrank_eq_card_basis basis, Fintype.card_fin]

end TauCeti.Toric.Fan
