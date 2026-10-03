module

public import BondalThomsen.Fan.ConeCoordinates
public import BondalThomsen.Fan.Facets

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem supportingFunctional_eq_sum_realCoordinates (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice) (point : Ambient) :
    fan.supportingFunctional basis point =
      ∑ index, (fan.lattice.isBaseChange.basis basis).repr point index := by
  let real_basis := fan.lattice.isBaseChange.basis basis
  conv_lhs => rw [← real_basis.sum_repr point]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [map_smul, smul_eq_mul]
  have generator_value : fan.supportingFunctional basis (real_basis index) = 1 := by
    change fan.supportingFunctional basis
      ((fan.lattice.isBaseChange.basis basis) index) = 1
    rw [fan.lattice.isBaseChange.basis_apply]
    exact fan.supportingFunctional_basis basis index
  rw [generator_value, mul_one]

end TauCeti.Toric.Fan
