module

public import BondalThomsen.Fan.WallGeometry
public import BondalThomsen.Fan.Determination

@[expose] public section

namespace TauCeti.Toric.Fan

open Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem deep_ray_coordinate_trichotomy_of_complete_regular
    (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ} (complete : fan.IsComplete)
    (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (ray : fan.Ray) (index : Fin dimension) :
    basis.repr ray.val index = -1 ∨ basis.repr ray.val index = 0 ∨
      basis.repr ray.val index = 1 :=
  fan.deep_ray_coordinate_trichotomy deep
    (fan.wallAdjacency_of_complete_regular_deep complete regular deep) basis cone_basis ray index

theorem deep_rayMatrix_totallyUnimodular (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) : (fan.rayMatrix basis).IsTotallyUnimodular :=
  fan.rayMatrix_totallyUnimodular_of_complete_regular complete regular deep
    (fan.wallAdjacency_of_complete_regular_deep complete regular deep) basis cone_basis

theorem deep_rayMatroid_representable (fan : TauCeti.Toric.Fan embedding)
    {Field : Type*} [_root_.Field Field] {dimension : ℕ} (complete : fan.IsComplete)
    (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference_basis : Basis (Fin dimension) ℤ Lattice) : fan.rayMatroid.Representable Field := by
  obtain ⟨size, basis, cone_basis, _⟩ :=
    fan.exists_coneBasis_containing complete regular (0 : Ambient)
  have size_eq : size = dimension := by
    have cone_rank := finrank_eq_card_basis basis
    have reference_rank := finrank_eq_card_basis reference_basis
    simp only [Fintype.card_fin] at cone_rank reference_rank
    omega
  subst size
  exact fan.rayMatroid_representable_of_complete_regular complete regular deep
    (fan.wallAdjacency_of_complete_regular_deep complete regular deep) basis cone_basis

end TauCeti.Toric.Fan
