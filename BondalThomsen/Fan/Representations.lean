module

public import BondalThomsen.Fan.Matrices
public import BondalThomsen.Matroid.UnimodularRepresentations
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

namespace TauCeti.Toric.Fan

open Module BondalThomsen
open scoped TensorProduct

variable {Lattice Ambient Field : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient} [_root_.Field Field]

theorem rayMatroid_eq_coordinates (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    fan.rayMatroid = BondalThomsen.rayMatroid (Field := ℚ)
      (fun ray row => (basis.repr ray.val row : ℚ)) := by
  let rational_basis := basis.baseChange ℚ
  let coordinates := rational_basis.equivFun
  have coordinate_eq : ∀ ray : fan.Ray,
      coordinates ((1 : ℚ) ⊗ₜ[ℤ] ray.val) = fun row => (basis.repr ray.val row : ℚ) := by
    intro ray
    ext row
    simp only [coordinates, Basis.equivFun_apply, rational_basis, Basis.baseChange_repr_tmul,
      zsmul_eq_mul, mul_one]
  have changed := rayMatroid_map_linearEquiv
    (fun ray : fan.Ray => (1 : ℚ) ⊗ₜ[ℤ] ray.val) coordinates
  simp only [coordinate_eq] at changed
  exact changed.symm

theorem rayMatroid_representable (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (deep : fan.IsDeep dimension) (adjacency : FanWallAdjacency fan dimension)
    (generic_cone : FanGenericPositiveCone fan dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    fan.rayMatroid.Representable Field := by
  rw [fan.rayMatroid_eq_coordinates basis]
  exact totallyUnimodular_representable (fan.rayMatrix basis)
    (fan.rayMatrix_totallyUnimodular deep adjacency generic_cone basis cone_basis)

end TauCeti.Toric.Fan
