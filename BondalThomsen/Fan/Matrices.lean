module

public import BondalThomsen.Fan.WallAdjacency
public import BondalThomsen.Matroid.UnimodularCompletion

@[expose] public section

open Module Matrix BondalThomsen

namespace BondalThomsen

theorem integer_basis_det_signed {Lattice Index : Type*} [AddCommGroup Lattice]
    [Fintype Index] [DecidableEq Index] (basis adjacent : Basis Index ℤ Lattice) :
    (basis.toMatrix adjacent).det = 1 ∨ (basis.toMatrix adjacent).det = -1 := by
  rw [← Basis.det_apply]
  exact Int.isUnit_iff.mp (basis.isUnit_det adjacent)

end BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

namespace TauCeti.Toric.Fan

variable (fan : TauCeti.Toric.Fan embedding)

noncomputable def rayMatrix {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice) :
    Matrix (Fin dimension) fan.Ray ℤ := basis.toMatrix (fun ray => ray.val)

theorem rayMatrix_deep {dimension : ℕ} (deep : fan.IsDeep dimension)
    (adjacency : FanWallAdjacency fan dimension) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) : DeepMatrix (fan.rayMatrix basis) := by
  refine ⟨fun ray => deep basis cone_basis ray, fun row ray => ?_⟩
  have trichotomy := fan.deep_ray_coordinate_trichotomy deep adjacency basis cone_basis ray row
  change -1 ≤ basis.repr ray.val row
  rcases trichotomy with equality | equality | equality <;> omega

theorem rayMatrix_full_minor_signed {dimension : ℕ} (deep : fan.IsDeep dimension)
    (adjacency : FanWallAdjacency fan dimension)
    (generic_cone : FanGenericPositiveCone fan dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (rays : Fin dimension → fan.Ray) :
    ((fan.rayMatrix basis).submatrix id rays).det ∈ Set.range SignType.cast := by
  classical
  let vectors := fun index => (rays index).val
  change (basis.toMatrix vectors).det ∈ Set.range SignType.cast
  by_cases zero : (basis.toMatrix vectors).det = 0
  · exact ⟨0, by simpa using zero.symm⟩
  have independent : LinearIndependent ℤ vectors := by
    apply LinearIndependent.of_comp basis.equivFun.toLinearMap
    have columns := Matrix.linearIndependent_cols_of_det_ne_zero zero
    convert columns using 1
    funext index row
    simp only [Function.comp_apply, Matrix.col_apply,
      Basis.toMatrix_apply]
    exact congrFun (basis.equivFun_apply (vectors index)) row
  obtain ⟨adapted, adapted_cone, weights, positive⟩ := generic_cone rays independent
  have deep_matrix : DeepMatrix (adapted.toMatrix vectors) := by
    exact ⟨fun column => deep adapted adapted_cone (rays column), fun row column =>
      (fan.rayMatrix_deep deep adjacency adapted adapted_cone).2 row (rays column)⟩
  have adapted_signed := deepMatrix_det_eq_one_or_neg_one deep_matrix positive
  have transition_signed := integer_basis_det_signed basis adapted
  have factorization : (basis.toMatrix vectors).det =
      (basis.toMatrix adapted).det * (adapted.toMatrix vectors).det := by
    rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix]
  rcases transition_signed with transition | transition <;>
    rcases adapted_signed with adapted_det | adapted_det
  · exact ⟨1, by simp [factorization, transition, adapted_det]⟩
  · exact ⟨-1, by simp [factorization, transition, adapted_det]⟩
  · exact ⟨-1, by simp [factorization, transition, adapted_det]⟩
  · exact ⟨1, by simp [factorization, transition, adapted_det]⟩

theorem rayMatrix_totallyUnimodular {dimension : ℕ} (deep : fan.IsDeep dimension)
    (adjacency : FanWallAdjacency fan dimension)
    (generic_cone : FanGenericPositiveCone fan dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    (fan.rayMatrix basis).IsTotallyUnimodular := by
  apply totallyUnimodular_of_full_minors (fan.rayMatrix basis)
    (fan.basisRay basis cone_basis)
  · exact fan.basisRay_coordinates basis cone_basis
  · exact fan.rayMatrix_full_minor_signed deep adjacency generic_cone basis

end TauCeti.Toric.Fan
