module

public import BondalThomsen.DeepFan.Coordinates
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

namespace BondalThomsen

open Module Finset

variable {Index Lattice Quotient : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Lattice] [AddCommGroup Quotient]

theorem deepCoordinates_without_basis_ray (basis : Basis Index ℤ Lattice)
    (removed : Index) (vector : Lattice)
    (deep : DeepCoordinates (fun index => basis.repr vector index)) :
    DeepCoordinates (fun index : {index : Index // index ≠ removed} =>
      basis.repr vector index.val) :=
  deep.comp Subtype.val Subtype.val_injective

theorem projected_deep_vector_eq_basis (basis : Basis Index ℤ Lattice)
    (removed : Index) (projection : Lattice →ₗ[ℤ] Quotient)
    (killed : projection (basis removed) = 0) (vector : Lattice)
    (deep : DeepCoordinates (fun index => basis.repr vector index))
    (nonnegative : ∀ index, index ≠ removed → 0 ≤ basis.repr vector index)
    (nonzero : projection vector ≠ 0) :
    ∃ chosen : Index, chosen ≠ removed ∧ projection vector = projection (basis chosen) := by
  classical
  let coordinates := fun index : {index : Index // index ≠ removed} =>
    basis.repr vector index.val
  have projected_sum : projection vector =
      ∑ index, basis.repr vector index • projection (basis index) := by
    have equality := congrArg projection (basis.sum_repr vector)
    simpa only [map_sum, map_smul] using equality.symm
  have coordinates_nonzero : coordinates ≠ 0 := by
    intro zero
    apply nonzero
    rw [projected_sum]
    apply sum_eq_zero
    intro index _
    by_cases same : index = removed
    · simp [same, killed]
    · have coordinate_zero := congrFun zero ⟨index, same⟩
      change basis.repr vector index = 0 at coordinate_zero
      rw [coordinate_zero, zero_smul]
  obtain ⟨chosen, coordinates_basis⟩ :=
    (deepCoordinates_without_basis_ray basis removed vector deep).eq_basis_vector_of_nonnegative
      (fun index => nonnegative index.val index.property) coordinates_nonzero
  refine ⟨chosen.val, chosen.property, ?_⟩
  rw [projected_sum, sum_eq_single chosen.val]
  · have chosen_one := coordinates_basis chosen
    simp only [ite_true] at chosen_one
    rw [chosen_one, one_smul]
  · intro index _ distinct
    by_cases same : index = removed
    · simp [same, killed]
    · have coordinate_zero := coordinates_basis ⟨index, same⟩
      have subtype_distinct : (⟨index, same⟩ : {index : Index // index ≠ removed}) ≠ chosen :=
        fun equality => distinct (congrArg Subtype.val equality)
      simp only [subtype_distinct, ite_false] at coordinate_zero
      rw [coordinate_zero, zero_smul]
  · simp

end BondalThomsen
