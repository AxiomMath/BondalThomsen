module

public import BondalThomsen.Ports.TauCeti.Algebra.Module.Primitive
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

open Module Submodule
open scoped TensorProduct

namespace TauCeti

variable {Lattice : Type*} [AddCommGroup Lattice] [Module ℤ Lattice]
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]

theorem IsPrimitive.eq_or_eq_neg_of_rational_span_eq {first second : Lattice}
    (first_primitive : IsPrimitive first) (second_primitive : IsPrimitive second)
    (same_span : span ℚ {(1 : ℚ) ⊗ₜ[ℤ] first} =
      span ℚ {(1 : ℚ) ⊗ₜ[ℤ] second}) :
    first = second ∨ first = -second := by
  classical
  obtain ⟨dimension, basis, chosen, basis_chosen⟩ := first_primitive.exists_basis
  have member : (1 : ℚ) ⊗ₜ[ℤ] second ∈ span ℚ {(1 : ℚ) ⊗ₜ[ℤ] first} := by
    rw [same_span]
    exact subset_span (Set.mem_singleton _)
  obtain ⟨scalar, equality⟩ := mem_span_singleton.mp member
  have zero_coordinates : ∀ row : Fin dimension, row ≠ chosen → basis.repr second row = 0 := by
    intro row different
    have coordinate := congrArg (fun vector => (basis.baseChange ℚ).repr vector row) equality
    rw [← basis_chosen] at coordinate
    simp [Basis.baseChange_repr_tmul, different] at coordinate
    exact_mod_cast coordinate.symm
  have integral_multiple : second = basis.repr second chosen • first := by
    apply basis.ext_elem
    intro row
    rw [← basis_chosen]
    by_cases same : row = chosen
    · subst row
      simp
    · simp [zero_coordinates row same, same]
  obtain ⟨functional, primitive_value⟩ := isPrimitive_def.mp second_primitive
  rw [integral_multiple, map_zsmul, zsmul_eq_mul] at primitive_value
  norm_cast at primitive_value
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp primitive_value with positive | negative
  · left
    simpa [positive.1] using integral_multiple.symm
  · right
    rw [integral_multiple, negative.1]
    simp

theorem IsPrimitive.rational_span_eq_iff {first second : Lattice}
    (first_primitive : IsPrimitive first) (second_primitive : IsPrimitive second) :
    span ℚ {(1 : ℚ) ⊗ₜ[ℤ] first} = span ℚ {(1 : ℚ) ⊗ₜ[ℤ] second} ↔
      first = second ∨ first = -second := by
  constructor
  · exact first_primitive.eq_or_eq_neg_of_rational_span_eq second_primitive
  · rintro (rfl | equality)
    · rfl
    · rw [equality, TensorProduct.tmul_neg]
      simpa using Submodule.span_neg (R := ℚ) {(1 : ℚ) ⊗ₜ[ℤ] second}

end TauCeti
