module

public import BondalThomsen.Fan.QuotientBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

namespace BondalThomsen

open Module
open scoped TensorProduct

variable {Index Lattice : Type*} [AddCommGroup Lattice] [DecidableEq Index]

noncomputable def rationalRayQuotientEquiv (basis : Basis Index ℤ Lattice) (removed : Index)
    (vector : Lattice) (equality : basis removed = vector) :
    ((ℚ ⊗[ℤ] Lattice) ⧸ Submodule.span ℚ {((1 : ℚ) ⊗ₜ[ℤ] vector)}) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] (Lattice ⧸ Submodule.span ℤ {vector})) :=
  (basisVectorQuotient (basis.baseChange ℚ) removed ((1 : ℚ) ⊗ₜ[ℤ] vector)
    (by rw [Basis.baseChange_apply, equality])).equiv
      ((basisVectorQuotient basis removed vector equality).baseChange ℚ) (Equiv.refl _)

@[simp] theorem rationalRayQuotientEquiv_mkQ_tmul (basis : Basis Index ℤ Lattice)
    (removed : Index) (vector : Lattice) (equality : basis removed = vector) (lifted : Lattice) :
    rationalRayQuotientEquiv basis removed vector equality
      ((Submodule.span ℚ {((1 : ℚ) ⊗ₜ[ℤ] vector)}).mkQ ((1 : ℚ) ⊗ₜ[ℤ] lifted)) =
        (1 : ℚ) ⊗ₜ[ℤ] ((Submodule.span ℤ {vector}).mkQ lifted) := by
  let equivalence := rationalRayQuotientEquiv basis removed vector equality
  let rational_projection := (Submodule.span ℚ {((1 : ℚ) ⊗ₜ[ℤ] vector)}).mkQ
  let integral_projection := (Submodule.span ℤ {vector}).mkQ
  have commute :
      (equivalence.toLinearMap.restrictScalars ℤ).comp
        ((rational_projection.restrictScalars ℤ).comp ((TensorProduct.mk ℤ ℚ Lattice) 1)) =
      ((TensorProduct.mk ℤ ℚ (Lattice ⧸ Submodule.span ℤ {vector})) 1).comp
        integral_projection := by
    apply basis.ext
    intro index
    change equivalence (rational_projection ((1 : ℚ) ⊗ₜ[ℤ] basis index)) =
      (1 : ℚ) ⊗ₜ[ℤ] integral_projection (basis index)
    by_cases same : index = removed
    · subst index
      rw [equality]
      have integral_zero : integral_projection vector = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton _)
      have rational_zero : rational_projection ((1 : ℚ) ⊗ₜ[ℤ] vector) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton _)
      rw [integral_zero, rational_zero, map_zero, TensorProduct.tmul_zero]
    · have rational_basis_eq : (basis.baseChange ℚ) removed = (1 : ℚ) ⊗ₜ[ℤ] vector := by
        rw [Basis.baseChange_apply, equality]
      rw [← Basis.baseChange_apply ℚ basis index]
      change rationalRayQuotientEquiv basis removed vector equality
        ((Submodule.span ℚ {((1 : ℚ) ⊗ₜ[ℤ] vector)}).mkQ ((basis.baseChange ℚ) index)) = _
      rw [← basisVectorQuotient_apply (basis.baseChange ℚ) removed
        ((1 : ℚ) ⊗ₜ[ℤ] vector) rational_basis_eq ⟨index, same⟩]
      unfold rationalRayQuotientEquiv
      rw [Basis.equiv_apply, Equiv.refl_apply, Basis.baseChange_apply,
        basisVectorQuotient_apply]
  exact DFunLike.congr_fun commute lifted

end BondalThomsen
