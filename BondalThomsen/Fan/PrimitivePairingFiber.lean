module

public import BondalThomsen.Fan.PrimitivePairingAvoidance
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

namespace BondalThomsen.PrimitivePairingFiber

open Set Submodule Finset
open scoped TensorProduct

variable {Lattice Index : Type*} [AddCommGroup Lattice] [Module ℤ Lattice]

theorem lift_mem_dualAnnihilator_iff (vectors : Index → Lattice)
    (pairing : Lattice →ₗ[ℤ] ℚ) :
    pairing.liftBaseChange ℚ ∈
      (span ℚ (Set.range (fun index => (1 : ℚ) ⊗ₜ[ℤ] vectors index))).dualAnnihilator ↔
      ∀ index, pairing (vectors index) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro vanishes index
    simpa only [LinearMap.liftBaseChange_one_tmul] using
      vanishes _ (subset_span (Set.mem_range_self index))
  · intro vanishes vector member
    have contained : span ℚ (Set.range (fun index => (1 : ℚ) ⊗ₜ[ℤ] vectors index)) ≤
        (pairing.liftBaseChange ℚ).ker := by
      apply span_le.mpr
      rintro _ ⟨index, rfl⟩
      apply LinearMap.mem_ker.mpr
      simpa only [LinearMap.liftBaseChange_one_tmul] using vanishes index
    exact contained member

theorem mem_rational_span_iff_forall_vanishing (vectors : Index → Lattice) (vector : Lattice) :
    (1 : ℚ) ⊗ₜ[ℤ] vector ∈
      span ℚ (Set.range (fun index => (1 : ℚ) ⊗ₜ[ℤ] vectors index)) ↔
      ∀ pairing : Lattice →ₗ[ℤ] ℚ,
        (∀ index, pairing (vectors index) = 0) → pairing vector = 0 := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  constructor
  · intro annihilated pairing vanishes
    simpa only [LinearMap.liftBaseChange_one_tmul] using annihilated
      (pairing.liftBaseChange ℚ) ((lift_mem_dualAnnihilator_iff vectors pairing).mpr vanishes)
  · intro annihilated rational_pairing member
    let pairing : Lattice →ₗ[ℤ] ℚ := (LinearMap.liftBaseChangeEquiv ℚ).symm rational_pairing
    have lift_eq : pairing.liftBaseChange ℚ = rational_pairing :=
      (LinearMap.liftBaseChangeEquiv ℚ).apply_symm_apply rational_pairing
    have vanishes : ∀ index, pairing (vectors index) = 0 :=
      (lift_mem_dualAnnihilator_iff vectors pairing).mp (lift_eq.symm ▸ member)
    simpa only [pairing, LinearMap.liftBaseChangeEquiv_symm_apply] using annihilated pairing vanishes

theorem exists_nonzero_vanishing_of_notMem_rational_span (vectors : Index → Lattice)
    (vector : Lattice)
    (outside : (1 : ℚ) ⊗ₜ[ℤ] vector ∉
      span ℚ (Set.range (fun index => (1 : ℚ) ⊗ₜ[ℤ] vectors index))) :
    ∃ variation : PrimitivePairingAvoidance.vanishingDirections vectors,
      variation.1 vector ≠ 0 := by
  have not_all := mt (mem_rational_span_iff_forall_vanishing vectors vector).mpr outside
  push Not at not_all
  obtain ⟨pairing, vanishes, nonzero⟩ := not_all
  exact ⟨⟨pairing, (PrimitivePairingAvoidance.mem_vanishingDirections vectors pairing).mpr
    vanishes⟩, nonzero⟩

end BondalThomsen.PrimitivePairingFiber
