module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp

@[expose] public section

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {N N' : Type*}
  [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']

@[simp]
lemma finsuppScalarLeft_lTensor_apply (g : N →ₗ[R] N') (t : (ι →₀ R) ⊗[R] N) (i : ι) :
    finsuppScalarLeft R N' ι (g.lTensor _ t) i = g (finsuppScalarLeft R N ι t i) := by
  induction t using TensorProduct.inductionOn with
  | tmul p n => simp
  | add a b ha hb => simp [ha, hb]

lemma sum_single_tmul_finsuppScalarLeft (t : (ι →₀ R) ⊗[R] N) :
    ∑ i ∈ (finsuppScalarLeft R N ι t).support,
      Finsupp.single i (1 : R) ⊗ₜ finsuppScalarLeft R N ι t i = t := by
  conv_rhs => rw [← (finsuppScalarLeft R N ι).symm_apply_apply t,
    ← Finsupp.sum_single (finsuppScalarLeft R N ι t)]
  simp [Finsupp.sum, finsuppScalarLeft_symm_apply_single]

end TensorProduct
