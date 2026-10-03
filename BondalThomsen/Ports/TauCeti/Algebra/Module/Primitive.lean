module

public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.LinearAlgebra.Unimodular

@[expose] public section

namespace TauCeti

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]

abbrev IsPrimitive (v : M) : Prop := Module.IsUnimodular ℤ v

theorem isPrimitive_def {v : M} : IsPrimitive v ↔ ∃ f : M →ₗ[ℤ] ℤ, f v = 1 :=
  Module.isUnimodular_iff

theorem IsPrimitive.ne_zero {v : M} (h : IsPrimitive v) : v ≠ 0 := by
  rintro rfl
  obtain ⟨f, hf⟩ := isPrimitive_def.mp h
  simp at hf

theorem IsPrimitive.eq_one_of_eq_nsmul {v w : M} (hv : IsPrimitive v) {m : ℕ}
    (hvw : v = m • w) : m = 1 := by
  obtain ⟨f, hf⟩ := isPrimitive_def.mp hv
  rw [hvw, map_nsmul, nsmul_eq_mul] at hf
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hf with h | h
  · exact_mod_cast h.1
  · omega

theorem IsPrimitive.neg {v : M} (h : IsPrimitive v) : IsPrimitive (-v) := by
  obtain ⟨f, hf⟩ := isPrimitive_def.mp h
  exact isPrimitive_def.mpr ⟨-f, by simp [hf]⟩

end TauCeti

namespace Module.Basis

variable {ι M : Type*} [AddCommGroup M] [Module ℤ M]

theorem isPrimitive (b : Module.Basis ι ℤ M) (j : ι) : TauCeti.IsPrimitive (b j) :=
  TauCeti.isPrimitive_def.2 ⟨b.coord j, by simp⟩

end Module.Basis

namespace LinearEquiv

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]

@[simp]
theorem isPrimitive_iff (φ : M ≃ₗ[ℤ] N) {v : M} :
    TauCeti.IsPrimitive (φ v) ↔ TauCeti.IsPrimitive v := by
  rw [TauCeti.isPrimitive_def, TauCeti.isPrimitive_def]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.comp (φ : M →ₗ[ℤ] N), by simpa using hg⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.comp (φ.symm : N →ₗ[ℤ] M), by simpa using hf⟩

end LinearEquiv

namespace TauCeti

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

theorem exists_eq_zsmul_isPrimitive [Module.Free ℤ M] {v : M}
    (hv : v ≠ 0) : ∃ (d : ℤ) (w : M), 0 < d ∧ IsPrimitive w ∧ v = d • w := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ M
  let b : Module.Basis ι ℤ M := Module.Free.chooseBasis ℤ M
  let c : ι →₀ ℤ := b.repr v
  let s : Finset ι := c.support
  let d : ℤ := s.gcd c
  have hc0 : c ≠ 0 := fun h ↦ hv (b.repr.injective (h.trans (map_zero b.repr).symm))
  have hs : s.Nonempty := by
    simpa only [s] using Finsupp.support_nonempty_iff.mpr hc0
  obtain ⟨j, hj⟩ := hs
  have hcj : c j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hd0 : d ≠ 0 := by
    simpa only [d, Finset.gcd_ne_zero_iff] using ⟨j, hj, hcj⟩
  have hd_nonneg : 0 ≤ d := by
    simpa only [d] using (Finset.Int.finsetGcd_nonneg : 0 ≤ s.gcd c)
  have hd : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd0)
  let q : ι → ℤ := fun k ↦ c k / d
  have hq : (Function.support q).Finite := by
    refine s.finite_toSet.subset fun k hk ↦ ?_
    by_contra hks
    have hck : c k = 0 := Finsupp.notMem_support_iff.mp hks
    exact hk (by simp [q, hck])
  let qf : ι →₀ ℤ := Finsupp.ofSupportFinite q hq
  let w : M := b.repr.symm qf
  have hcd (j : ι) : c j = d * q j := by
    by_cases hj : j ∈ s
    · exact (Int.ediv_mul_cancel (Finset.gcd_dvd hj)).symm.trans (mul_comm _ _)
    · have hcj : c j = 0 := Finsupp.notMem_support_iff.mp hj
      simp [q, hcj]
  have hvw : v = d • w := by
    have hrepr : b.repr v = d • qf := by
      ext j
      simp only [Finsupp.smul_apply, qf, Finsupp.ofSupportFinite_coe, smul_eq_mul]
      simpa only [c, d, q] using hcd j
    calc
      v = b.repr.symm (b.repr v) := (b.repr.symm_apply_apply v).symm
      _ = b.repr.symm (d • qf) := congrArg b.repr.symm hrepr
      _ = d • w := by
        simp only [w, LinearEquiv.map_smul]
        exact Int.cast_smul_eq_zsmul ℤ d _
  have hqgcd : s.gcd q = 1 := by
    simpa only [q, d] using Finset.gcd_div_eq_one (s := s) (f := c) hj hcj
  obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul (R := ℤ) s q
  refine ⟨d, w, hd, ?_, hvw⟩
  let f : M →ₗ[ℤ] ℤ := ∑ k ∈ s, a k • b.coord k
  refine isPrimitive_def.2 ⟨f, ?_⟩
  simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, w, b.coord_repr_symm, qf,
    Finsupp.ofSupportFinite_coe, smul_eq_mul]
  simpa only [mul_comm] using (hqgcd.symm.trans ha).symm

theorem IsPrimitive.exists_basis [Module.Free ℤ M] [Module.Finite ℤ M] {v : M}
    (hv : IsPrimitive v) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ M) (j : Fin n), b j = v := by
  obtain ⟨f, hf⟩ := isPrimitive_def.1 hv
  obtain ⟨m, ⟨c⟩⟩ := Submodule.nonempty_basis_of_pid (Module.finBasis ℤ M) (LinearMap.ker f)
  refine ⟨m + 1, Module.Basis.mkFinCons v c ?_ ?_, 0, ?_⟩
  · intro a x hx hax
    have h := congrArg f hax
    simp only [map_add, map_smul, hf, LinearMap.mem_ker.1 hx, map_zero, add_zero, smul_eq_mul,
      mul_one] at h
    exact h
  · exact fun z ↦ ⟨-f z, by simp [LinearMap.mem_ker, hf]⟩
  · simp

end TauCeti
