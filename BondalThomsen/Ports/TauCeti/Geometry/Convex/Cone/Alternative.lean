module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

@[expose] public section

namespace TauCeti

variable {ι K V : Type*}

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V] [Module K V]

theorem exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at_of_finset [DecidableEq ι]
    (k : ι)
    (s : Finset ι) (a : ι → V) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, (∀ j ∈ insert k s, 0 ≤ x j ∧ 0 ≤ y (a j)) ∧
      ∑ j ∈ insert k s, x j • a j = 0 ∧ 0 < x k + y (a k) := by
  induction s using Finset.induction_on generalizing a with
  | empty =>
    by_cases ha : a k = 0
    · exact ⟨Pi.single k 1, 0, by simp, by simp [ha], by simp⟩
    · obtain ⟨y, hy⟩ := Module.Projective.exists_dual_eq_one K ha
      exact ⟨0, y, by simp [hy], by simp, by simp [hy]⟩
  | insert n s hn ih =>
    by_cases hnk : n = k
    · subst hnk
      simpa only [Finset.insert_idem] using ih a
    have hn' : n ∉ insert k s := by simp [hn, hnk]
    have hne : ∀ j ∈ insert k s, j ≠ n := fun j hj h => hn' (h ▸ hj)
    rw [Finset.insert_comm]
    obtain ⟨x, y, hxy, hsum, hpos⟩ := ih a
    by_cases hy : 0 ≤ y (a n)
    ·
      refine ⟨Function.update x n 0, y, ?_, ?_, ?_⟩
      · rintro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simp [hy]
        · simpa [Function.update_of_ne (hne j hj)] using hxy j hj
      · rw [Finset.sum_insert hn', Function.update_self, zero_smul, zero_add, ← hsum]
        exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
      · rwa [Function.update_of_ne (Ne.symm hnk)]
    ·
      push Not at hy
      set d := y (a n)
      have hd : d ≠ 0 := hy.ne
      set c : ι → K := fun j => -y (a j) / d
      have hc : ∀ j ∈ insert k s, 0 ≤ c j := fun j hj =>
        div_nonneg_of_nonpos (neg_nonpos.2 (hxy j hj).2) hy.le
      obtain ⟨u, z, huz, hsum', hpos'⟩ := ih fun j => a j + c j • a n
      set w : Module.Dual K V := z + (-z (a n) / d) • y
      have hw : ∀ j, w (a j) = z (a j + c j • a n) := fun j => by
        simp only [w, c, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
          smul_eq_mul]
        field_simp
      refine ⟨Function.update u n (∑ j ∈ insert k s, c j * u j), w, ?_, ?_, ?_⟩
      · rintro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · refine ⟨?_, ?_⟩
          · rw [Function.update_self]
            exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (huz i hi).1
          · simp only [w, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            rw [div_mul_cancel₀ _ hd, add_neg_cancel]
        · rw [Function.update_of_ne (hne j hj), hw]
          exact huz j hj
      · rw [Finset.sum_insert hn', Function.update_self, ← hsum', Finset.sum_smul]
        simp only [smul_add, smul_smul, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        · exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
        · exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
      · rw [Function.update_of_ne (Ne.symm hnk), hw]
        exact hpos'

theorem exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at [Fintype ι] (a : ι → V) (k : ι) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, 0 ≤ x ∧ ∑ j, x j • a j = 0 ∧ (∀ j, 0 ≤ y (a j)) ∧
      0 < x k + y (a k) := by
  classical
  obtain ⟨x, y, hxy, hsum, hpos⟩ :=
    exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at_of_finset (K := K) k
      (Finset.univ.erase k) a
  rw [Finset.insert_erase (Finset.mem_univ k)] at hxy hsum
  exact ⟨x, y, fun j => (hxy j (Finset.mem_univ j)).1, hsum,
    fun j => (hxy j (Finset.mem_univ j)).2, hpos⟩

theorem exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos [Fintype ι] (a : ι → V) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, 0 ≤ x ∧ ∑ j, x j • a j = 0 ∧ (∀ j, 0 ≤ y (a j)) ∧
      ∀ j, 0 < x j + y (a j) := by
  choose x y hx hsum hy hpos using
    exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at (K := K) a
  refine ⟨∑ k, x k, ∑ k, y k, Finset.sum_nonneg fun k _ ↦ hx k, ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · simp only [Finset.sum_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun k _ ↦ hsum k
  · rw [LinearMap.sum_apply]
    exact Finset.sum_nonneg fun k _ ↦ hy k j
  · rw [Finset.sum_apply, LinearMap.sum_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_pos' (fun k _ ↦ add_nonneg (hx k j) (hy k j)) ⟨j, Finset.mem_univ j, hpos j⟩

end Field

section Int

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

theorem exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos [Fintype ι]
    (a : ι → N) :
    ∃ (x : ι → ℕ) (m : N →+ ℤ), ∑ j, x j • a j = 0 ∧ (∀ j, 0 ≤ m (a j)) ∧
      ∀ j, 0 < (x j : ℤ) + m (a j) := by
  classical
  let b := Module.Free.chooseBasis ℤ N
  let e : N →+ (Module.Free.ChooseBasisIndex ℤ N → ℚ) :=
    { toFun n k := (b.repr n k : ℚ)
      map_zero' := by ext; simp
      map_add' n n' := by ext; simp }
  obtain ⟨X, Y, hX, hsum, hY, hpos⟩ :=
    exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos (K := ℚ) fun j ↦ e (a j)
  obtain ⟨⟨D, hD⟩, hDX⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) X
  obtain ⟨⟨E, hE⟩, hEY⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ)
    fun k ↦ Y (Pi.single k 1)
  choose z hz using hDX
  choose w hw using hEY
  simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at hz hw
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hE' : (0 : ℚ) < E := by exact_mod_cast hE
  let x : ι → ℕ := fun j ↦ (z j).toNat
  have hx : ∀ j, (x j : ℚ) = D * X j := fun j ↦ by
    have : (0 : ℚ) ≤ z j := by rw [hz]; exact mul_nonneg hD'.le (hX j)
    rw [← hz]
    exact_mod_cast Int.toNat_of_nonneg (by exact_mod_cast this)
  let m : N →+ ℤ :=
    { toFun n := ∑ k, w k * b.repr n k
      map_zero' := by simp
      map_add' n n' := by simp [mul_add, Finset.sum_add_distrib] }
  have hm : ∀ n, (m n : ℚ) = E * Y (e n) := fun n ↦ by
    rw [LinearMap.pi_apply_eq_sum_univ, Finset.mul_sum]
    simp only [m, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sum, Int.cast_mul, hw]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [e, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul]
    have hk : (fun j ↦ if k = j then (1 : ℚ) else 0) = Pi.single k 1 := by
      ext j
      simp [Pi.single_apply, eq_comm]
    rw [hk]
    ring
  refine ⟨x, m, ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · apply b.repr.injective
    ext k
    have h := congrFun hsum k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have : ((b.repr (∑ j, x j • a j) k : ℤ) : ℚ) = 0 := by
      rw [← mul_zero (D : ℚ), ← h]
      simp [Finset.mul_sum, e, ← mul_assoc, hx]
    simpa using (by exact_mod_cast this : b.repr (∑ j, x j • a j) k = 0)
  · have : (0 : ℚ) ≤ m (a j) := by
      rw [hm]
      exact mul_nonneg hE'.le (hY j)
    exact_mod_cast this
  · have : (0 : ℚ) < x j + m (a j) := by
      rw [hm, hx]
      have hXj : 0 ≤ X j := hX j
      rcases hXj.lt_or_eq with h | h
      · exact add_pos_of_pos_of_nonneg (mul_pos hD' h)
          (mul_nonneg hE'.le (hY j))
      · rw [← h, mul_zero, zero_add]
        have hYj := hpos j
        rw [← h, zero_add] at hYj
        exact mul_pos hE' hYj
    exact_mod_cast this

end Int

end TauCeti
