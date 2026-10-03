module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ResidueWeightedLength
public import BondalThomsen.Ports.MiyaokaMori.Nef.FiniteExtensionNormOrder
public import Mathlib.RingTheory.QuasiFinite.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped Classical BigOperators

universe u v

noncomputable section

theorem Ring.liesOver_maximalIdeal_of_finite {baseRing extensionRing : Type u} [CommRing baseRing] [IsLocalRing baseRing] [CommRing extensionRing]
    [Algebra baseRing extensionRing] [Module.Finite baseRing extensionRing] (maximalPoint : MaximalSpectrum extensionRing) :
    maximalPoint.asIdeal.LiesOver (IsLocalRing.maximalIdeal baseRing) := by
  have : Algebra.IsIntegral baseRing extensionRing := Algebra.IsIntegral.of_finite baseRing extensionRing
  have hmax : (maximalPoint.asIdeal.comap (algebraMap baseRing extensionRing)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap baseRing extensionRing)
      (Algebra.IsIntegral.isIntegral (R := baseRing)) maximalPoint.asIdeal
  exact ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩

theorem Ring.finite_maximalSpectrum_of_finite {baseRing extensionRing : Type u} [CommRing baseRing] [IsLocalRing baseRing] [CommRing extensionRing]
    [Algebra baseRing extensionRing] [Module.Finite baseRing extensionRing] : Finite (MaximalSpectrum extensionRing) := by
  have hfin : ((IsLocalRing.maximalIdeal baseRing).primesOver extensionRing).Finite :=
    Algebra.QuasiFinite.finite_primesOver _
  have := hfin.to_subtype
  let secondMap : MaximalSpectrum extensionRing → (IsLocalRing.maximalIdeal baseRing).primesOver extensionRing := fun maximalPoint =>
    ⟨maximalPoint.asIdeal, maximalPoint.isMaximal.isPrime, Ring.liesOver_maximalIdeal_of_finite maximalPoint⟩
  refine Finite.of_injective secondMap fun maximalPoint m' equality => ?_
  ext1
  exact congrArg Subtype.val equality

theorem Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord
    {baseRing extensionRing baseField extensionField : Type u} [CommRing baseRing] [IsDomain baseRing] [IsLocalRing baseRing] [IsNoetherianRing baseRing]
    [Ring.KrullDimLE 1 baseRing] [CommRing extensionRing] [IsDomain extensionRing] [Algebra baseRing extensionRing] [FaithfulSMul baseRing extensionRing]
    [Module.Finite baseRing extensionRing] [Field baseField] [Algebra baseRing baseField] [IsFractionRing baseRing baseField]
    [Field extensionField] [Algebra extensionRing extensionField] [IsFractionRing extensionRing extensionField] [Algebra baseField extensionField] [Algebra baseRing extensionField]
    [IsScalarTower baseRing baseField extensionField] [IsScalarTower baseRing extensionRing extensionField] (rational : extensionRing) (hy : rational ≠ 0) :
    Ring.ordFrac baseRing (Algebra.norm baseField (algebraMap extensionRing extensionField rational)) =
      WithZero.exp (∑ᶠ maximalPoint : MaximalSpectrum extensionRing,
        (maximalPoint.asIdeal.inertiaDeg baseRing : ℤ) *
          ((Ring.ord (Localization.AtPrime maximalPoint.asIdeal) (algebraMap extensionRing _ rational)).toNat : ℤ)) := by
  have hfinMS : Finite (MaximalSpectrum extensionRing) := Ring.finite_maximalSpectrum_of_finite (baseRing := baseRing)
  have hB : ∀ maximalPoint : MaximalSpectrum extensionRing, maximalPoint.asIdeal.LiesOver (IsLocalRing.maximalIdeal baseRing) :=
    fun maximalPoint => Ring.liesOver_maximalIdeal_of_finite maximalPoint
  have hfin : ∀ maximalPoint : MaximalSpectrum extensionRing,
      maximalPoint.asIdeal.inertiaDeg baseRing ≠ 0 := fun maximalPoint => by
    have := hB maximalPoint
    have := maximalPoint.isMaximal
    exact (Ideal.inertiaDeg_pos maximalPoint.asIdeal baseRing).ne'

  have hLtop : Module.length baseRing (extensionRing ⧸ Ideal.span {rational}) ≠ ⊤ :=
    Ring.length_quotient_span_singleton_ne_top baseRing hy
  have hflA : IsFiniteLength baseRing (extensionRing ⧸ Ideal.span {rational}) := Module.length_ne_top_iff.mp hLtop
  have hflB : IsFiniteLength extensionRing (extensionRing ⧸ Ideal.span {rational}) := by
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hflA ⊢
    exact ⟨isNoetherian_of_tower baseRing hflA.1, isArtinian_of_tower baseRing hflA.2⟩

  have h0 := Module.length_eq_inertiaLengthSum (baseRing := baseRing) hB hfin hflB
  unfold Module.inertiaLengthSum at h0
  simp only [Module.length_localizedModule_quotient_span_singleton] at h0

  rw [Ring.ordFrac_norm_eq_exp_length (baseField := baseField) (extensionField := extensionField) hy]
  congr 1
  have := Fintype.ofFinite (MaximalSpectrum extensionRing)
  rw [finsum_eq_sum_of_fintype] at h0 ⊢
  have hne : ∀ maximalPoint : MaximalSpectrum extensionRing,
      Ring.ord (Localization.AtPrime maximalPoint.asIdeal) (algebraMap extensionRing _ rational) ≠ ⊤ := by
    intro maximalPoint htop
    apply hLtop
    rw [h0, eq_top_iff]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ maximalPoint))
    rw [htop, ENat.mul_top (by exact_mod_cast hfin maximalPoint)]
  have hcoe : ∀ maximalPoint : MaximalSpectrum extensionRing,
      Ring.ord (Localization.AtPrime maximalPoint.asIdeal) (algebraMap extensionRing _ rational) =
        (((Ring.ord (Localization.AtPrime maximalPoint.asIdeal) (algebraMap extensionRing _ rational)).toNat : ℕ) : ℕ∞) :=
    fun maximalPoint => (ENat.natCast_toNat (hne maximalPoint)).symm
  rw [h0, Finset.sum_congr rfl fun maximalPoint _ => by rw [hcoe maximalPoint]]
  simp only [← Nat.cast_mul, ← Nat.cast_sum, ENat.toNat_natCast]

theorem Ring.eq_of_mul_of_eq_on_algebraMap {extensionRing extensionField : Type*} [CommRing extensionRing] [IsDomain extensionRing] [Field extensionField]
    [Algebra extensionRing extensionField] [IsFractionRing extensionRing extensionField] {firstOrder secondOrder : extensionField → ℤ}
    (hF : ∀ first second : extensionField, first ≠ 0 → second ≠ 0 → firstOrder (first * second) = firstOrder first + firstOrder second)
    (hG : ∀ first second : extensionField, first ≠ 0 → second ≠ 0 → secondOrder (first * second) = secondOrder first + secondOrder second)
    (hB : ∀ numerator : extensionRing, numerator ≠ 0 → firstOrder (algebraMap extensionRing extensionField numerator) = secondOrder (algebraMap extensionRing extensionField numerator))
    {rational : extensionField} (hy : rational ≠ 0) : firstOrder rational = secondOrder rational := by
  obtain ⟨numerator, denominator, hb', hyb⟩ := IsFractionRing.div_surjective (A := extensionRing) rational
  have hb'0 : denominator ≠ 0 := nonZeroDivisors.ne_zero hb'
  have hb'L : algebraMap extensionRing extensionField denominator ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective extensionRing extensionField)).mpr hb'0
  have hb0 : numerator ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hyb
    exact hy hyb.symm
  have hmul : rational * algebraMap extensionRing extensionField denominator = algebraMap extensionRing extensionField numerator := by
    rw [← hyb, div_mul_cancel₀ _ hb'L]
  have e1 := hF rational _ hy hb'L
  have e2 := hG rational _ hy hb'L
  rw [hmul] at e1 e2
  rw [hB numerator hb0, hB denominator hb'0] at e1
  linarith

end
