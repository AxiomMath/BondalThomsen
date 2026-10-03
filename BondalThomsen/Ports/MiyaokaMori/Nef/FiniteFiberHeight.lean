module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LocalNormOrderFormula
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Polynomial
open scoped Classical AlgebraicGeometry

universe u

noncomputable section

namespace Ideal

section Fiber

variable {baseRing extensionRing : Type*} [CommRing baseRing] [CommRing extensionRing] [Algebra baseRing extensionRing] (basePrime : Ideal baseRing) [basePrime.IsPrime]

theorem finite_comap_preimage_singleton_of_finite_fiber
    [Module.Finite basePrime.ResidueField (basePrime.Fiber extensionRing)] :
    (PrimeSpectrum.comap (algebraMap baseRing extensionRing) ⁻¹' {⟨basePrime, inferInstance⟩}).Finite :=
  have : IsArtinianRing (basePrime.Fiber extensionRing) := .of_finite basePrime.ResidueField _
  (PrimeSpectrum.preimageEquivFiber baseRing extensionRing ⟨basePrime, inferInstance⟩).finite_iff.mpr
    finite_of_compact_of_discrete

theorem finite_primesOver_of_finite_fiber [Module.Finite basePrime.ResidueField (basePrime.Fiber extensionRing)] :
    (basePrime.primesOver extensionRing).Finite := by
  refine ((finite_comap_preimage_singleton_of_finite_fiber (extensionRing := extensionRing) basePrime).image
    PrimeSpectrum.asIdeal).subset ?_
  exact fun smallerIdeal hJ ↦ ⟨⟨_, hJ.1⟩, PrimeSpectrum.ext hJ.2.1.symm, rfl⟩

theorem eq_of_le_of_liesOver_of_finite_fiber [Module.Finite basePrime.ResidueField (basePrime.Fiber extensionRing)]
    (primeIdeal upperPrime : Ideal extensionRing) [primeIdeal.IsPrime] [upperPrime.IsPrime] [primeIdeal.LiesOver basePrime] [upperPrime.LiesOver basePrime] (equality : primeIdeal ≤ upperPrime) :
    primeIdeal = upperPrime := by
  have : IsArtinianRing (basePrime.Fiber extensionRing) := .of_finite basePrime.ResidueField _
  have hd : _root_.IsDiscrete (PrimeSpectrum.comap (algebraMap baseRing extensionRing) ⁻¹' {⟨basePrime, inferInstance⟩}) :=
    ⟨(PrimeSpectrum.preimageHomeomorphFiber baseRing extensionRing ⟨basePrime, inferInstance⟩).symm.discreteTopology⟩
  have primeEquation : PrimeSpectrum.comap (algebraMap baseRing extensionRing)
      ⟨primeIdeal, inferInstance⟩ = ⟨basePrime, inferInstance⟩ :=
    PrimeSpectrum.ext (primeIdeal.over_def basePrime).symm
  have upperEquation : PrimeSpectrum.comap (algebraMap baseRing extensionRing)
      ⟨upperPrime, inferInstance⟩ = ⟨basePrime, inferInstance⟩ :=
    PrimeSpectrum.ext (upperPrime.over_def basePrime).symm
  have specialization : (⟨primeIdeal, inferInstance⟩ : PrimeSpectrum extensionRing) ⤳
      ⟨upperPrime, inferInstance⟩ := by
    apply (PrimeSpectrum.le_iff_specializes _ _).mp
    exact equality
  exact congrArg PrimeSpectrum.asIdeal
    (hd.eq_of_specializes specialization primeEquation upperEquation)

theorem height_le_of_liesOver_of_finite_fiber [IsNoetherianRing baseRing] [IsNoetherianRing extensionRing]
    [Module.Finite basePrime.ResidueField (basePrime.Fiber extensionRing)]
    (upperPrime : Ideal extensionRing) [upperPrime.IsPrime] [upperPrime.LiesOver basePrime] : upperPrime.height ≤ basePrime.height := by
  refine (Ideal.height_le_height_add_of_liesOver basePrime upperPrime).trans ?_
  have hle : basePrime.map (algebraMap baseRing extensionRing) ≤ upperPrime := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← upperPrime.over_def basePrime]
  have hprime : (upperPrime.map (Ideal.Quotient.mk (basePrime.map (algebraMap baseRing extensionRing)))).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hle
  suffices h0 : (upperPrime.map (Ideal.Quotient.mk (basePrime.map (algebraMap baseRing extensionRing)))).height = 0 by
    rw [h0, add_zero]
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨hprime, bot_le⟩, fun smallerIdeal ⟨hJ, _⟩ hJQ ↦ ?_⟩
  have hsurj : Function.Surjective (Ideal.Quotient.mk (basePrime.map (algebraMap baseRing extensionRing))) :=
    Ideal.Quotient.mk_surjective
  set smallerPrime := smallerIdeal.comap (Ideal.Quotient.mk (basePrime.map (algebraMap baseRing extensionRing))) with hQ''
  have : smallerPrime.IsPrime := Ideal.comap_isPrime _ _
  have hQ''Q : smallerPrime ≤ upperPrime := by
    intro generators hs
    have h1 : Ideal.Quotient.mk _ generators ∈ upperPrime.map (Ideal.Quotient.mk (basePrime.map (algebraMap baseRing extensionRing))) :=
      hJQ hs
    rw [Ideal.mem_map_iff_of_surjective _ hsurj] at h1
    obtain ⟨remainingGenerators, ht, hts⟩ := h1
    have : remainingGenerators - generators ∈ basePrime.map (algebraMap baseRing extensionRing) := by
      rw [← Ideal.Quotient.eq]; exact hts
    have := upperPrime.sub_mem ht (hle this)
    simpa using this
  have hle'' : basePrime.map (algebraMap baseRing extensionRing) ≤ smallerPrime := by
    intro generators hs
    show Ideal.Quotient.mk _ generators ∈ smallerIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs]; exact smallerIdeal.zero_mem
  have : smallerPrime.LiesOver basePrime := by
    refine ⟨le_antisymm ?_ ?_⟩
    · rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap]; exact hle''
    · rw [upperPrime.over_def basePrime]; exact Ideal.comap_mono hQ''Q
  have heq : smallerPrime = upperPrime := eq_of_le_of_liesOver_of_finite_fiber basePrime smallerPrime upperPrime hQ''Q
  rw [← heq, hQ'', Ideal.map_comap_of_surjective _ hsurj]

end Fiber

section Step

variable {baseRing extensionRing : Type*} [CommRing baseRing] [IsDomain baseRing] [IsNoetherianRing baseRing] [CommRing extensionRing] [IsDomain extensionRing]
  [Algebra baseRing extensionRing] [FaithfulSMul baseRing extensionRing]

theorem liesOver_map_C (basePrime : Ideal baseRing) : (basePrime.map (C : baseRing →+* baseRing[X])).LiesOver basePrime := ⟨by
  ext element
  rw [Ideal.under_def, Ideal.mem_comap, Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
  refine ⟨fun equality dimension ↦ ?_, fun equality ↦ by simpa using equality 0⟩
  rw [Polynomial.coeff_C]; split_ifs
  · exact equality
  · exact basePrime.zero_mem⟩

theorem height_map_C_le_one (basePrime : Ideal baseRing) [basePrime.IsPrime] (h𝔮 : basePrime.height = 1) :
    (basePrime.map (C : baseRing →+* baseRing[X])).height ≤ 1 := by
  have hprime : (basePrime.map (C : baseRing →+* baseRing[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hlo : (basePrime.map (C : baseRing →+* baseRing[X])).LiesOver basePrime := liesOver_map_C basePrime
  refine (Ideal.height_le_height_add_of_liesOver basePrime (basePrime.map (C : baseRing →+* baseRing[X]))).trans ?_
  rw [h𝔮, Polynomial.algebraMap_eq, Ideal.map_quotient_self]
  have : Nontrivial (baseRing[X] ⧸ basePrime.map (C : baseRing →+* baseRing[X])) :=
    Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
  rw [Ideal.height_bot, add_zero]

theorem finite_fiber_of_adjoin_singleton (generator : extensionRing) (hx : Algebra.adjoin baseRing {generator} = ⊤)
    (halg : IsAlgebraic baseRing generator) (basePrime : Ideal baseRing) [basePrime.IsPrime] (h𝔮 : basePrime.height = 1) :
    Module.Finite basePrime.ResidueField (basePrime.Fiber extensionRing) := by
  let ringMap : baseRing[X] →ₐ[baseRing] extensionRing := Polynomial.aeval generator
  have hφ : Function.Surjective ringMap := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval, hx]
  have hPprime : (RingHom.ker (ringMap : baseRing[X] →+* extensionRing)).IsPrime := RingHom.ker_isPrime _
  have hPne : RingHom.ker (ringMap : baseRing[X] →+* extensionRing) ≠ ⊥ := by
    obtain ⟨polynomial, hg0, hg⟩ := halg
    intro equality
    have : polynomial ∈ RingHom.ker (ringMap : baseRing[X] →+* extensionRing) := hg
    rw [equality, Ideal.mem_bot] at this
    exact hg0 this

  have hnot : ¬ RingHom.ker (ringMap : baseRing[X] →+* extensionRing) ≤ basePrime.map (C : baseRing →+* baseRing[X]) := by
    intro hle
    have hprime : (basePrime.map (C : baseRing →+* baseRing[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime
    have h𝔮ne : basePrime ≠ ⊥ := by
      rintro rfl; simp at h𝔮
    obtain ⟨element, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮ne
    have hlt : RingHom.ker (ringMap : baseRing[X] →+* extensionRing) < basePrime.map (C : baseRing →+* baseRing[X]) := by
      refine lt_of_le_of_ne hle fun heq ↦ ?_
      have h1 : C element ∈ RingHom.ker (ringMap : baseRing[X] →+* extensionRing) := heq ▸ Ideal.mem_map_of_mem _ ha
      rw [RingHom.mem_ker] at h1
      have h2 : algebraMap baseRing extensionRing element = 0 := by simpa [ringMap] using h1
      exact ha0 ((FaithfulSMul.algebraMap_injective baseRing extensionRing) (by simpa using h2))
    have h1 : (1 : ℕ∞) ≤ (RingHom.ker (ringMap : baseRing[X] →+* extensionRing)).height := by
      rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hPne
    have h2 := height_map_C_le_one basePrime h𝔮
    have hfin : (RingHom.ker (ringMap : baseRing[X] →+* extensionRing)).height ≠ ⊤ := Ideal.height_ne_top hPprime.ne_top
    have h3 := Ideal.height_strict_mono_of_isPrime hlt
    exact absurd (h1.trans_lt (h3.trans_le h2)) (lt_irrefl _)
  obtain ⟨polynomial, hgP, hg𝔮⟩ := Set.not_subset.mp hnot
  let residueField := basePrime.ResidueField
  let ideal : Ideal residueField[X] := (RingHom.ker (ringMap : baseRing[X] →+* extensionRing)).map (mapRingHom (algebraMap baseRing residueField))
  let residuePolynomial : residueField[X] := polynomial.map (algebraMap baseRing residueField)
  have hgb0 : residuePolynomial ≠ 0 := by
    intro h0
    apply hg𝔮
    rw [SetLike.mem_coe, Ideal.mem_map_C_iff]
    intro dimension
    have : (residuePolynomial.coeff dimension) = 0 := by rw [h0]; simp
    rw [Polynomial.coeff_map] at this
    exact (Ideal.algebraMap_residueField_eq_zero).mp this
  have hgbI : residuePolynomial ∈ ideal := Ideal.mem_map_of_mem _ hgP
  have hfin1 : Module.Finite residueField (residueField[X] ⧸ Ideal.span {residuePolynomial}) :=
    (AdjoinRoot.powerBasis hgb0).finite
  have hle : Ideal.span {residuePolynomial} ≤ ideal := (Ideal.span_singleton_le_iff_mem ideal).mpr hgbI
  have hfin2 : Module.Finite residueField (residueField[X] ⧸ ideal) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ residueField hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  exact Module.Finite.equiv (Polynomial.fiberEquivQuotient ringMap hφ basePrime).symm.toLinearEquiv

end Step

end Ideal

end
