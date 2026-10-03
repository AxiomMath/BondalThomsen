module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.SetTheory.Cardinal.ENat

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped nonZeroDivisors

universe u

noncomputable section

namespace MiyaokaMori.RingTheory

theorem ringKrullDim_eq_of_integral_injective
    (baseRing extensionRing : Type u) [CommRing baseRing] [CommRing extensionRing]
    [Algebra baseRing extensionRing] [Algebra.IsIntegral baseRing extensionRing]
    [FaithfulSMul baseRing extensionRing] : ringKrullDim extensionRing = ringKrullDim baseRing := by
  have : Algebra.HasGoingUp baseRing extensionRing := Algebra.HasGoingUp.of_isIntegral
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap baseRing extensionRing))
    intro firstPrime secondPrime strictOrder
    have : firstPrime.asIdeal.IsPrime := firstPrime.isPrime
    have idealOrder : firstPrime.asIdeal < secondPrime.asIdeal := strictOrder
    change firstPrime.asIdeal.comap (algebraMap baseRing extensionRing) <
      secondPrime.asIdeal.comap (algebraMap baseRing extensionRing)
    exact Ideal.IsIntegral.under_lt_under (R := baseRing) idealOrder
  · change (⨆ chain : LTSeries (PrimeSpectrum baseRing), (chain.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun chain => ?_
    obtain ⟨liftedPrime, liftedEquality⟩ :=
      (Algebra.IsIntegral.comap_surjective baseRing extensionRing) chain.head
    have : liftedPrime.asIdeal.IsPrime := liftedPrime.isPrime
    have : liftedPrime.asIdeal.LiesOver chain.head.asIdeal :=
      ⟨(congrArg PrimeSpectrum.asIdeal liftedEquality).symm⟩
    obtain ⟨liftedChain, lengthEquality, _, _⟩ :=
      Ideal.exists_ltSeries_of_hasGoingUp chain liftedPrime.asIdeal
    rw [← lengthEquality]
    exact Order.LTSeries.length_le_krullDim liftedChain

theorem finiteTypeDomain_ringKrullDim_eq_trdeg
    (baseField coordinateRing : Type u) [Field baseField] [CommRing coordinateRing]
    [IsDomain coordinateRing] [Algebra baseField coordinateRing]
    [Algebra.FiniteType baseField coordinateRing] :
    ringKrullDim coordinateRing =
      (Cardinal.toENat (Algebra.trdeg baseField coordinateRing) : WithBot ℕ∞) := by
  obtain ⟨dimension, normalization, normalizationInjective, normalizationIntegral⟩ :=
    exists_integral_inj_algHom_of_fg baseField coordinateRing
  let polynomialRing := MvPolynomial (Fin dimension) baseField
  let : Algebra polynomialRing coordinateRing := normalization.toRingHom.toAlgebra
  have : Algebra.IsIntegral polynomialRing coordinateRing := ⟨normalizationIntegral⟩
  have : FaithfulSMul polynomialRing coordinateRing :=
    (faithfulSMul_iff_algebraMap_injective polynomialRing coordinateRing).mpr normalizationInjective
  have : IsScalarTower baseField polynomialRing coordinateRing := IsScalarTower.of_algHom normalization
  have relativeTrdegZero : Algebra.trdeg polynomialRing coordinateRing = 0 := trdeg_eq_zero
  have polynomialTrdeg : Algebra.trdeg baseField polynomialRing = (dimension : Cardinal.{u}) := by
    simp [polynomialRing]
  have coordinateTrdeg : Algebra.trdeg baseField coordinateRing = (dimension : Cardinal.{u}) := by
    simpa only [relativeTrdegZero, polynomialTrdeg, add_zero] using
      (trdeg_add_eq baseField polynomialRing (A := coordinateRing)).symm
  rw [ringKrullDim_eq_of_integral_injective polynomialRing coordinateRing, coordinateTrdeg]
  simp [polynomialRing]

end MiyaokaMori.RingTheory
