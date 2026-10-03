module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LocalizedModuleLength
public import BondalThomsen.Ports.MiyaokaMori.Nef.SpecResidueDegree
public import Mathlib.NumberTheory.RamificationInertia.Inertia

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

namespace Module

variable {baseRing extensionRing : Type u} [CommRing baseRing] [IsLocalRing baseRing] [CommRing extensionRing] [Algebra baseRing extensionRing]
  [Finite (MaximalSpectrum extensionRing)]

def inertiaLengthSum (baseRing : Type u) (extensionRing : Type u) [CommRing baseRing] [IsLocalRing baseRing] [CommRing extensionRing]
    [Algebra baseRing extensionRing] (middleModule : Type u) [AddCommGroup middleModule] [Module extensionRing middleModule] : ℕ∞ :=
  ∑ᶠ maximalPoint : MaximalSpectrum extensionRing,
    ((maximalPoint.asIdeal.inertiaDeg baseRing : ℕ) : ℕ∞) *
      Module.length (Localization.AtPrime maximalPoint.asIdeal) (LocalizedModule maximalPoint.asIdeal.primeCompl middleModule)

theorem inertiaLengthSum_eq_add_of_exact {leftModule middleModule rightModule : Type u} [AddCommGroup leftModule] [Module extensionRing leftModule]
    [AddCommGroup middleModule] [Module extensionRing middleModule] [AddCommGroup rightModule] [Module extensionRing rightModule] (firstMap : leftModule →ₗ[extensionRing] middleModule) (secondMap : middleModule →ₗ[extensionRing] rightModule)
    (hf : Function.Injective firstMap) (hg : Function.Surjective secondMap) (hex : Function.Exact firstMap secondMap) :
    inertiaLengthSum baseRing extensionRing middleModule = inertiaLengthSum baseRing extensionRing leftModule + inertiaLengthSum baseRing extensionRing rightModule := by
  unfold inertiaLengthSum
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  refine finsum_congr fun maximalPoint => ?_
  rw [length_localizedModule_eq_add_of_exact maximalPoint.asIdeal.primeCompl firstMap secondMap hf hg hex, mul_add]

theorem inertiaLengthSum_congr {middleModule rightModule : Type u} [AddCommGroup middleModule] [Module extensionRing middleModule] [AddCommGroup rightModule]
    [Module extensionRing rightModule] (equivalence : middleModule ≃ₗ[extensionRing] rightModule) : inertiaLengthSum baseRing extensionRing middleModule = inertiaLengthSum baseRing extensionRing rightModule := by
  unfold inertiaLengthSum
  refine finsum_congr fun maximalPoint => ?_
  rw [length_localizedModule_congr maximalPoint.asIdeal.primeCompl equivalence]

theorem inertiaLengthSum_quotient (ideal : Ideal extensionRing) [hI : ideal.IsMaximal] :
    inertiaLengthSum baseRing extensionRing (extensionRing ⧸ ideal) =
      ((ideal.inertiaDeg baseRing : ℕ) : ℕ∞) := by
  unfold inertiaLengthSum
  rw [finsum_eq_single _ (⟨ideal, hI⟩ : MaximalSpectrum extensionRing)]
  · have := length_localizedModule_quotient_self ideal
    rw [this, mul_one]
  · intro maximalPoint hm
    have hne : ideal ≠ maximalPoint.asIdeal := fun equality => hm (by ext1; exact equality.symm)
    have : maximalPoint.asIdeal.IsMaximal := maximalPoint.isMaximal
    rw [length_localizedModule_quotient_of_ne ideal maximalPoint.asIdeal hne, mul_zero]

theorem length_quotient_eq_inertiaDeg (ideal : Ideal extensionRing) [hI : ideal.IsMaximal]
    [hlo : ideal.LiesOver (IsLocalRing.maximalIdeal baseRing)]
    (hfin : ideal.inertiaDeg baseRing ≠ 0) :
    Module.length baseRing (extensionRing ⧸ ideal) =
      ((ideal.inertiaDeg baseRing : ℕ) : ℕ∞) := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal baseRing)] at hfin ⊢
  let _ : Field (baseRing ⧸ IsLocalRing.maximalIdeal baseRing) := Ideal.Quotient.field _
  have hfd : Module.Finite (baseRing ⧸ IsLocalRing.maximalIdeal baseRing) (extensionRing ⧸ ideal) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hfin)
  rw [Module.length_eq_of_surjective (S := baseRing) (R := baseRing ⧸ IsLocalRing.maximalIdeal baseRing)
    (M := extensionRing ⧸ ideal) Ideal.Quotient.mk_surjective, Module.length_eq_finrank]

theorem length_eq_inertiaLengthSum {middleModule : Type u} [AddCommGroup middleModule] [Module extensionRing middleModule]
    (hB : ∀ maximalPoint : MaximalSpectrum extensionRing, maximalPoint.asIdeal.LiesOver (IsLocalRing.maximalIdeal baseRing))
    (hfin : ∀ maximalPoint : MaximalSpectrum extensionRing, maximalPoint.asIdeal.inertiaDeg baseRing ≠ 0)
    (hM : IsFiniteLength extensionRing middleModule) :
    ∀ [Module baseRing middleModule] [IsScalarTower baseRing extensionRing middleModule], Module.length baseRing middleModule = inertiaLengthSum baseRing extensionRing middleModule := by
  induction hM with
  | @of_subsingleton middleModule _ _ _ =>
    intro _ _
    rw [Module.length_eq_zero]
    unfold inertiaLengthSum
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun maximalPoint => ?_
    have h0 : Module.length extensionRing middleModule = 0 := Module.length_eq_zero
    have : Module.length (Localization.AtPrime maximalPoint.asIdeal)
        (LocalizedModule maximalPoint.asIdeal.primeCompl middleModule) = 0 :=
      le_antisymm ((length_localizedModule_le _).trans h0.le) (by simp)
    rw [this, mul_zero]
  | @of_simple_quotient middleModule _ _ leftModule hs _ ih =>
    intro _ _
    have hex : Function.Exact leftModule.subtype leftModule.mkQ := LinearMap.exact_subtype_mkQ leftModule
    rw [Module.length_eq_add_of_exact (leftModule.subtype.restrictScalars baseRing) (leftModule.mkQ.restrictScalars baseRing)
      (Submodule.subtype_injective leftModule) (Submodule.mkQ_surjective leftModule) hex,
      inertiaLengthSum_eq_add_of_exact leftModule.subtype leftModule.mkQ (Submodule.subtype_injective leftModule)
        (Submodule.mkQ_surjective leftModule) hex, ih]
    congr 1
    obtain ⟨ideal, hI, ⟨equivalence⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have := hB ⟨ideal, hI⟩
    rw [(equivalence.restrictScalars baseRing).length_eq, inertiaLengthSum_congr equivalence, inertiaLengthSum_quotient,
      length_quotient_eq_inertiaDeg ideal (hfin ⟨ideal, hI⟩)]

end Module

end
