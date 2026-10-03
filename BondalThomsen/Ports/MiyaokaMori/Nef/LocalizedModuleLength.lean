module

public import Mathlib.Tactic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

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

variable {baseRing : Type*} [CommRing baseRing] (multiplicativeSet : Submonoid baseRing)
variable {middleModule : Type*} [AddCommGroup middleModule] [Module baseRing middleModule]
variable {leftModule : Type*} [AddCommGroup leftModule] [Module baseRing leftModule]
variable {rightModule : Type*} [AddCommGroup rightModule] [Module baseRing rightModule]

theorem length_localizedModule_le :
    Module.length (Localization multiplicativeSet) (LocalizedModule multiplicativeSet middleModule) ≤ Module.length baseRing middleModule := by
  have gi := Submodule.localized'gi (Localization multiplicativeSet) multiplicativeSet (LocalizedModule.mkLinearMap multiplicativeSet middleModule)
  have equality := Order.krullDim_le_of_strictMono _ gi.strictMono_u
  rw [← Module.coe_length, ← Module.coe_length] at equality
  exact WithBot.coe_le_coe.mp equality

def locMap (firstMap : leftModule →ₗ[baseRing] middleModule) : LocalizedModule multiplicativeSet leftModule →ₗ[Localization multiplicativeSet] LocalizedModule multiplicativeSet middleModule :=
  (IsLocalizedModule.map multiplicativeSet (LocalizedModule.mkLinearMap multiplicativeSet leftModule) (LocalizedModule.mkLinearMap multiplicativeSet middleModule)
    firstMap).extendScalarsOfIsLocalization multiplicativeSet (Localization multiplicativeSet)

theorem length_localizedModule_eq_add_of_exact (firstMap : leftModule →ₗ[baseRing] middleModule) (secondMap : middleModule →ₗ[baseRing] rightModule)
    (hf : Function.Injective firstMap) (hg : Function.Surjective secondMap) (hex : Function.Exact firstMap secondMap) :
    Module.length (Localization multiplicativeSet) (LocalizedModule multiplicativeSet middleModule) =
      Module.length (Localization multiplicativeSet) (LocalizedModule multiplicativeSet leftModule) +
        Module.length (Localization multiplicativeSet) (LocalizedModule multiplicativeSet rightModule) :=
  Module.length_eq_add_of_exact (locMap multiplicativeSet firstMap) (locMap multiplicativeSet secondMap)
    (IsLocalizedModule.map_injective multiplicativeSet _ _ firstMap hf) (IsLocalizedModule.map_surjective multiplicativeSet _ _ secondMap hg)
    (LocalizedModule.map_exact multiplicativeSet firstMap secondMap hex)

theorem length_localizedModule_congr (equivalence : middleModule ≃ₗ[baseRing] rightModule) :
    Module.length (Localization multiplicativeSet) (LocalizedModule multiplicativeSet middleModule) =
      Module.length (Localization multiplicativeSet) (LocalizedModule multiplicativeSet rightModule) := by
  have equality := length_localizedModule_eq_add_of_exact multiplicativeSet (⊥ : Submodule baseRing middleModule).subtype
    (equivalence : middleModule →ₗ[baseRing] rightModule) (Submodule.subtype_injective _) equivalence.surjective (by
      intro element
      constructor
      · intro hx
        have : element = 0 := equivalence.injective (by simpa using hx)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨⟨rational, hy⟩, rfl⟩
        rw [Submodule.mem_bot] at hy
        simp [hy])
  have h0 : Module.length (Localization multiplicativeSet) (LocalizedModule multiplicativeSet (⊥ : Submodule baseRing middleModule)) = 0 := by
    refine le_antisymm ((length_localizedModule_le multiplicativeSet).trans ?_) zero_le
    rw [Module.length_bot]
  rw [equality, h0, zero_add]

theorem length_localizedModule_quotient_span_singleton (rational : baseRing) :
    Module.length (Localization multiplicativeSet) (LocalizedModule multiplicativeSet (baseRing ⧸ Ideal.span {rational})) =
      Ring.ord (Localization multiplicativeSet) (algebraMap baseRing (Localization multiplicativeSet) rational) := by
  let localizedRing := Localization multiplicativeSet
  let firstMap : baseRing →ₗ[baseRing] localizedRing := Algebra.linearMap baseRing localizedRing
  let ideal : Submodule baseRing baseRing := Ideal.span {rational}
  let e₀ : (localizedRing ⧸ ideal.localized' localizedRing multiplicativeSet firstMap) ≃ₗ[baseRing] LocalizedModule multiplicativeSet (baseRing ⧸ ideal) :=
    IsLocalizedModule.linearEquiv multiplicativeSet (ideal.toLocalizedQuotient' localizedRing multiplicativeSet firstMap)
      (LocalizedModule.mkLinearMap multiplicativeSet (baseRing ⧸ ideal))
  let equivalence : (localizedRing ⧸ ideal.localized' localizedRing multiplicativeSet firstMap) ≃ₗ[localizedRing] LocalizedModule multiplicativeSet (baseRing ⧸ ideal) :=
    e₀.extendScalarsOfIsLocalization multiplicativeSet localizedRing
  have hI : ideal.localized' localizedRing multiplicativeSet firstMap = (Ideal.span {algebraMap baseRing localizedRing rational} : Ideal localizedRing) := by
    show (Submodule.span baseRing {rational}).localized' localizedRing multiplicativeSet firstMap = _
    rw [Submodule.localized'_span, Set.image_singleton]
    rfl
  unfold Ring.ord
  rw [← equivalence.length_eq, hI]

section Maximal

variable (ideal otherIdeal : Ideal baseRing) [ideal.IsMaximal] [otherIdeal.IsMaximal]

theorem length_localizedModule_quotient_of_ne (equality : ideal ≠ otherIdeal) :
    Module.length (Localization otherIdeal.primeCompl) (LocalizedModule otherIdeal.primeCompl (baseRing ⧸ ideal)) = 0 := by
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  have hIJ : ¬ ideal ≤ otherIdeal := fun hle => equality (Ideal.IsMaximal.eq_of_le ‹ideal.IsMaximal› Ideal.IsPrime.ne_top' hle)
  obtain ⟨denominator, hsI, hsJ⟩ := Set.not_subset.mp hIJ
  intro element
  refine ⟨denominator, hsJ, ?_⟩
  induction element using Submodule.Quotient.induction_on with
  | H element =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ideal.mul_mem_right element hsI

theorem length_localizedModule_quotient_self :
    Module.length (Localization ideal.primeCompl) (LocalizedModule ideal.primeCompl (baseRing ⧸ ideal)) = 1 := by
  have : IsSimpleModule baseRing (baseRing ⧸ ideal) := by
    rw [isSimpleModule_iff_quot_maximal]
    exact ⟨ideal, ‹_›, ⟨LinearEquiv.refl _ _⟩⟩
  refine le_antisymm ((length_localizedModule_le _).trans (Module.length_eq_one baseRing (baseRing ⧸ ideal)).le) ?_
  rw [Order.one_le_iff_ne_zero, Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  intro hx
  obtain ⟨denominator, hs, hs1⟩ := hx (Submodule.Quotient.mk 1)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one] at hs1
  exact hs hs1

end Maximal

end Module

end
