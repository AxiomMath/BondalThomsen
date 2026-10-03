module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import BondalThomsen.Ports.TauCeti.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X X' Y Y' : C}

section DimensionShift

instance injective_cokernelSequence_X₂ {X Y : C} (f : X ⟶ Y) [Injective Y] :
    Injective (ShortComplex.cokernelSequence f).X₂ :=
  (inferInstance : Injective Y)

lemma subsingleton_ext_succ_of_comp_extClass_eq_zero {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂] (X : C) (n : ℕ)
    (hzero : ∀ x₃ : Ext X S.X₃ n, x₃.comp hS.extClass rfl = 0) :
    Subsingleton (Ext X S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS y
    (Ext.eq_zero_of_injective _) rfl
  exact hzero x₃

variable [EnoughInjectives C]

noncomputable abbrev injectiveCokernelSequence (Y : C) : ShortComplex C :=
  ShortComplex.cokernelSequence (Injective.ι Y)

omit [HasExt C] in

lemma injectiveCokernelSequence_shortExact (Y : C) :
    (injectiveCokernelSequence Y).ShortExact :=
  cokernelSequence_shortExact _

lemma subsingleton_ext_succ_of_injectiveCokernelSequence (X Y : C) (n : ℕ)
    (hzero : ∀ x₃ : Ext X (injectiveCokernelSequence Y).X₃ n,
      x₃.comp (injectiveCokernelSequence_shortExact Y).extClass rfl = 0) :
    Subsingleton (Ext X Y (n + 1)) :=
  subsingleton_ext_succ_of_comp_extClass_eq_zero
    (injectiveCokernelSequence_shortExact Y) X n hzero

end DimensionShift

variable {S : ShortComplex C}

@[simp]
theorem coe_postcompOfLinear (R : Type t) [CommRing R] [Linear R C] {Y Z : C} {n a b : ℕ}
    (beta : Ext.{w} Y Z n) (X : C) (h : a + n = b) :
    ⇑(Ext.postcompOfLinear beta R X h) = Ext.postcomp beta X h :=
  rfl

@[simp]
theorem coe_precompOfLinear (R : Type t) [CommRing R] [Linear R C] {X Y : C} {n a b : ℕ}
    (alpha : Ext.{w} X Y n) (Z : C) (h : n + a = b) :
    ⇑(Ext.precompOfLinear alpha R Z h) = Ext.precomp alpha Z h :=
  rfl

end TauCeti
