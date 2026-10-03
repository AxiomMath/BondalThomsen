module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

variable {C : Type u₁} [Category.{v₁} C]

namespace TauCeti

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M P : _root_.PresheafOfModules.{v} R}

noncomputable section

def liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) :
    P ⟶ N.toPresheafOfModules :=
  _root_.PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        (((φ.app U).hom.toAddMonoidHom).codRestrict (N.obj U) (hφ U))
      naturality := by
        intro U V f
        ext x
        apply Subtype.ext
        exact _root_.PresheafOfModules.naturality_apply φ f x }
    (by
      intro U r m
      apply Subtype.ext
      exact (φ.app U).hom.map_smul r m)

@[simp]
lemma liftToSubmodule_app_coe (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) (U : Cᵒᵖ) (s : P.obj U) :
    ((liftToSubmodule N φ hφ).app U s).val = φ.app U s :=
  (rfl)

@[reassoc (attr := simp)]
lemma liftToSubmodule_ι (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) :
    liftToSubmodule N φ hφ ≫ N.ι = φ := by
  ext U s
  exact liftToSubmodule_app_coe N φ hφ U s

lemma ι_app_mem (N : M.Submodule) (U : Cᵒᵖ) (s : N.toPresheafOfModules.obj U) :
    N.ι.app U s ∈ N.obj U :=
  s.2

end

end PresheafOfModules

namespace SheafOfModules

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M P : _root_.SheafOfModules.{v} R}

noncomputable section

def liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    P ⟶ N.toSheafOfModules :=
  ⟨PresheafOfModules.liftToSubmodule N.toSubmodule φ.val hφ⟩

@[simp]
lemma liftToSubmodule_val_app_coe (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U)
    (U : Cᵒᵖ) (s : P.val.obj U) :
    ((liftToSubmodule N φ hφ).val.app U s).val = φ.val.app U s :=
  (rfl)

@[reassoc (attr := simp)]
lemma liftToSubmodule_ι (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    liftToSubmodule N φ hφ ≫ N.ι = φ :=
  _root_.SheafOfModules.Hom.ext (PresheafOfModules.liftToSubmodule_ι N.toSubmodule φ.val hφ)

lemma ι_val_app_mem (N : M.Submodule) (U : Cᵒᵖ) (s : N.toSheafOfModules.val.obj U) :
    N.ι.val.app U s ∈ N.toSubmodule.obj U :=
  PresheafOfModules.ι_app_mem N.toSubmodule U s

lemma ι_val_app_injective (N : M.Submodule) (U : Cᵒᵖ) :
    Function.Injective (N.ι.val.app U) :=
  Subtype.val_injective

lemma isIso_liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U)
    (hinj : ∀ U : Cᵒᵖ, Function.Injective (φ.val.app U))
    (hsurj : ∀ (U : Cᵒᵖ) (s : M.val.obj U), s ∈ N.toSubmodule.obj U → ∃ t, φ.val.app U t = s) :
    IsIso (liftToSubmodule N φ hφ) := by
  rw [← isIso_iff_of_reflects_iso _ (_root_.SheafOfModules.forget _)]
  have (U : Cᵒᵖ) : IsIso ((liftToSubmodule N φ hφ).val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ hinj U ?_, fun s ↦ ?_⟩
    · simpa only [liftToSubmodule_val_app_coe] using congrArg Subtype.val hab
    · obtain ⟨t, ht⟩ := hsurj U s.1 s.2
      exact ⟨t, Subtype.ext (by simpa only [liftToSubmodule_val_app_coe] using ht)⟩
  exact (_root_.PresheafOfModules.isoMk (fun U ↦ asIso ((liftToSubmodule N φ hφ).val.app U))
    fun _ _ f ↦ (liftToSubmodule N φ hφ).val.naturality f).isIso_hom

namespace Submodule

def homOfLE {N₁ N₂ : M.Submodule} (h : N₁.toSubmodule ≤ N₂.toSubmodule) :
    N₁.toSheafOfModules ⟶ N₂.toSheafOfModules :=
  ⟨_root_.PresheafOfModules.Submodule.homOfLE h⟩

end Submodule

end

end SheafOfModules

end TauCeti

namespace SheafOfModules.Submodule

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}

noncomputable section

def overIsoOfEq (N₁ N₂ : M.Submodule) (V : C)
    (h : ∀ (W : C) (_ : W ⟶ V), N₁.toSubmodule.obj (op W) = N₂.toSubmodule.obj (op W)) :
    N₁.toSheafOfModules.over V ≅ N₂.toSheafOfModules.over V :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun W ↦
        letI := ((N₁.toSheafOfModules.over V).val.obj W).isModule
        letI := ((N₂.toSheafOfModules.over V).val.obj W).isModule
        LinearEquiv.toModuleIso
          (LinearEquiv.ofEq _ _ (h _ W.unop.hom)))
      (fun _ _ _ ↦ rfl)

instance instMonoιOver (N : M.Submodule) (V : C) : Mono (N.ι.over V) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  change Mono (N.ι.over V).val
  apply PresheafOfModules.mono_of_injective
  intro W
  exact Subtype.val_injective

@[reassoc (attr := simp)]
lemma overIsoOfEq_hom_ι (N₁ N₂ : M.Submodule) (V : C)
    (h : ∀ (W : C) (_ : W ⟶ V), N₁.toSubmodule.obj (op W) = N₂.toSubmodule.obj (op W)) :
    (overIsoOfEq N₁ N₂ V h).hom ≫ N₂.ι.over V = N₁.ι.over V := by
  ext W s
  rfl

end

end SheafOfModules.Submodule
