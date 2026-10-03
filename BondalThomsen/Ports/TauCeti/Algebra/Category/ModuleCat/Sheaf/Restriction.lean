module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

@[expose] public section

open CategoryTheory Category Opposite

namespace TauCeti

universe u v v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

section Additive

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

instance : (_root_.SheafOfModules.pushforward.{v} φ).Additive where
  map_add := rfl

instance (R : Sheaf J RingCat.{u}) (X : C) :
    (_root_.SheafOfModules.overFunctor.{v} R X).Additive :=
  inferInstanceAs (_root_.SheafOfModules.pushforward _).Additive

end Additive

section General

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{u})
variable [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in
abbrev pushedRing : Sheaf J RingCat.{u} :=
  (F.sheafPushforwardContinuous RingCat.{u} J K).obj R

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in

abbrev pushforwardRingIso : F.op ⋙ R.obj ≅
    ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj :=
  Iso.refl _

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in
abbrev presheafPushforward :
    PresheafOfModules.{v} R.obj ⥤
      PresheafOfModules.{v} (pushedRing (J := J) (K := K) F R).obj :=
  PresheafOfModules.pushforward (F := F)
    (pushforwardRingIso (J := J) (K := K) F R).inv

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in
abbrev sheafPushforward :
    SheafOfModules.{v} R ⥤
      SheafOfModules.{v} (pushedRing (J := J) (K := K) F R) :=
  SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [F.IsCocontinuous J K] in

def pushforwardToSheafify (P : PresheafOfModules.{v} R.obj) :
    (PresheafOfModules.pushforward (F := F)
        (pushforwardRingIso (J := J) (K := K) F R).inv).obj P ⟶
      ((SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P)).val :=
  (presheafPushforward F R).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [F.IsCocontinuous J K] in

@[reassoc]
theorem pushforwardToSheafify_naturality {P Q : PresheafOfModules.{v} R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.pushforward (F := F)
        (pushforwardRingIso (J := J) (K := K) F R).inv).map f ≫
        pushforwardToSheafify (J := J) (K := K) F R Q =
      pushforwardToSheafify (J := J) (K := K) F R P ≫
        ((SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).map
          ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map f)).val := by
  change (presheafPushforward F R).map f ≫
      (presheafPushforward F R).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app Q) =
    (presheafPushforward F R).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) ≫
      (presheafPushforward F R).map
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj) ⋙
          SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map f)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (presheafPushforward F R).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.naturality f)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [F.IsCocontinuous J K] in

theorem toPresheaf_map_pushforwardToSheafify_def
    (P : PresheafOfModules.{v} R.obj) :
    (PresheafOfModules.toPresheaf _).map
        (pushforwardToSheafify (J := J) (K := K) F R P) =
      Functor.whiskerLeft F.op
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction (R := R)
            (𝟙 R.obj)).unit.app P)) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [F.IsCocontinuous J K] in

theorem toPresheaf_map_pushforwardToSheafify
    (P : PresheafOfModules.{v} R.obj) :
    (PresheafOfModules.toPresheaf _).map
        (pushforwardToSheafify (J := J) (K := K) F R P) =
      Functor.whiskerLeft F.op (CategoryTheory.toSheafify K P.presheaf) := by
  rw [toPresheaf_map_pushforwardToSheafify_def,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{v}] in
theorem W_toPresheaf_map_pushforwardToSheafify
    (P : PresheafOfModules.{v} R.obj) :
    J.W ((PresheafOfModules.toPresheaf _).map
      (pushforwardToSheafify (J := J) (K := K) F R P)) := by
  rw [toPresheaf_map_pushforwardToSheafify]
  exact (J.W_iff_isLocallyBijective _).mpr
    ⟨Presheaf.isLocallyInjective_whisker J K F _,
      Presheaf.isLocallySurjective_whisker J K F _⟩

instance isIso_sheafification_map_pushforwardToSheafify
    (P : PresheafOfModules.{v} R.obj) :
    IsIso ((PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)).map
        (pushforwardToSheafify (J := J) (K := K) F R P)) := by
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)))
        (pushforwardToSheafify (J := J) (K := K) F R P)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact W_toPresheaf_map_pushforwardToSheafify (J := J) (K := K) F R P

def pushforwardSheafificationIso (P : PresheafOfModules.{v} R.obj) :
    (SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P) ≅
      (PresheafOfModules.sheafification
        (R := (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)).obj
          ((PresheafOfModules.pushforward (F := F)
            (pushforwardRingIso (J := J) (K := K) F R).inv).obj P) :=
  (sheafificationIso (pushedRing (J := J) (K := K) F R)
      ((sheafPushforward (J := J) (K := K) F R).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P))).symm ≪≫
    (asIso ((PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)).map
        (pushforwardToSheafify (J := J) (K := K) F R P))).symm

@[simp]
theorem pushforwardSheafificationIso_inv (P : PresheafOfModules.{v} R.obj) :
    (pushforwardSheafificationIso F R P).inv =
      (PresheafOfModules.sheafification
        (R := (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)).map
          (pushforwardToSheafify (J := J) (K := K) F R P) ≫
        (sheafificationIso ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
          ((SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
            ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P))).hom := by
  simp [pushforwardSheafificationIso]

@[reassoc]
theorem pushforwardSheafificationIso_inv_naturality
    {P Q : PresheafOfModules.{v} R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification
          (R := (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
          (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)).map
            ((PresheafOfModules.pushforward (F := F)
              (pushforwardRingIso (J := J) (K := K) F R).inv).map f) ≫
        (pushforwardSheafificationIso F R Q).inv =
      (pushforwardSheafificationIso F R P).inv ≫
        (SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).map
          ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map f) := by
  rw [pushforwardSheafificationIso_inv, pushforwardSheafificationIso_inv]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [pushforwardToSheafify_naturality]
  simp only [Functor.map_comp]
  rw [Category.assoc, sheafificationIso_hom_naturality]
  rw [Category.assoc]

end General

def overSheafificationIso (R : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{v} R.obj) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P).over X ≅
      (PresheafOfModules.sheafification (R := R.over X) (𝟙 (R.over X).obj)).obj
        ((PresheafOfModules.pushforward (F := Over.forget X)
          (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X) R).inv).obj P) :=
  pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X) R P

@[reassoc]
theorem overSheafificationIso_inv_naturality (R : Sheaf J RingCat.{u})
    {P Q : PresheafOfModules.{v} R.obj} (f : P ⟶ Q) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    (PresheafOfModules.sheafification (R := R.over X) (𝟙 (R.over X).obj)).map
          ((PresheafOfModules.pushforward (F := Over.forget X)
            (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X) R).inv).map f) ≫
        (overSheafificationIso R Q X).inv =
      (overSheafificationIso R P X).inv ≫
        (_root_.SheafOfModules.overFunctor R X).map
          ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map f) :=
  pushforwardSheafificationIso_inv_naturality
    (J := J.over X) (K := J) (Over.forget X) R f

def overSheafificationNatIso (R : Sheaf J RingCat.{u}) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    PresheafOfModules.sheafification (R := R) (𝟙 R.obj) ⋙
        _root_.SheafOfModules.overFunctor R X ≅
      PresheafOfModules.pushforward (F := Over.forget X)
          (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X) R).inv ⋙
        PresheafOfModules.sheafification (R := R.over X) (𝟙 (R.over X).obj) := by
  symm
  apply NatIso.ofComponents
  case app => exact fun P ↦ (overSheafificationIso R P X).symm
  case naturality => exact fun f ↦ overSheafificationIso_inv_naturality R f X

end SheafOfModules

end

end TauCeti
