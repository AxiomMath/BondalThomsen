module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal

@[expose] public section

open CategoryTheory Category MonoidalCategory Opposite

namespace TauCeti

universe u v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
variable (R : Sheaf K CommRingCat.{u})

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in

abbrev pushforwardCommRing : Sheaf J CommRingCat.{u} :=
  (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in

abbrev pushforwardModule :
    SheafOfModules.{u} (ringCatSheaf R) ⥤
      SheafOfModules.{u} (ringCatSheaf (pushforwardCommRing (J := J) (K := K) F R)) :=
  SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)

def pushforwardTensorProductIso
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardModule (J := J) (K := K) F R).obj (tensorProduct R M N) ≅
      tensorProduct (pushforwardCommRing (J := J) (K := K) F R)
        ((pushforwardModule (J := J) (K := K) F R).obj M)
        ((pushforwardModule (J := J) (K := K) F R).obj N) :=
  (pushforwardModule (J := J) (K := K) F R).mapIso (tensorProductIso R M N) ≪≫
    pushforwardSheafificationIso F (ringCatSheaf R) (M.val ⊗ N.val) ≪≫
    (PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (pushforwardCommRing (J := J) (K := K) F R)).obj)).mapIso
        (Functor.Monoidal.μIso
          (PresheafOfModules.pushforward₀OfCommRingCat F R.obj) M.val N.val).symm ≪≫
    (tensorProductIso (pushforwardCommRing (J := J) (K := K) F R)
      ((pushforwardModule (J := J) (K := K) F R).obj M)
      ((pushforwardModule (J := J) (K := K) F R).obj N)).symm

def overTensorProductIso (M N : SheafOfModules.{u} (ringCatSheaf R)) (X : D)
    [(K.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
    [(K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (tensorProduct R M N).over X ≅ tensorProduct (R.over X) (M.over X) (N.over X) :=
  pushforwardTensorProductIso (J := K.over X) (K := K) (Over.forget X) R M N

end SheafOfModules

end

end TauCeti
