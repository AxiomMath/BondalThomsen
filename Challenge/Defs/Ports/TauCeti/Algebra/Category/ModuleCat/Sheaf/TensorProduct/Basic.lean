module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs

@[expose] public section
open CategoryTheory Category Limits MonoidalCategory Opposite
namespace TauCeti
universe u v₁ u₁
noncomputable section
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})
namespace SheafOfModules
instance instMonoidalPresheafOfModulesRingCatSheaf :
    MonoidalCategory (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))

instance instSymmetricPresheafOfModulesRingCatSheaf :
    SymmetricCategory (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  inferInstanceAs (SymmetricCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))

def tensorProductRightFunctor (N : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ SheafOfModules.{u} (ringCatSheaf R) :=
  (SheafOfModules.forget (ringCatSheaf R)).comp
    ((MonoidalCategory.tensorRight (C := PresheafOfModules.{u} (ringCatSheaf R).obj)
      N.val).comp (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)))

def tensorProductLeftFunctor (M : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ SheafOfModules.{u} (ringCatSheaf R) :=
  (SheafOfModules.forget (ringCatSheaf R)).comp
    ((MonoidalCategory.tensorLeft (C := PresheafOfModules.{u} (ringCatSheaf R).obj)
      M.val).comp (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)))

def tensorProduct (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) :=
  (tensorProductRightFunctor R N).obj M

def tensorProductIso (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M N ≅
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj (M.val ⊗ N.val) :=
  Iso.refl _

def tensorProductCongrLeft {M M' N : SheafOfModules.{u} (ringCatSheaf R)} (e : M ≅ M') :
    tensorProduct R M N ≅ tensorProduct R M' N :=
  (tensorProductRightFunctor R N).mapIso e

def tensorProductCongrRight {M N N' : SheafOfModules.{u} (ringCatSheaf R)} (e : N ≅ N') :
    tensorProduct R M N ≅ tensorProduct R M N' :=
  (tensorProductLeftFunctor R M).mapIso e

def tensorProductUnitIsoLeft (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R (_root_.SheafOfModules.unit (ringCatSheaf R)) M ≅ M :=
  (tensorProductIso R _ M).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (λ_ M.val) ≪≫
      sheafificationIso (ringCatSheaf R) M

def tensorProductUnitIsoRight (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M (_root_.SheafOfModules.unit (ringCatSheaf R)) ≅ M :=
  (tensorProductIso R M _).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (ρ_ M.val) ≪≫
      sheafificationIso (ringCatSheaf R) M

def tensorProductComm (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M N ≅ tensorProduct R N M :=
  (tensorProductIso R M N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (β_ M.val N.val) ≪≫
      tensorProductIso R N M

end SheafOfModules
end
end TauCeti
end
