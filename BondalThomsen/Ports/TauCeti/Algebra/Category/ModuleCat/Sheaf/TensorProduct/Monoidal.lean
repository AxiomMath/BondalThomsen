module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Presheaf.IsMonoidalW
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

@[expose] public section

open CategoryTheory Category MonoidalCategory

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})

instance isMonoidal_inverseImage_W_toPresheaf :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)).IsMonoidal :=
  PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf J (R := R.obj)

def sheafificationUnitIso :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj
      (𝟙_ (PresheafOfModules.{u} (ringCatSheaf R).obj)) ≅
        _root_.SheafOfModules.unit (ringCatSheaf R) :=
  sheafificationIso (ringCatSheaf R) (_root_.SheafOfModules.unit _)

instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringCatSheaf R)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)))

instance symmetricCategory : SymmetricCategory (SheafOfModules.{u} (ringCatSheaf R)) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)))

@[simp]
theorem tensorUnit_eq :
    𝟙_ (SheafOfModules.{u} (ringCatSheaf R)) = _root_.SheafOfModules.unit (ringCatSheaf R) :=
  rfl

instance sheafificationMonoidal :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)).Monoidal

instance sheafificationBraided :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)).Braided

@[simp]
theorem sheafification_ε :
    Functor.LaxMonoidal.ε (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)) =
      (sheafificationUnitIso R).inv :=
  rfl

@[simp]
theorem sheafification_η :
    Functor.OplaxMonoidal.η (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)) =
      (sheafificationUnitIso R).hom :=
  rfl

variable {R}

def _root_.SheafOfModules.tensorUnderlyingIso (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    M ⊗ N ≅ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj
      (M.val ⊗ N.val) :=
  ((sheafificationIso _ M).symm ⊗ᵢ (sheafificationIso _ N).symm) ≪≫
    Functor.Monoidal.μIso _ M.val N.val

end SheafOfModules

end

end TauCeti
