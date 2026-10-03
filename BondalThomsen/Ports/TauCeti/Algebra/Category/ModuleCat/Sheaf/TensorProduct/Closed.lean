module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Monoidal.Closed.Preadditive

@[expose] public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed PresheafOfModules

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})

instance presheafMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  inferInstanceAs (MonoidalClosed (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))

instance monoidalClosed : MonoidalClosed (SheafOfModules.{u} (ringCatSheaf R)) :=
  Monoidal.Reflective.monoidalClosed
    (PresheafOfModules.sheafificationAdjunction (R := ringCatSheaf R)
      (R₀ := (ringCatSheaf R).obj) (J := J) (𝟙 (ringCatSheaf R).obj))

instance monoidalPreadditive : MonoidalPreadditive (SheafOfModules.{u} (ringCatSheaf R)) :=
  monoidalPreadditive_of_monoidalClosed _

variable {R}

@[simp]
theorem _root_.SheafOfModules.ihom_obj
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (ihom M).obj N =
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        ((ihom M.val).obj N.val) := rfl

@[simp]
theorem _root_.SheafOfModules.ihom_map
    (M : SheafOfModules.{u} (ringCatSheaf R)) {N P : SheafOfModules.{u} (ringCatSheaf R)}
    (f : N ⟶ P) :
    (ihom M).map f =
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        ((ihom M.val).map f.val) := rfl

end SheafOfModules

end

end TauCeti
