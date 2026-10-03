module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.Ring.Limits
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

@[expose] public section
open CategoryTheory Limits
namespace TauCeti
universe u v₁ u₁
noncomputable section
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
variable [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
namespace SheafOfModules
variable (R : Sheaf J CommRingCat.{u})
def tensorProductFreePUnitIsoLeft
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit) M ≅ M :=
  tensorProductCongrLeft R (freePUnitIsoUnit (ringCatSheaf R)) ≪≫
    tensorProductUnitIsoLeft R M

def tensorProductFreePUnitIsoRight
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit) ≅ M :=
  tensorProductCongrRight R (freePUnitIsoUnit (ringCatSheaf R)) ≪≫
    tensorProductUnitIsoRight R M

namespace IsInvertible
variable {M N : SheafOfModules.{u} (ringCatSheaf R)}
end IsInvertible
end SheafOfModules
end
end TauCeti
end
