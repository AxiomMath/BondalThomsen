module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

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

theorem tensorProduct_of_iso_unit_left [IsInvertible N]
    (e : M ≅ _root_.SheafOfModules.unit (ringCatSheaf R)) :
    IsInvertible (tensorProduct R M N) :=
  IsInvertible.of_iso
    ((tensorProductCongrLeft R e ≪≫ tensorProductUnitIsoLeft R N).symm)

theorem tensorProduct_of_iso_unit_right [IsInvertible M]
    (e : N ≅ _root_.SheafOfModules.unit (ringCatSheaf R)) :
    IsInvertible (tensorProduct R M N) :=
  IsInvertible.of_iso
    ((tensorProductCongrRight R e ≪≫ tensorProductUnitIsoRight R M).symm)

instance tensorProduct_freePUnit_left [IsInvertible N] :
    IsInvertible
      (tensorProduct R (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit) N) :=
  tensorProduct_of_iso_unit_left R (freePUnitIsoUnit (ringCatSheaf R))

instance tensorProduct_freePUnit_right [IsInvertible M] :
    IsInvertible
      (tensorProduct R M (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit)) :=
  tensorProduct_of_iso_unit_right R (freePUnitIsoUnit (ringCatSheaf R))

end IsInvertible

end SheafOfModules

end

end TauCeti
