module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits

@[expose] public section
open CategoryTheory Category Limits
namespace TauCeti
universe u v v₁ u₁
noncomputable section
namespace SheafOfModules
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
abbrev ringCatSheaf (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

def sheafificationIso (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{v} R) :
    (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).app M

end SheafOfModules
end
end TauCeti
end
