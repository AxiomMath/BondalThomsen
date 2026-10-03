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

@[simp]
theorem sheafificationIso_hom (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{v} R) :
    (sheafificationIso R M).hom =
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M := by
  simp only [sheafificationIso]
  rfl

@[reassoc]
theorem sheafificationIso_inv_naturality {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{v} R}
    (f : M ⟶ N) :
    f ≫ (sheafificationIso R N).inv =
      (sheafificationIso R M).inv ≫ (PresheafOfModules.sheafification (𝟙 R.obj)).map f.val := by
  rw [Iso.comp_inv_eq, assoc, Iso.eq_inv_comp, sheafificationIso_hom, sheafificationIso_hom]
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.naturality f).symm

@[reassoc]
theorem sheafificationIso_hom_naturality {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{v} R}
    (f : M ⟶ N) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).map f.val ≫ (sheafificationIso R N).hom =
      (sheafificationIso R M).hom ≫ f := by
  rw [← cancel_epi (sheafificationIso R M).inv, Iso.inv_hom_id_assoc,
    ← Category.assoc, ← sheafificationIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end SheafOfModules

end

end TauCeti
