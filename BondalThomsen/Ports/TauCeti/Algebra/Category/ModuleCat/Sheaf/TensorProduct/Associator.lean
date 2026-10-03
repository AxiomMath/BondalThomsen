module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
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

instance (M₀ P₀ : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app M₀ ▷
        P₀)) := by
  rw [← MorphismProperty.isomorphisms.iff, ← MorphismProperty.inverseImage_iff (.isomorphisms _),
    ← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact PresheafOfModules.inverseImage_W_toPresheaf_whiskerRight J
    (f := (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringCatSheaf R).obj)).unit.app M₀) (J.W_toSheafify M₀.presheaf) P₀

instance (M₀ P₀ : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      (M₀ ◁ (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        P₀)) := by
  rw [← MorphismProperty.isomorphisms.iff, ← MorphismProperty.inverseImage_iff (.isomorphisms _),
    ← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft J M₀
    (f := (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringCatSheaf R).obj)).unit.app P₀) (J.W_toSheafify P₀.presheaf)

def tensorProductAssoc (M N P : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R (tensorProduct R M N) P ≅ tensorProduct R M (tensorProduct R N P) :=
  tensorProductIso R (tensorProduct R M N) P ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
      (whiskerRightIso ((_root_.SheafOfModules.forget _).mapIso (tensorProductIso R M N))
        P.val) ≪≫
    (asIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        (M.val ⊗ N.val) ▷ P.val))).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (α_ M.val N.val P.val) ≪≫
    asIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      (M.val ◁ (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        (N.val ⊗ P.val))) ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
      (whiskerLeftIso M.val
        ((_root_.SheafOfModules.forget _).mapIso (tensorProductIso R N P))).symm ≪≫
    (tensorProductIso R M (tensorProduct R N P)).symm

end SheafOfModules

end

end TauCeti
