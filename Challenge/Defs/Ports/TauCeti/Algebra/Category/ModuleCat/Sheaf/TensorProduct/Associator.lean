module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

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
        P₀)) :=
  sorry

instance (M₀ P₀ : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      (M₀ ◁ (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        P₀)) :=
  sorry

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
end
