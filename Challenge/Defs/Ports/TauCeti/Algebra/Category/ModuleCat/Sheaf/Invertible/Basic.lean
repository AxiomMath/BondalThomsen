module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section
open CategoryTheory
namespace TauCeti
universe u v₁ u₁
noncomputable section
namespace SheafOfModules
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}
structure _root_.SheafOfModules.LocalGeneratorsData.IsInvertible
    (q : SheafOfModules.LocalGeneratorsData M) : Prop where

  isLocallyFreeData : q.IsLocallyFreeData

  basisNonempty (i : q.I) : Nonempty (q.generators i).I

  basisSubsingleton (i : q.I) : Subsingleton (q.generators i).I

variable (M) in

class IsInvertible : Prop where

  exists_isInvertible :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u₁} M,
      SheafOfModules.LocalGeneratorsData.IsInvertible q

section
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
instance free_isInvertible [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
    [Limits.HasBinaryProducts C] (I : Type u) [Nonempty I] [Subsingleton I] :
    IsInvertible (SheafOfModules.free (R := R) I) :=
  sorry

end
end SheafOfModules
end
end TauCeti
end
