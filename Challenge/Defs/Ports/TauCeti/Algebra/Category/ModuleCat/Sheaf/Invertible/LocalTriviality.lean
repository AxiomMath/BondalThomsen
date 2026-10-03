module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic

@[expose] public section
open CategoryTheory
namespace TauCeti
universe u v₁ u₁
noncomputable section
namespace SheafOfModules
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}
structure LocalTrivializations (M : SheafOfModules.{u} R) where

  I : Type u₁

  X : I → C

  coversTop : J.CoversTop X

  iso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ M.over (X i)

namespace LocalTrivializations
end LocalTrivializations
end SheafOfModules
end
end TauCeti
end
