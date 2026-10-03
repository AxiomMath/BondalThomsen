module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Sites.Whiskering

@[expose] public section
open CategoryTheory
universe u v
namespace CommRingCat
abbrev additiveUnits : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ commGroupAddCommGroupEquivalence.functor

end CommRingCat
namespace CategoryTheory.Sheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
noncomputable abbrev additiveUnitsFunctor :
    Sheaf J CommRingCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafCompose J CommRingCat.additiveUnits

end CategoryTheory.Sheaf
end
