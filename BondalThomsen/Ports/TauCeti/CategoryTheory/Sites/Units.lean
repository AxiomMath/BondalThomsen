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

@[simp]
lemma additiveUnitsFunctor_obj_obj (F : Sheaf J CommRingCat.{u}) (U : Cᵒᵖ) :
    ((additiveUnitsFunctor J).obj F).obj.obj U =
      AddCommGrpCat.of (Additive ((F.obj.obj U : CommRingCat.{u})ˣ)) :=
  rfl

@[simp]
lemma additiveUnitsFunctor_map_app_apply {F G : Sheaf J CommRingCat.{u}} (f : F ⟶ G)
    (U : Cᵒᵖ) (x : Additive ((F.obj.obj U : CommRingCat.{u})ˣ)) :
    (@AddCommGrpCat.Hom.hom
      (AddCommGrpCat.of (Additive ((F.obj.obj U : CommRingCat.{u})ˣ)))
      (AddCommGrpCat.of (Additive ((G.obj.obj U : CommRingCat.{u})ˣ)))
      (((additiveUnitsFunctor J).map f).hom.app U)) x =
      Additive.ofMul (Units.map (f.hom.app U).hom.toMonoidHom (Additive.toMul x)) :=
  rfl

@[simp]
lemma additiveUnitsFunctor_obj_map_apply (F : Sheaf J CommRingCat.{u}) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : Additive ((F.obj.obj U : CommRingCat.{u})ˣ)) :
    (@AddCommGrpCat.Hom.hom
      (AddCommGrpCat.of (Additive ((F.obj.obj U : CommRingCat.{u})ˣ)))
      (AddCommGrpCat.of (Additive ((F.obj.obj V : CommRingCat.{u})ˣ)))
      (((additiveUnitsFunctor J).obj F).obj.map i)) x =
      Additive.ofMul (Units.map (F.obj.map i).hom.toMonoidHom (Additive.toMul x)) :=
  rfl

end CategoryTheory.Sheaf
