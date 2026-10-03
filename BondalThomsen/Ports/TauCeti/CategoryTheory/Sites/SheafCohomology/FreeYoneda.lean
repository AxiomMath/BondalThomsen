module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

noncomputable section

variable [HasSheafify J AddCommGrpCat.{v}]

noncomputable def freeYonedaSheafFunctor :
    C ⥤ _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat.{v}

lemma sheafH'_eq [HasExt.{v} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})]
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) :
    _root_.CategoryTheory.Sheaf.H'.{v} F n U =
      AddCommGrpCat.of (Abelian.Ext.{v} ((freeYonedaSheafFunctor J).obj U) F n) :=
  (rfl)

def freeYonedaSheafSectionsEquiv (U : C)
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}) :
    ((freeYonedaSheafFunctor J).obj U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv _ _).trans
    { ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{v}).homEquiv _ _).trans yonedaEquiv with
    map_add' := by
      intro f g
      rfl }

def freeYonedaSheafSectionsFormula (U : C)
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})
    (f : (freeYonedaSheafFunctor J).obj U ⟶ F) : F.obj.obj (op U) :=
  yonedaEquiv
    ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{v}).homEquiv _ _
      ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _ f))

lemma freeYonedaSheafSectionsEquiv_apply (U : C)
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})
    (f : (freeYonedaSheafFunctor J).obj U ⟶ F) :
    freeYonedaSheafSectionsEquiv J U F f = freeYonedaSheafSectionsFormula J U F f :=
  (rfl)

@[simp]
lemma freeYonedaSheafSectionsEquiv_naturality_right {U : C}
    {F G : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v}}
    (f : (freeYonedaSheafFunctor J).obj U ⟶ F) (g : F ⟶ G) :
    freeYonedaSheafSectionsEquiv J U G (f ≫ g) =
      g.hom.app (op U) (freeYonedaSheafSectionsEquiv J U F f) := by
  rw [freeYonedaSheafSectionsEquiv_apply, freeYonedaSheafSectionsEquiv_apply]
  dsimp only [freeYonedaSheafSectionsFormula, freeYonedaSheafFunctor, Functor.comp_obj] at f ⊢
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    yonedaEquiv_comp]
  rfl

lemma freeYonedaSheafSectionsEquiv_naturality_left {U V : C} (i : U ⟶ V)
    (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})
    (f : (freeYonedaSheafFunctor J).obj V ⟶ F) :
    freeYonedaSheafSectionsEquiv J U F ((freeYonedaSheafFunctor J).map i ≫ f) =
      F.obj.map i.op (freeYonedaSheafSectionsEquiv J V F f) := by
  rw [freeYonedaSheafSectionsEquiv_apply, freeYonedaSheafSectionsEquiv_apply]
  dsimp only [freeYonedaSheafSectionsFormula, freeYonedaSheafFunctor, Functor.comp_obj,
    Functor.comp_map] at f ⊢
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ _).symm

end

variable [HasSheafify J AddCommGrpCat.{v}]

instance mono_freeYonedaSheafFunctor_map {U V : C} (i : U ⟶ V) [Mono i] :
    Mono ((freeYonedaSheafFunctor J).map i) := by
  dsimp only [freeYonedaSheafFunctor, Functor.comp_map]
  infer_instance

end CategoryTheory

end TauCeti
