module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite
namespace TauCeti
namespace AlgebraicGeometry
universe u
noncomputable section
namespace Scheme.Modules
variable {X : Scheme.{u}} {M N : X.Modules}
def restrictGlobal (U : X.Opens) (r : Γ(X, ⊤)) :
    X.ringCatSheaf.obj.obj (.op U) :=
  X.presheaf.map (homOfLE le_top).op r

def _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul
    (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M where
  val.app U := by
    letI : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    exact ModuleCat.ofHom <|
      LinearMap.lsmul (X.ringCatSheaf.obj.obj U) (M.val.obj U) (restrictGlobal U.unop r)
  val.naturality {U V} f := by
    let : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    let : CommRing (X.ringCatSheaf.obj.obj V) :=
      inferInstanceAs (CommRing (X.presheaf.obj V))
    ext x
    dsimp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.lsmul_apply]
    rw [M.val.map_smul]
    change restrictGlobal V.unop r • M.val.map f x =
      X.ringCatSheaf.obj.map f (restrictGlobal U.unop r) • M.val.map f x
    congr 1
    change X.presheaf.map (homOfLE le_top).op r =
      X.presheaf.map f (X.presheaf.map (homOfLE le_top).op r)
    rw [← Functor.map_comp_apply]
    congr

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_add
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r + s) = globalSectionsSmul M r + globalSectionsSmul M s :=
  sorry

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_one
    (M : X.Modules) : globalSectionsSmul M 1 = 𝟙 M :=
  sorry

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_mul
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r * s) = globalSectionsSmul M s ≫ globalSectionsSmul M r :=
  sorry

@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_naturality
    (f : M ⟶ N) (r : Γ(X, ⊤)) :
    globalSectionsSmul M r ≫ f = f ≫ globalSectionsSmul N r :=
  sorry

section Base
variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
end Base
end Scheme.Modules
end
end AlgebraicGeometry
end TauCeti
end
