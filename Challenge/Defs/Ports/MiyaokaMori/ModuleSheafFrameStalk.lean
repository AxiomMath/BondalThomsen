module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}
namespace IsFrame
variable {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
end IsFrame
instance moduleStalkModule (X : Scheme.{u}) (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  change Module (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (C := Ab)
      (show _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) from M.val).presheaf x)
  infer_instance

def moduleStalkMap (X : Scheme.{u}) (x : X) {M N : X.Modules} (f : M ⟶ N) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  toFun := (TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, b, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf) M.val,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change N.presheaf.germ V x hxV (f.app V (_ • b)) = _
    erw [Scheme.Modules.Hom.app_smul, PresheafOfModules.germ_smul (R := X.presheaf) N.val,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl

def moduleStalkFunctor (X : Scheme.{u}) (x : X) : X.Modules ⥤ ModuleCat (X.presheaf.stalk x) where
  obj M := ModuleCat.of _ (M.presheaf.stalk x)
  map f := ModuleCat.ofHom (moduleStalkMap X x f)
  map_id M := by
    ext m
    exact CategoryTheory.congr_fun (C := AddCommGrpCat.{u})
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_id M) m
  map_comp f g := by
    ext m
    exact CategoryTheory.congr_fun (C := AddCommGrpCat.{u})
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp f g) m

abbrev stalk (M : X.Modules) (x : X) : ModuleCat.{u} (X.presheaf.stalk x) :=
  (moduleStalkFunctor X x).obj M

end AlgebraicGeometry.Scheme.Modules
end
end
