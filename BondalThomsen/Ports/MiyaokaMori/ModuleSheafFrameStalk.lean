module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk

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

abbrev res (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) : Γ(M, W') :=
  M.presheaf.map (homOfLE h).op x

theorem res_res (M : X.Modules) {W'' W' W : X.Opens} (h' : W'' ≤ W') (h : W' ≤ W)
    (x : Γ(M, W)) : M.res h' (M.res h x) = M.res (h'.trans h) x := by
  unfold res
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl

@[simp] theorem res_self (M : X.Modules) {W : X.Opens} (x : Γ(M, W)) :
    M.res le_rfl x = x := by
  unfold res
  have identity : (homOfLE (le_refl W)).op = 𝟙 (op W) := rfl
  rw [identity, M.presheaf.map_id]
  rfl

def IsFrame (M : X.Modules) (W : X.Opens) (e : Γ(M, W)) : Prop :=
  ∀ (W' : X.Opens) (h : W' ≤ W), Function.Bijective (fun r : Γ(X, W') => r • M.res h e)

namespace IsFrame

variable {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}

theorem restrict (hf : IsFrame M W e) {W₁ : X.Opens} (h : W₁ ≤ W) :
    IsFrame M W₁ (M.res h e) := by
  intro W' h'
  rw [res_res]
  exact hf W' _

def coordEquiv (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) :
    Γ(M, W') ≃ₗ[Γ(X, W')] Γ(X, W') :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton Γ(X, W') Γ(M, W') (M.res h e)) (hf W' h)).symm

def coord (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W')) : Γ(X, W') :=
  hf.coordEquiv h x

@[simp] theorem coord_smul_frame (hf : IsFrame M W e) {W' : X.Opens}
    (h : W' ≤ W) (x : Γ(M, W')) : hf.coord h x • M.res h e = x :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton Γ(X, W') Γ(M, W') (M.res h e)) (hf W' h)).apply_symm_apply x

end IsFrame

theorem exists_frame (M : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] (point : X) :
    ∃ (W : X.Opens) (_ : point ∈ W) (e : Γ(M, W)), IsFrame M W e := by
  obtain ⟨W, trivialization, contains⟩ := M.exists_mem_trivialization point
  refine ⟨W, contains, M.trivializationGenerator trivialization, ?_⟩
  intro smaller inclusion
  let coordinates := M.trivializationCoordinate trivialization (homOfLE inclusion)
  have formula : ∀ scalar : Γ(X, smaller),
      coordinates.symm scalar = scalar • M.res inclusion (M.trivializationGenerator trivialization) := by
    intro scalar
    have representation := M.eq_trivializationCoordinate_smul_map_trivializationGenerator
      trivialization (homOfLE inclusion) (coordinates.symm scalar)
    simpa only [coordinates, LinearEquiv.apply_symm_apply] using representation
  rw [← funext formula]
  exact coordinates.symm.bijective

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

@[simp] theorem moduleStalkMap_germ (X : Scheme.{u}) (x : X) {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    moduleStalkMap X x f (M.presheaf.germ U x hx m) =
      N.presheaf.germ U x hx (f.app U m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.mapPresheaf m

abbrev stalk (M : X.Modules) (x : X) : ModuleCat.{u} (X.presheaf.stalk x) :=
  (moduleStalkFunctor X x).obj M

end AlgebraicGeometry.Scheme.Modules
