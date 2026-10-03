module

public import BondalThomsen.Ports.MiyaokaMori.LineBundleNonvanishingLocus

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

theorem Submodule.mem_smul_top_linearEquiv_iff {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M ≃ₗ[R] N) (I : Ideal R) (v : M) :
    f v ∈ I • (⊤ : Submodule R N) ↔ v ∈ I • (⊤ : Submodule R M) := by
  have h : (I • (⊤ : Submodule R M)).map (f : M →ₗ[R] N) = I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 f.surjective]
  rw [← h, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hfy⟩
    exact f.injective hfy ▸ hy
  · intro hv
    exact ⟨v, hv, rfl⟩

noncomputable def AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') (x : X) :
    L.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L'.presheaf.stalk x :=
  ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor X x).mapIso e).toLinearEquiv

@[simp]
theorem AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso_apply
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') (x : X)
    (v : L.presheaf.stalk x) :
    AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso e x v =
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x e.hom v :=
  rfl

theorem AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L']
    (e : L ≅ L') (s : Γ(L, ⊤)) (x : X) :
    x ∈ L'.nonvanishingLocus (e.hom.app ⊤ s) ↔ x ∈ L.nonvanishingLocus s := by
  rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus,
    AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
  have hg : L'.presheaf.germ ⊤ x trivial (e.hom.app ⊤ s)
      = AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso e x
        (L.presheaf.germ ⊤ x trivial s) :=
    (AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x e.hom ⊤ trivial s).symm
  rw [hg]
  exact not_congr (Submodule.mem_smul_top_linearEquiv_iff _ _ _)

theorem AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L']
    (e : L ≅ L') (s : Γ(L, ⊤)) :
    L'.nonvanishingLocus (e.hom.app ⊤ s) = L.nonvanishingLocus s :=
  TopologicalSpace.Opens.ext (Set.ext fun x =>
    AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso e s x)
