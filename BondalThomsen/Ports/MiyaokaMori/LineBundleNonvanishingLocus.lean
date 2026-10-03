module

public import BondalThomsen.Ports.MiyaokaMori.ModuleSheafFrameStalk

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

theorem germ_smul' (M : X.Modules) {V : X.Opens} {y : X} (hy : y ∈ V) (r : Γ(X, V)) (m : Γ(M, V)) :
    M.presheaf.germ V y hy (r • m) = X.presheaf.germ V y hy r • M.presheaf.germ V y hy m :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val y V hy r m

theorem IsFrame.span_germ_eq_top {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {y : X} (hy : y ∈ W) :
    Submodule.span (X.presheaf.stalk y)
      ({(M.presheaf.germ W y hy e : ↥(M.stalk y))} : Set ↥(M.stalk y)) = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨V, hVW, hyV, t, rfl⟩ := M.presheaf.exists_le_germ_eq m hy
  have ht : t = hf.coord hVW t • M.res hVW e := (hf.coord_smul_frame hVW t).symm
  rw [ht, germ_smul', TopCat.Presheaf.germ_res_apply]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem IsFrame.germ_notMem_maximalIdeal_smul {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {y : X} (hy : y ∈ W) :
    M.presheaf.germ W y hy e ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
        (⊤ : Submodule (X.presheaf.stalk y) (M.stalk y)) := by
  intro hmem
  rw [← hf.span_germ_eq_top hy] at hmem
  obtain ⟨a, ha, hae'⟩ :=
    (Submodule.mem_smul_span_singleton (M := ↥(M.stalk y))).mp hmem
  have hu : IsUnit (1 - a) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a ((IsLocalRing.mem_maximalIdeal a).mp ha)
  have hz : (1 - a) • (M.presheaf.germ W y hy e : ↥(M.stalk y)) = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero_of_eq hae'.symm
  have hey : (M.presheaf.germ W y hy e : ↥(M.stalk y)) = 0 := by
    obtain ⟨u, hu'⟩ := hu
    have h2 : ((u⁻¹ : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) •
        ((1 - a) • (M.presheaf.germ W y hy e : ↥(M.stalk y))) = 0 := by
      rw [hz, smul_zero]
    rwa [smul_smul, ← hu', Units.inv_mul, one_smul] at h2
  have hzero : M.presheaf.germ W y hy e = M.presheaf.germ W y hy 0 := by
    rw [map_zero]; exact hey
  obtain ⟨W', hyW', iU, iV, hW'⟩ := M.presheaf.germ_eq y hy hy e 0 hzero
  rw [map_zero] at hW'
  have hres : M.res (leOfHom iU) e = 0 := hW'
  have hfr : IsFrame M W' (M.res (leOfHom iU) e) := hf.restrict (leOfHom iU)
  have h10 : (1 : Γ(X, W')) = 0 := (hfr W' le_rfl).1 (by simp [res_self, hres])
  have h1 := congrArg (X.presheaf.germ W' y hyW') h10
  simp at h1

theorem isOpen_setOf_germ_notMem_maximalIdeal_smul (L : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] (s : Γ(L, ⊤)) :
    IsOpen {x : X | L.presheaf.germ ⊤ x trivial s ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x))} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hxW, e, hf⟩ := exists_frame L x
  set f : Γ(X, W) := hf.coord le_rfl (L.res le_top s) with hfdef
  have hse : L.res le_top s = f • e := by
    have h := hf.coord_smul_frame le_rfl (L.res le_top s)
    rw [res_self] at h
    exact h.symm
  have key : ∀ (y : X) (hy : y ∈ W),
      L.presheaf.germ ⊤ y trivial s = X.presheaf.germ W y hy f • L.presheaf.germ W y hy e := by
    intro y hy
    have h0 : L.presheaf.germ W y hy (L.res le_top s) = L.presheaf.germ ⊤ y trivial s :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [← h0, hse, germ_smul']
  refine ⟨(X.basicOpen f : Set X), ?_, (X.basicOpen f).isOpen, ?_⟩
  · intro y hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨u, hu'⟩ := (X.mem_basicOpen f y hyW).mp hy
    intro hcon
    refine hf.germ_notMem_maximalIdeal_smul hyW ?_
    have he : L.presheaf.germ W y hyW e =
        (↑u⁻¹ : X.presheaf.stalk y) • L.presheaf.germ ⊤ y trivial s := by
      rw [key y hyW, ← hu', smul_smul, Units.inv_mul, one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ hcon
  · rw [SetLike.mem_coe, X.mem_basicOpen f x hxW]
    by_contra hnu
    refine hx ?_
    rw [key x hxW]
    exact Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x)))
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry in

noncomputable def AlgebraicGeometry.Scheme.Modules.nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] (s : Γ(L, ⊤)) : X.Opens :=
  ⟨{x | TopCat.Presheaf.germ L.presheaf ⊤ x trivial s ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x))},
    AlgebraicGeometry.Scheme.Modules.isOpen_setOf_germ_notMem_maximalIdeal_smul L s⟩

open AlgebraicGeometry in

theorem AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] (s : Γ(L, ⊤)) (x : X) :
    x ∈ L.nonvanishingLocus s ↔
      TopCat.Presheaf.germ L.presheaf ⊤ x trivial s ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x)) :=
  Iff.rfl

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

theorem IsFrame.inf_nonvanishingLocus_eq_basicOpen (L : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]
    (t : Γ(L, ⊤)) {W : X.Opens} {e : Γ(L, W)} (hf : IsFrame L W e) :
    W ⊓ L.nonvanishingLocus t = X.basicOpen (hf.coord le_rfl (L.res le_top t)) := by
  set f : Γ(X, W) := hf.coord le_rfl (L.res le_top t) with hfdef
  have hse : L.res le_top t = f • e := by
    have h := hf.coord_smul_frame le_rfl (L.res le_top t)
    rw [res_self] at h
    exact h.symm
  have key : ∀ (y : X) (hy : y ∈ W),
      L.presheaf.germ ⊤ y trivial t = X.presheaf.germ W y hy f • L.presheaf.germ W y hy e := by
    intro y hy
    have h0 : L.presheaf.germ W y hy (L.res le_top t) = L.presheaf.germ ⊤ y trivial t :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [← h0, hse, germ_smul']
  apply TopologicalSpace.Opens.ext
  ext y
  rw [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe,
    SetLike.mem_coe, mem_nonvanishingLocus]
  constructor
  · rintro ⟨hyW, hyt⟩
    rw [X.mem_basicOpen f y hyW]
    by_contra hnu
    refine hyt ?_
    rw [key y hyW]
    exact Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk y) (L.stalk y)))
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
  · intro hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨u, hu'⟩ := (X.mem_basicOpen f y hyW).mp hy
    refine ⟨hyW, fun hcon => hf.germ_notMem_maximalIdeal_smul hyW ?_⟩
    have he : L.presheaf.germ W y hyW e =
        (↑u⁻¹ : X.presheaf.stalk y) • L.presheaf.germ ⊤ y trivial t := by
      rw [key y hyW, ← hu', smul_smul, Units.inv_mul, one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ hcon

end AlgebraicGeometry.Scheme.Modules
