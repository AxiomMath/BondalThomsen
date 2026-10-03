module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.GlobalSections

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} {M : X.Modules}

section TrivializationScalar

variable {V : X.Opens} (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)

def Hom.trivializationScalar (φ : M ⟶ M) : Γ(X, V) :=
  trivializationCoordinate M t (𝟙 V) (φ.app V (trivializationGenerator M t))

@[simp]
theorem Hom.app_trivializationGenerator (φ : M ⟶ M) :
    φ.app V (trivializationGenerator M t) =
      φ.trivializationScalar t • trivializationGenerator M t := by
  have h := eq_trivializationCoordinate_smul_map_trivializationGenerator M t (𝟙 V)
    (φ.app V (trivializationGenerator M t))
  rwa [op_id, M.presheaf.map_id, ConcreteCategory.id_apply] at h

theorem Hom.app_eq_trivializationScalar_smul (φ : M ⟶ M) {W : X.Opens} (i : W ⟶ V)
    (s : Γ(M, W)) :
    φ.app W s = X.presheaf.map i.op (φ.trivializationScalar t) • s := by
  have hs := eq_trivializationCoordinate_smul_map_trivializationGenerator M t i s
  have hnat : φ.app W (M.presheaf.map i.op (trivializationGenerator M t)) =
      M.presheaf.map i.op (φ.app V (trivializationGenerator M t)) := by
    simpa only [mapPresheaf_app, unop_op] using
      φ.mapPresheaf.naturality_apply i.op (trivializationGenerator M t)
  calc φ.app W s
      = φ.app W (trivializationCoordinate M t i s •
          M.presheaf.map i.op (trivializationGenerator M t)) := by rw [← hs]
    _ = trivializationCoordinate M t i s • X.presheaf.map i.op (φ.trivializationScalar t) •
          M.presheaf.map i.op (trivializationGenerator M t) := by
        rw [Hom.app_smul, hnat, Hom.app_trivializationGenerator, Modules.map_smul]
    _ = X.presheaf.map i.op (φ.trivializationScalar t) • s := by
        rw [smul_smul, mul_comm, ← smul_smul, ← hs]

theorem Hom.map_trivializationScalar_eq (φ : M ⟶ M) {V₁ V₂ W : X.Opens}
    (t₁ : SheafOfModules.free (R := X.ringCatSheaf.over V₁) PUnit ≅ M.over V₁)
    (t₂ : SheafOfModules.free (R := X.ringCatSheaf.over V₂) PUnit ≅ M.over V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) :
    X.presheaf.map i₁.op (φ.trivializationScalar t₁) =
      X.presheaf.map i₂.op (φ.trivializationScalar t₂) := by
  have h := (φ.app_eq_trivializationScalar_smul t₁ i₁
    (M.presheaf.map i₁.op (trivializationGenerator M t₁))).symm.trans
      (φ.app_eq_trivializationScalar_smul t₂ i₂
        (M.presheaf.map i₁.op (trivializationGenerator M t₁)))
  have h' := congrArg (trivializationCoordinate M t₁ i₁) h
  simpa only [LinearEquiv.map_smul, trivializationCoordinate_map_trivializationGenerator,
    smul_eq_mul, mul_one] using h'

end TrivializationScalar

section Invertible

variable (M) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]

theorem globalSectionsAction_injective : Function.Injective (globalSectionsAction M) := by
  intro r s hrs
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  have hcover : (⊤ : X.Opens) ≤ iSup t.X :=
    ((Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop).iSup_eq_top.ge
  apply X.sheaf.eq_of_locally_eq' t.X ⊤ (fun i ↦ (t.X i).leTop) hcover
  intro i
  have h := congrArg (fun ψ : End M ↦ trivializationCoordinate M (t.iso i) (𝟙 (t.X i))
    (ψ.app (t.X i) (trivializationGenerator M (t.iso i)))) hrs
  have key : X.presheaf.map (t.X i).leTop.op r = X.presheaf.map (t.X i).leTop.op s := by
    simpa only [globalSectionsAction_apply, globalSectionsSmul_app, smul_apply,
      LinearEquiv.map_smul, trivializationCoordinate_trivializationGenerator, smul_eq_mul,
      mul_one] using h
  exact key

theorem globalSectionsAction_surjective : Function.Surjective (globalSectionsAction M) := by
  intro φ
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  have hcover : (⊤ : X.Opens) ≤ iSup t.X :=
    ((Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop).iSup_eq_top.ge
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf t.X
      fun i ↦ φ.trivializationScalar (t.iso i) := fun i j ↦
    φ.map_trivializationScalar_eq (t.iso i) (t.iso j) (Opens.infLELeft _ _) (Opens.infLERight _ _)
  have key : ∃ r : Γ(X, ⊤), ∀ i, X.presheaf.map (t.X i).leTop.op r =
      φ.trivializationScalar (t.iso i) := by
    obtain ⟨r, hr, -⟩ :=
      X.sheaf.existsUnique_gluing' t.X ⊤ (fun i ↦ (t.X i).leTop) hcover _ hcompat
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := key
  refine ⟨r, ?_⟩
  rw [globalSectionsAction_apply]
  refine Modules.hom_ext _ _ fun U ↦ ?_
  ext x
  rw [globalSectionsSmul_app, smul_apply]
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i ↦ U ⊓ t.X i) U (fun i ↦ homOfLE inf_le_left)
  · rw [← inf_iSup_eq]
    exact le_inf le_rfl (le_top.trans hcover)
  · intro i
    have hnat : M.presheaf.map (homOfLE inf_le_left : U ⊓ t.X i ⟶ U).op (φ.app U x) =
        φ.app (U ⊓ t.X i) (M.presheaf.map (homOfLE inf_le_left).op x) := by
      simpa only [mapPresheaf_app, unop_op] using
        (φ.mapPresheaf.naturality_apply (homOfLE inf_le_left : U ⊓ t.X i ⟶ U).op x).symm
    have hglobal {V W : X.Opens} (j : W ⟶ V) :
        X.presheaf.map j.op (X.presheaf.map V.leTop.op r) = X.presheaf.map W.leTop.op r := by
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
      rfl
    rw [Modules.map_smul, hnat,
      φ.app_eq_trivializationScalar_smul (t.iso i) (homOfLE inf_le_right), ← hr i, hglobal,
      hglobal]

theorem globalSectionsAction_bijective : Function.Bijective (globalSectionsAction M) :=
  ⟨globalSectionsAction_injective M, globalSectionsAction_surjective M⟩

def globalSectionsActionRingEquiv : Γ(X, ⊤) ≃+* End M :=
  RingEquiv.ofBijective _ (globalSectionsAction_bijective M)

end Invertible

end

end AlgebraicGeometry.Scheme.Modules
