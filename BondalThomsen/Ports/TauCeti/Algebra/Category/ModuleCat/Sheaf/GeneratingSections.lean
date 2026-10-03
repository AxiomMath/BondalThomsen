module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction

@[expose] public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

section EquivOfIso

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

@[simp]
theorem _root_.SheafOfModules.GeneratingSections.equivOfIso_apply_I (e : M ≅ N)
    (σ : M.GeneratingSections) : (GeneratingSections.equivOfIso e σ).I = σ.I :=
  rfl

@[simp]
theorem _root_.SheafOfModules.GeneratingSections.equivOfIso_apply_π (e : M ≅ N)
    (σ : M.GeneratingSections) : (GeneratingSections.equivOfIso e σ).π = σ.π ≫ e.hom :=
  GeneratingSections.ofEpi_π _ _

instance _root_.SheafOfModules.GeneratingSections.isIso_equivOfIso_π (e : M ≅ N)
    (σ : M.GeneratingSections) [hσ : IsIso σ.π] : IsIso (GeneratingSections.equivOfIso e σ).π := by
  rw [GeneratingSections.equivOfIso_apply_π]
  exact IsIso.comp_isIso' hσ inferInstance

instance _root_.SheafOfModules.GeneratingSections.isFiniteType_equivOfIso (e : M ≅ N)
    (σ : M.GeneratingSections) [hσ : σ.IsFiniteType] :
    (GeneratingSections.equivOfIso e σ).IsFiniteType where
  finite := by
    rw [GeneratingSections.equivOfIso_apply_I]
    exact hσ.finite

end EquivOfIso

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R} {N : SheafOfModules.{u} S} (σ : M.GeneratingSections)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : unit S ≅ F.obj (unit R)) (e : F.obj M ≅ N)

noncomputable def _root_.SheafOfModules.GeneratingSections.mapIso : N.GeneratingSections :=
  GeneratingSections.equivOfIso e (σ.map F η)

instance _root_.SheafOfModules.GeneratingSections.isIso_mapIso_π [IsIso σ.π] :
    IsIso (σ.mapIso F η e).π :=
  (GeneratingSections.isIso_equivOfIso_π _ _)

instance _root_.SheafOfModules.GeneratingSections.isFiniteType_mapIso [hσ : σ.IsFiniteType] :
    (σ.mapIso F η e).IsFiniteType :=
  (GeneratingSections.isFiniteType_equivOfIso _ _)

end SheafOfModules

end

end TauCeti
