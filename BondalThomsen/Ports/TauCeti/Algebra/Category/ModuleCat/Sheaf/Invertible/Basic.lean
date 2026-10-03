module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

structure _root_.SheafOfModules.LocalGeneratorsData.IsInvertible
    (q : SheafOfModules.LocalGeneratorsData M) : Prop where

  isLocallyFreeData : q.IsLocallyFreeData

  basisNonempty (i : q.I) : Nonempty (q.generators i).I

  basisSubsingleton (i : q.I) : Subsingleton (q.generators i).I

variable (M) in

class IsInvertible : Prop where

  exists_isInvertible :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u₁} M,
      SheafOfModules.LocalGeneratorsData.IsInvertible q

instance IsInvertible.isLocallyFree (M : SheafOfModules.{u} R) [h : IsInvertible M] :
    M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  let := hq.isLocallyFreeData
  exact q.isLocallyFree

@[simps]
def _root_.SheafOfModules.LocalGeneratorsData.ofIso (q : SheafOfModules.LocalGeneratorsData M)
    (e : M ≅ N) :
    SheafOfModules.LocalGeneratorsData N where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom

theorem _root_.SheafOfModules.LocalGeneratorsData.IsInvertible.ofIso
    {q : SheafOfModules.LocalGeneratorsData M}
    (hq : SheafOfModules.LocalGeneratorsData.IsInvertible q) (e : M ≅ N) :
    SheafOfModules.LocalGeneratorsData.IsInvertible
      (SheafOfModules.LocalGeneratorsData.ofIso q e) where
  isLocallyFreeData :=
    { isIso := by
        change ∀ i : q.I, IsIso ((q.generators i).ofEpi
          ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom).π
        intro i
        rw [SheafOfModules.GeneratingSections.ofEpi_π]
        exact IsIso.comp_isIso' (hq.isLocallyFreeData.isIso i) inferInstance }
  basisNonempty i := by
    change Nonempty (q.generators i).I
    exact hq.basisNonempty i
  basisSubsingleton i := by
    change Subsingleton (q.generators i).I
    exact hq.basisSubsingleton i

theorem IsInvertible.of_iso (e : M ≅ N) [h : IsInvertible M] : IsInvertible N := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  exact ⟨SheafOfModules.LocalGeneratorsData.ofIso q e, hq.ofIso e⟩

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

instance free_isInvertible [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
    [Limits.HasBinaryProducts C] (I : Type u) [Nonempty I] [Subsingleton I] :
    IsInvertible (SheafOfModules.free (R := R) I) where
  exists_isInvertible :=
    ⟨(SheafOfModules.free.generatingSections (R := R) I).localGeneratorsData,
      { isLocallyFreeData := inferInstance
        basisNonempty := fun _ => by
          change Nonempty I
          infer_instance
        basisSubsingleton := fun _ => by
          change Subsingleton I
          infer_instance }⟩

end

end SheafOfModules

end

end TauCeti
