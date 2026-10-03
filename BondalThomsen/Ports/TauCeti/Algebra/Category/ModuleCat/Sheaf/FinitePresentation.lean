module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

theorem _root_.SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation
    {q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M} (hfree : q.IsLocallyFreeData)
    (hfinite : q.IsFiniteType) :
    M.IsFinitePresentation := by
  let : q.IsLocallyFreeData := hfree
  refine ⟨q.quasiCoherentData, ⟨fun i ↦ ?_⟩⟩
  refine
    { isFiniteType_generators := ?_
      isFiniteType_relations := ?_ }
  ·
    change (q.generators i).IsFiniteType
    exact hfinite.isFiniteType i
  · refine ⟨?_⟩
    change Finite (ULift Empty)
    infer_instance

instance isFinitePresentation_free [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Limits.HasBinaryProducts C] (I : Type u)
    [Finite I] : (_root_.SheafOfModules.free (R := R) I).IsFinitePresentation :=
  _root_.SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation
    (q := (_root_.SheafOfModules.free.generatingSections I).localGeneratorsData)
    inferInstance ⟨fun _ ↦ ⟨inferInstanceAs (Finite I)⟩⟩

end SheafOfModules

end

end TauCeti
