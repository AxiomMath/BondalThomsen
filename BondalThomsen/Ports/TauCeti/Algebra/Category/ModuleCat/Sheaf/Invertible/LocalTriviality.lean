module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic

@[expose] public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

structure LocalTrivializations (M : SheafOfModules.{u} R) where

  I : Type u₁

  X : I → C

  coversTop : J.CoversTop X

  iso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ M.over (X i)

def _root_.SheafOfModules.LocalGeneratorsData.IsInvertible.trivializationIso
    {q : SheafOfModules.LocalGeneratorsData M}
    (hq : SheafOfModules.LocalGeneratorsData.IsInvertible q) (i : q.I) :
    _root_.SheafOfModules.free (R := R.over (q.X i)) PUnit ≅ M.over (q.X i) := by
  letI : Nonempty (q.generators i).I := hq.basisNonempty i
  letI : Subsingleton (q.generators i).I := hq.basisSubsingleton i
  exact
    ((_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
      Equiv.punitOfNonemptyOfSubsingleton.symm.toIso).trans
      (@asIso _ _ _ _ (q.generators i).π (hq.isLocallyFreeData.isIso i))

namespace LocalTrivializations

def ofIso (t : LocalTrivializations M) (e : M ≅ N) : LocalTrivializations N where
  I := t.I
  X := t.X
  coversTop := t.coversTop
  iso i := t.iso i ≪≫ (SheafOfModules.overFunctor R (t.X i)).mapIso e

theorem isInvertible (t : LocalTrivializations M) : IsInvertible M := by
  let q : SheafOfModules.LocalGeneratorsData.{u₁} M :=
    { I := t.I
      X := t.X
      coversTop := t.coversTop
      generators i :=
        (_root_.SheafOfModules.free.generatingSections
          (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom }
  refine ⟨q, ?_⟩
  refine
    { isLocallyFreeData :=
        { isIso := by
            change ∀ i : t.I, IsIso
              ((_root_.SheafOfModules.free.generatingSections
                (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom).π
            intro i
            rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
            simpa only [_root_.SheafOfModules.free.generatingSections_π, Category.id_comp] using
              inferInstanceAs (IsIso (t.iso i).hom) }
      basisNonempty := fun i ↦ ?_
      basisSubsingleton := fun i ↦ ?_ }
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Nonempty PUnit)
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Subsingleton PUnit)

def ofIsInvertible (M : SheafOfModules.{u} R) [hM : IsInvertible M] :
    LocalTrivializations M := by
  let q := hM.exists_isInvertible.choose
  let hq := hM.exists_isInvertible.choose_spec
  exact
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      iso i := hq.trivializationIso i }

end LocalTrivializations

end SheafOfModules

end

end TauCeti
