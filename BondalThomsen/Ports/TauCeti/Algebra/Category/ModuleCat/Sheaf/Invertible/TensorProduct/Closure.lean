module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Restriction
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Basic
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.CoversTop

@[expose] public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} (ringCatSheaf R)}

namespace LocalTrivializations

def tensorProduct (tM : LocalTrivializations.{u, v₁, u₁} M)
    (tN : LocalTrivializations.{u, v₁, u₁} N) :
    LocalTrivializations.{u, v₁, u₁} (SheafOfModules.tensorProduct R M N) := by
  let r : CategoryTheory.GrothendieckTopology.CoversTop.CommonRefinement.{u₁, v₁, u₁, u₁}
      J tM.X tN.X :=
    CategoryTheory.GrothendieckTopology.CoversTop.commonRefinement tM.coversTop tN.coversTop
  exact
    { I := r.I
      X := r.X
      coversTop := r.coversTop
      iso := fun i ↦ by
        let F : SheafOfModules.{u, v₁, max u₁ v₁} (ringCatSheaf (R.over (r.X i))) :=
          _root_.SheafOfModules.free (R := ringCatSheaf (R.over (r.X i))) (PUnit.{u + 1})
        exact (SheafOfModules.tensorProductFreePUnitIsoLeft.{u, v₁, max u₁ v₁}
          (R.over (r.X i)) F).symm ≪≫
          SheafOfModules.tensorProductCongrLeft.{u, v₁, max u₁ v₁} (R.over (r.X i))
            (tM.isoOver (r.leftIndex i) (r.left i)) ≪≫
          SheafOfModules.tensorProductCongrRight.{u, v₁, max u₁ v₁} (R.over (r.X i))
            (tN.isoOver (r.rightIndex i) (r.right i)) ≪≫
          (SheafOfModules.overTensorProductIso R M N (r.X i)).symm }

end LocalTrivializations

namespace IsInvertible

theorem tensorProduct [IsInvertible M] [IsInvertible N] :
    IsInvertible (SheafOfModules.tensorProduct R M N) := by
  let tM := LocalTrivializations.ofIsInvertible M
  let tN := LocalTrivializations.ofIsInvertible N
  exact (LocalTrivializations.tensorProduct tM tN).isInvertible

end IsInvertible

end SheafOfModules

end

end TauCeti
