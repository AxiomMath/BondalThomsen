module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

noncomputable def yonedaObjIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ≅ (Functor.const Cᵒᵖ).obj PUnit.{v + 1} :=
  (hT.isTerminalObj yoneda).uniqueUpToIso (Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit)

def freeObjPUnitIso :
    AddCommGrpCat.free.obj PUnit.{v + 1} ≅ AddCommGrpCat.of (ULift.{v} ℤ) :=
  AddEquiv.toAddCommGrpIso ((FreeAbelianGroup.uniqueEquiv PUnit).trans AddEquiv.ulift.symm)

noncomputable def freeYonedaObjIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  Functor.isoWhiskerRight (yonedaObjIsoConst hT) AddCommGrpCat.free ≪≫
    Functor.constComp (J := Cᵒᵖ) PUnit.{v + 1} AddCommGrpCat.free ≪≫
      (Functor.const Cᵒᵖ).mapIso freeObjPUnitIso

noncomputable section

variable [HasWeakSheafify J AddCommGrpCat.{v}]

def freeYonedaSheafIsoConstantSheaf {T : C} (hT : IsTerminal T) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J _).mapIso (freeYonedaObjIsoConst hT)

end

noncomputable section

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
noncomputable def functorHIso (n : ℕ) :
    _root_.CategoryTheory.Sheaf.functorH J n ≅
      (_root_.CategoryTheory.Abelian.extFunctor n).obj
        (op ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)))) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      intros
      ext
      rfl)

end

end CategoryTheory

end TauCeti

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (J) in

noncomputable def cohomologyPresheafEvaluationIsoFunctorH (n : ℕ) {T : C} (hT : IsTerminal T) :
    cohomologyPresheafFunctor J n ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op T) ≅
      functorH J n :=
  (Abelian.extFunctor n).mapIso
      (TauCeti.CategoryTheory.freeYonedaSheafIsoConstantSheaf hT).symm.op ≪≫
    TauCeti.CategoryTheory.functorHIso n

noncomputable abbrev cohomologyPresheafObjIsoH (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {T : C} (hT : IsTerminal T) :
    H' F n T ≅ AddCommGrpCat.of (H F n) :=
  (cohomologyPresheafEvaluationIsoFunctorH J n hT).app F

end CategoryTheory.Sheaf
