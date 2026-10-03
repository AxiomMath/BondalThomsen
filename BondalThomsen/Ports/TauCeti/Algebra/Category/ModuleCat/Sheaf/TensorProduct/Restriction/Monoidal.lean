module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor

@[expose] public section

open CategoryTheory Category MonoidalCategory

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u}) (X : C)

local notation "sourceSheafification" =>
  PresheafOfModules.sheafification
    (𝟙 (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))

local notation "targetSheafification" =>
  PresheafOfModules.sheafification
    (𝟙 (ObjectProperty.FullSubcategory.obj (Sheaf.over (ringCatSheaf R) X)))

local notation "presheafRestriction" =>
  PresheafOfModules.pushforward (F := Over.forget X)
    (Iso.inv (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X)
      (ringCatSheaf R)))

local notation "restrictionSheafification" => presheafRestriction ⋙ targetSheafification

local notation "sourceW" =>
  MorphismProperty.inverseImage (J.W (A := AddCommGrpCat))
    (PresheafOfModules.toPresheaf (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))

local instance overSheafificationLifting : CategoryTheory.Localization.Lifting
    sourceSheafification sourceW restrictionSheafification
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) where
  iso := overSheafificationNatIso (ringCatSheaf R) X

local instance : MonoidalCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

local instance : SymmetricCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  symmetricCategory (R.over X)

local instance : MonoidalCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := (R.over X).obj)

local instance : SymmetricCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := (R.over X).obj)

local instance overPresheafFunctorMonoidal : (presheafRestriction).Monoidal := by
  change (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj).Monoidal
  infer_instance

local instance overPresheafFunctorBraided : (presheafRestriction).Braided where
  braided _ _ := by
    rfl

local instance overTargetSheafificationBraided : (targetSheafification).Braided :=
  sheafificationBraided (R.over X)

local instance overSheafificationBraided : (restrictionSheafification).Braided := by
  exact @Functor.Braided.instComp _ _ _ _ _ _ _ _ _ _ _ _
    presheafRestriction targetSheafification inferInstance inferInstance

instance _root_.SheafOfModules.overFunctorMonoidal :
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).Monoidal :=
  @CategoryTheory.Localization.Monoidal.functorMonoidalOfComp
    _ _ _ _ _ _ _ _ _ sourceSheafification sourceW _ _
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) restrictionSheafification
    (overSheafificationBraided R X).toMonoidal _ (overSheafificationLifting R X)

instance _root_.SheafOfModules.overFunctorBraided :
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).Braided where
  braided M N := by
    let _ : CategoryTheory.Localization.Lifting
        sourceSheafification sourceW
        restrictionSheafification
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) :=
      overSheafificationLifting R X
    let _ : (restrictionSheafification).Braided := overSheafificationBraided R X
    let _ : (restrictionSheafification).Monoidal :=
      (overSheafificationBraided R X).toMonoidal
    change
      ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
        sourceSheafification sourceW
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
        restrictionSheafification).hom.app M).app N ≫
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map (β_ M N).hom =
        (β_ ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M)
          ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj N)).hom ≫
          ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
            sourceSheafification sourceW
            (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
            restrictionSheafification).hom.app N).app M
    rw [CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
      sourceSheafification sourceW
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      restrictionSheafification (sheafificationIso (ringCatSheaf R) M).symm
      (sheafificationIso (ringCatSheaf R) N).symm,
      CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
      sourceSheafification sourceW
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      restrictionSheafification (sheafificationIso (ringCatSheaf R) N).symm
      (sheafificationIso (ringCatSheaf R) M).symm]
    simp only [Category.assoc, ← Functor.map_comp]
    have sheafification_braiding :
        Functor.OplaxMonoidal.δ sourceSheafification M.val N.val ≫
            (β_ ((sourceSheafification).obj M.val)
              ((sourceSheafification).obj N.val)).hom =
          (sourceSheafification).map (β_ M.val N.val).hom ≫
            Functor.OplaxMonoidal.δ sourceSheafification N.val M.val := by
      rw [← cancel_mono (Functor.LaxMonoidal.μ
        sourceSheafification N.val M.val)]
      simp
    rw [BraidedCategory.braiding_naturality, reassoc_of% sheafification_braiding,
      Functor.map_comp]
    have lifting_naturality :
        (restrictionSheafification).map (β_ M.val N.val).hom ≫
            (CategoryTheory.Localization.Lifting.iso
              sourceSheafification sourceW restrictionSheafification
              (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.app
                (N.val ⊗ M.val) =
          (CategoryTheory.Localization.Lifting.iso
              sourceSheafification sourceW restrictionSheafification
              (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.app
                (M.val ⊗ N.val) ≫
            (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
              ((sourceSheafification).map (β_ M.val N.val).hom) :=
      (CategoryTheory.Localization.Lifting.iso
        sourceSheafification sourceW restrictionSheafification
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.naturality
          (β_ M.val N.val).hom
    rw [← reassoc_of% lifting_naturality]
    have presheaf_braiding :
        Functor.LaxMonoidal.μ restrictionSheafification M.val N.val ≫
            (targetSheafification).map
              ((presheafRestriction).map (β_ M.val N.val).hom) =
          (β_ ((restrictionSheafification).obj M.val)
            ((restrictionSheafification).obj N.val)).hom ≫
            Functor.LaxMonoidal.μ restrictionSheafification N.val M.val :=
      Functor.LaxBraided.braided (F := restrictionSheafification) M.val N.val
    rw [reassoc_of% presheaf_braiding]
    have comparison_braiding := BraidedCategory.braiding_naturality
      ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          (sheafificationIso (ringCatSheaf R) M).symm.hom ≫
        (CategoryTheory.Localization.Lifting.iso
          sourceSheafification sourceW restrictionSheafification
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).hom.app M.val)
      ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          (sheafificationIso (ringCatSheaf R) N).symm.hom ≫
        (CategoryTheory.Localization.Lifting.iso
          sourceSheafification sourceW restrictionSheafification
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).hom.app N.val)
    rw [reassoc_of% comparison_braiding]

variable {R}

def _root_.SheafOfModules.overTensorIso
    (M N : SheafOfModules.{u} (ringCatSheaf R)) (X : C) :
    @Iso (SheafOfModules.{u} (ringCatSheaf (R.over X))) _ ((M ⊗ N).over X)
      (M.over X ⊗ N.over X) :=
  (Functor.Monoidal.μIso
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N).symm

@[simp]
theorem _root_.SheafOfModules.overTensorIso_hom
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overTensorIso N X).hom =
      Functor.OplaxMonoidal.δ
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N :=
  (rfl)

end SheafOfModules

end

end TauCeti
