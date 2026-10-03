module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Closure
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Associator
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.Sheaf
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X : Scheme.{u}}

def tensorProduct (L K : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨SheafOfModules.tensorProduct X.sheaf L.obj K.obj,
    by
      let _ : SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
      let _ : SheafOfModules.IsInvertible (R := X.ringCatSheaf) K.obj := K.property
      exact SheafOfModules.IsInvertible.tensorProduct (R := X.sheaf) (M := L.obj) (N := K.obj)⟩

@[simp]
lemma tensorProduct_obj (L K : InvertibleSheaf X) :
    (tensorProduct L K).obj = SheafOfModules.tensorProduct X.sheaf L.obj K.obj :=
  (rfl)

def tensorProductCongrLeftIso {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct L' K).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductCongrLeft (N := K.obj) X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e))

def tensorProductCongrLeft {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    tensorProduct L K ≅ tensorProduct L' K :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCongrLeftIso e))

def tensorProductCongrRightIso {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct L K').obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductCongrRight (M := L.obj) X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e))

def tensorProductCongrRight {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    tensorProduct L K ≅ tensorProduct L K' :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCongrRightIso e))

lemma isIsomorphic_tensorProduct {L L' K K' : InvertibleSheaf X}
    (hL : IsIsomorphic L L') (hK : IsIsomorphic K K') :
    IsIsomorphic (tensorProduct L K) (tensorProduct L' K') := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := hK
  exact ⟨tensorProductCongrLeft e ≪≫ tensorProductCongrRight f⟩

def tensorProductCommIso (L K : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct K L).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductComm X.sheaf L.obj K.obj)

def tensorProductComm (L K : InvertibleSheaf X) : tensorProduct L K ≅ tensorProduct K L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCommIso L K))

def tensorProductAssocIso (L K M : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct (tensorProduct L K) M).obj
      (tensorProduct L (tensorProduct K M)).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductAssoc X.sheaf L.obj K.obj M.obj)

def tensorProductAssoc (L K M : InvertibleSheaf X) :
    tensorProduct (tensorProduct L K) M ≅ tensorProduct L (tensorProduct K M) :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductAssocIso L K M))

def tensorTrivialLeftIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct (trivial X) L).obj L.obj := by
  simpa only [tensorProduct_obj, trivial_obj] using
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoLeft X.sheaf L.obj)

def tensorTrivialLeftIso (L : InvertibleSheaf X) : tensorProduct (trivial X) L ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorTrivialLeftIsoSheaf L))

def tensorTrivialRightIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L (trivial X)).obj L.obj := by
  simpa only [tensorProduct_obj, trivial_obj] using
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoRight X.sheaf L.obj)

def tensorTrivialRightIso (L : InvertibleSheaf X) : tensorProduct L (trivial X) ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorTrivialRightIsoSheaf L))

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
