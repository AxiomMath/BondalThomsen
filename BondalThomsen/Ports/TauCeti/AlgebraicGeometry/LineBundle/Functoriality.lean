module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Class

@[expose] public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X Y Z : Scheme.{u}}

lemma pullbackComp_obj_obj (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    ((pullback g ⋙ pullback f).obj L).obj =
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj L.obj :=
  (pullback_obj_obj f ((pullback g).obj L)).trans
    (congrArg (Scheme.Modules.pullback f).obj (pullback_obj_obj g L))

def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents (fun L ↦
    ObjectProperty.isoMk (SheafOfModules.isInvertible X)
      ((eqToIso (pullbackComp_obj_obj f g L)) ≪≫
        (Scheme.Modules.pullbackComp f g).app L.obj ≪≫
        eqToIso (pullback_obj_obj (f ≫ g) L).symm)) (by
    intro L K φ
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.isoMk_hom,
      Iso.trans_hom, eqToIso.hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      pullback_map, Functor.map_comp, Category.assoc, ObjectProperty.homMk_hom,
      eqToHom_trans_assoc, eqToHom_refl, eqToHom_map, eqToHom_trans,
      Category.id_comp]
    conv_lhs =>
      enter [2]
      rw [← Category.assoc]
    have h := (Scheme.Modules.pullbackComp f g).hom.naturality φ.hom
    simp only [Functor.comp_map] at h
    rw [h]
    simp only [Category.assoc])

end InvertibleSheaf

namespace LineBundleClass

variable {X Y Z : Scheme.{u}}

def pullback (f : X ⟶ Y) (a : LineBundleClass Y) : LineBundleClass X :=
  lift (fun L ↦ mk ((InvertibleSheaf.pullback f).obj L)) (fun _ _ ⟨e⟩ ↦
    mk_eq_mk_iff.mpr ⟨(SheafOfModules.isInvertible X).ι.mapIso
      ((InvertibleSheaf.pullback f).mapIso
        (ObjectProperty.isoMk (SheafOfModules.isInvertible Y) e))⟩) a

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
