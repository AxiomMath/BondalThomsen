module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LineBundleDegreeIndependence

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory

universe schemeUniverse

namespace IntegralCurve

variable {baseField : Type schemeUniverse} [Field baseField]
    {source target : Scheme.{schemeUniverse}}
    [source.Over (Spec (CommRingCat.of baseField))]
    [target.Over (Spec (CommRingCat.of baseField))]

def mapClosedImmersion (curve : IntegralCurve baseField source)
    (map : source ⟶ target) [IsClosedImmersion map]
    [map.IsOver (Spec (CommRingCat.of baseField))] : IntegralCurve baseField target where
  carrier := curve.carrier
  ι := curve.ι ≫ map
  isProper := by
    simpa only [Category.assoc, HomIsOver.comp_over] using curve.isProper
  dim_eq_one := curve.dim_eq_one

end IntegralCurve

namespace AlgebraicGeometry

variable {baseField : Type schemeUniverse} [Field baseField]
    {source target : Scheme.{schemeUniverse}}
    [source.Over (Spec (CommRingCat.of baseField))]
    [target.Over (Spec (CommRingCat.of baseField))]

theorem IsNef.pullback_of_isClosedImmersion (map : source ⟶ target)
    [IsClosedImmersion map] [map.IsOver (Spec (CommRingCat.of baseField))]
    {bundle : target.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target bundle]
    (nef : IsNef (baseField := baseField) bundle) :
    IsNef (baseField := baseField) ((Scheme.Modules.pullback map).obj bundle) := by
  intro curve
  let comparison :
      (Scheme.Modules.pullback curve.ι).obj ((Scheme.Modules.pullback map).obj bundle) ≅
        (Scheme.Modules.pullback (curve.ι ≫ map)).obj bundle :=
    (Scheme.Modules.pullbackComp curve.ι map).app bundle
  rw [curve.lineBundleDegree_eq_of_iso comparison]
  let : IsProper ((curve.ι ≫ map) ≫ (target ↘ Spec (CommRingCat.of baseField))) :=
    (curve.mapClosedImmersion map).isProper
  have ambientNef := nef (curve.mapClosedImmersion map)
  change 0 ≤ Intersection.lineBundleDegree
    ((curve.ι ≫ map) ≫ (target ↘ Spec (CommRingCat.of baseField)))
    curve.dim_eq_one.le ((Scheme.Modules.pullback (curve.ι ≫ map)).obj bundle) at ambientNef
  change 0 ≤ Intersection.lineBundleDegree
    (curve.ι ≫ (source ↘ Spec (CommRingCat.of baseField)))
    curve.dim_eq_one.le ((Scheme.Modules.pullback (curve.ι ≫ map)).obj bundle)
  simpa only [IntegralCurve.lineBundleDegree, IntegralCurve.over,
    Category.assoc, HomIsOver.comp_over] using ambientNef

end AlgebraicGeometry
