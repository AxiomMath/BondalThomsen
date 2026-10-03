module

public import BondalThomsen.ProjectiveBundle.FiberTransition
public import BondalThomsen.Toric.Scheme.TransitionUnits
public import BondalThomsen.Toric.Divisor.LineBundleGluing
public import BondalThomsen.Toric.Divisor.CartierChoiceIndependence
public import BondalThomsen.Toric.Divisor.PicardEquivalence

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CartierEquationAtlas

universe schemeUniverse

variable {SchemeModel : Scheme.{schemeUniverse}} [IsIntegral SchemeModel]

theorem frame_hom_ι (atlas : CartierEquationAtlas SchemeModel) (index : atlas.Index) :
    (atlas.chartTrivialization index).hom ≫
      atlas.cartierDivisor.sheafι.over (atlas.chart index) =
      (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions SchemeModel ≫
        TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul SchemeModel
          ((atlas.equation index : SchemeModel.functionField)⁻¹)).over (atlas.chart index) := by
  let := atlas.nonempty_chart index
  let equation := atlas.equation index
  let chart := atlas.chart index
  let principal := TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor SchemeModel equation
  let localIso := TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor
    SchemeModel equation
  let restrictionEq :=
    (TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_restrict SchemeModel equation chart).trans
      (atlas.cartierDivisor_restrict index).symm
  let restrictionIso := principal.sheafOverIsoOfRestrictEq atlas.cartierDivisor chart restrictionEq
  let restrictFunctor := SheafOfModules.overFunctor SchemeModel.ringCatSheaf chart
  change (restrictFunctor.map localIso.hom ≫ restrictionIso.hom) ≫
    atlas.cartierDivisor.sheafι.over chart = _
  calc
    _ = restrictFunctor.map localIso.hom ≫
        (restrictionIso.hom ≫ atlas.cartierDivisor.sheafι.over chart) := Category.assoc _ _ _
    _ = restrictFunctor.map localIso.hom ≫ principal.sheafι.over chart :=
      congrArg (fun morphism => restrictFunctor.map localIso.hom ≫ morphism)
        (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafOverIsoOfRestrictEq_hom_ι
          principal atlas.cartierDivisor chart restrictionEq)
    _ = restrictFunctor.map (localIso.hom ≫ principal.sheafι) :=
      (restrictFunctor.map_comp _ _).symm
    _ = restrictFunctor.map
        (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions SchemeModel ≫
          TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul SchemeModel
            ((equation : SchemeModel.functionField)⁻¹)) := by
      apply congrArg restrictFunctor.map
      simpa only [localIso, principal,
        TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor_hom,
        Units.val_inv_eq_inv_val] using
        (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitToSheafPrincipalCartierDivisor_ι equation)
    _ = _ := rfl

noncomputable def restrictedFrame (atlas : CartierEquationAtlas SchemeModel)
    (index : atlas.Index) (domain : SchemeModel.Opens) (contained : domain ≤ atlas.chart index) :
    (SheafOfModules.unit SchemeModel.ringCatSheaf).over domain ≅
      atlas.invertibleSheaf.obj.over domain :=
  ((SheafOfModules.overFunctorMap SchemeModel.ringCatSheaf (homOfLE contained)).app
      (SheafOfModules.unit SchemeModel.ringCatSheaf)).symm ≪≫
    (SheafOfModules.overMap SchemeModel.ringCatSheaf (homOfLE contained)).mapIso
      (atlas.chartTrivialization index) ≪≫
    (SheafOfModules.overFunctorMap SchemeModel.ringCatSheaf (homOfLE contained)).app
      atlas.invertibleSheaf.obj

end BondalThomsen.CartierEquationAtlas

namespace BondalThomsen.ProjectiveBundle

variable {rows baseDimension columns : ℕ}

variable {𝕜} in
local instance : IsIntegral (baseScheme 𝕜 rows baseDimension) := scheme_isIntegral 𝕜 0

end BondalThomsen.ProjectiveBundle
