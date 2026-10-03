module

public import BondalThomsen.LineBundle.GlobalGenerationGeometricNef
public import BondalThomsen.Ports.MiyaokaMori.Nef.LineBundleDegreeTensor
public import BondalThomsen.LineBundle.AmpleLineBundleArbitraryAffinePullback

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory

namespace BondalThomsen

variable {baseField : Type} [Field baseField] {scheme : Scheme.{0}}
    [scheme.Over (Spec (CommRingCat.of baseField))]

theorem invertibleSheaf_isNef_of_semiample
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (semiample : InvertibleSheafSemiample bundle) :
    AlgebraicGeometry.IsNef (baseField := baseField) bundle.obj := by
  obtain ⟨exponent, positive, generated⟩ := semiample
  let comparison := MiyaokaMori.invertibleSheafTensorPowerIso bundle exponent
  have tensorGenerated : Nonempty
      (Scheme.Modules.tensorPow bundle.obj exponent).GeneratingSections :=
    (SheafOfModules.GeneratingSections.equivOfIso comparison).nonempty_congr.mp generated
  exact AlgebraicGeometry.IsNef.of_tensorPow positive
    (globallyGeneratedInvertibleSheaf_isNef _ tensorGenerated)

end BondalThomsen
