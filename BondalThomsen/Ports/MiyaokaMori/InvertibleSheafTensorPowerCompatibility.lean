module

public import BondalThomsen.Ports.MiyaokaMori.AmpleLineBundle
public import BondalThomsen.Toric.Positivity.SemiampleClassCriterion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace BondalThomsen.MiyaokaMori

def invertibleSheafTensorPowerIso {scheme : Scheme.{u}}
    (bundle : InvertibleSheaf scheme) : (exponent : ℕ) →
    (BondalThomsen.invertibleSheafTensorPower bundle exponent).obj ≅
      Scheme.Modules.tensorPow bundle.obj exponent
  | 0 => Scheme.Modules.isoOfSheafIso scheme
      (TauCeti.SheafOfModules.freePUnitIsoUnit scheme.ringCatSheaf)
  | exponent + 1 => Scheme.Modules.isoOfSheafIso scheme
      (TauCeti.SheafOfModules.tensorProductCongrLeft scheme.sheaf
        (Scheme.Modules.tensorPowerUnderlyingSheafIso
          (invertibleSheafTensorPowerIso bundle exponent)))

end BondalThomsen.MiyaokaMori
