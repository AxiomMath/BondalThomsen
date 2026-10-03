module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.TensorProduct

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

abbrev tensor {X : Scheme.{u}} (first second : X.Modules) : X.Modules :=
  TauCeti.SheafOfModules.tensorProduct X.sheaf first second

def tensorPow {X : Scheme.{u}} (bundle : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | exponent + 1 => tensor (tensorPow bundle exponent) bundle

instance tensorPow_isInvertible {X : Scheme.{u}} (bundle : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X bundle] (exponent : ℕ) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (tensorPow bundle exponent) := by
  induction exponent with
  | zero => exact TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_unit X
  | succ exponent induction_hypothesis =>
      let := induction_hypothesis
      exact TauCeti.SheafOfModules.IsInvertible.tensorProduct (R := X.sheaf)
        (M := tensorPow bundle exponent) (N := bundle)

def tensorPowerUnderlyingSheafIso {X : Scheme.{u}} {first second : X.Modules}
    (comparison : first ≅ second) : @Iso (SheafOfModules X.ringCatSheaf) _ first second :=
  { hom := ⟨comparison.hom.val⟩
    inv := ⟨comparison.inv.val⟩
    hom_inv_id := by
      apply SheafOfModules.Hom.ext
      exact congrArg (fun morphism => morphism.val) comparison.hom_inv_id
    inv_hom_id := by
      apply SheafOfModules.Hom.ext
      exact congrArg (fun morphism => morphism.val) comparison.inv_hom_id }

def tensorPowMapIso {X : Scheme.{u}} {first second : X.Modules} (comparison : first ≅ second) :
    (exponent : ℕ) → tensorPow first exponent ≅ tensorPow second exponent
  | 0 => Iso.refl _
  | exponent + 1 =>
      isoOfSheafIso X
        (TauCeti.SheafOfModules.tensorProductCongrLeft X.sheaf
          (tensorPowerUnderlyingSheafIso (tensorPowMapIso comparison exponent)) ≪≫
            TauCeti.SheafOfModules.tensorProductCongrRight X.sheaf (tensorPowerUnderlyingSheafIso comparison))

def tensorPowOneIso {X : Scheme.{u}} (bundle : X.Modules) : tensorPow bundle 1 ≅ bundle :=
  isoOfSheafIso X (TauCeti.SheafOfModules.tensorProductUnitIsoLeft X.sheaf bundle)

end AlgebraicGeometry.Scheme.Modules
