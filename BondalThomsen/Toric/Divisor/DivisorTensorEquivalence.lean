module

public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.TensorProduct
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Representation

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

namespace BondalThomsen.CartierDivisorTensorEquivalence

universe schemeUniverse

variable {scheme : Scheme.{schemeUniverse}} [IsIntegral scheme]

noncomputable def tensorAddIso
    (first second : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor scheme) :
    first.sheaf ⊗ second.sheaf ≅ (first + second).sheaf :=
  SheafOfModules.tensorUnderlyingIso first.sheaf second.sheaf ≪≫
    (TauCeti.SheafOfModules.tensorProductIso scheme.sheaf first.sheaf second.sheaf).symm ≪≫
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.tensorProductSheafIso first second

noncomputable def zeroIsoUnit :
    (0 : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor scheme).sheaf ≅ 𝟙_ scheme.Modules := by
  have unit_eq : (𝟙_ scheme.Modules) = SheafOfModules.unit scheme.ringCatSheaf :=
    TauCeti.SheafOfModules.tensorUnit_eq scheme.sheaf
  exact (eqToIso (congrArg (fun cartier => cartier.sheaf)
      (TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_one scheme).symm)) ≪≫
    (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor
      scheme 1).symm ≪≫ eqToIso unit_eq.symm

noncomputable def tensorNegIsoUnit
    (divisor : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor scheme) :
    divisor.sheaf ⊗ (-divisor).sheaf ≅ 𝟙_ scheme.Modules :=
  tensorAddIso divisor (-divisor) ≪≫
    eqToIso (congrArg (fun cartier => cartier.sheaf) (add_neg_cancel divisor)) ≪≫ zeroIsoUnit

noncomputable def negTensorIsoUnit
    (divisor : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor scheme) :
    (-divisor).sheaf ⊗ divisor.sheaf ≅ 𝟙_ scheme.Modules :=
  tensorAddIso (-divisor) divisor ≪≫
    eqToIso (congrArg (fun cartier => cartier.sheaf) (neg_add_cancel divisor)) ≪≫ zeroIsoUnit

noncomputable def tensorEquivalence
    (divisor : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor scheme) :
    scheme.Modules ≌ scheme.Modules :=
  CategoryTheory.Equivalence.mk (tensorLeft divisor.sheaf) (tensorLeft (-divisor).sheaf)
    ((leftUnitorNatIso scheme.Modules).symm ≪≫
      ((tensoringLeft scheme.Modules).mapIso
        (negTensorIsoUnit divisor)).symm ≪≫
      tensorLeftTensor (-divisor).sheaf divisor.sheaf)
    ((tensorLeftTensor divisor.sheaf (-divisor).sheaf).symm ≪≫
      (tensoringLeft scheme.Modules).mapIso (tensorNegIsoUnit divisor) ≪≫
      leftUnitorNatIso scheme.Modules)

end BondalThomsen.CartierDivisorTensorEquivalence

namespace BondalThomsen

universe schemeUniverse

variable {scheme : Scheme.{schemeUniverse}} [IsIntegral scheme]

theorem invertibleSheafTensor_isEquivalence
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    (tensorLeft line_bundle.obj).IsEquivalence := by
  obtain ⟨divisor, ⟨sheaf_iso⟩⟩ :=
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.exists_nonempty_iso_sheaf line_bundle
  let : (tensorLeft divisor.sheaf).IsEquivalence :=
    (CartierDivisorTensorEquivalence.tensorEquivalence divisor).isEquivalence_functor
  exact Functor.isEquivalence_of_iso ((tensoringLeft scheme.Modules).mapIso sheaf_iso.symm)

end BondalThomsen

