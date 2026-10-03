module

public import BondalThomsen.Toric.Positivity.PrimitivePairHom
public import BondalThomsen.Toric.Divisor.DivisorTensorEquivalence
public import BondalThomsen.Toric.Divisor.DivisorInternalHom
public import BondalThomsen.Derived.SheafExtCohomologyDimensionShift

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme.Modules

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def invariantClassTensorAddIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisorClass) :
    (fan.invariantClassInvertibleSheaf 𝕜 complete regular first).obj ⊗
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular second).obj ≅
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular (first + second)).obj := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular
    (fan.completeFan_nonemptyCones complete)
  let source := fan.invariantClassInvertibleSheaf 𝕜 complete regular first
  let target := fan.invariantClassInvertibleSheaf 𝕜 complete regular second
  let product := TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorProduct source target
  have classes : TauCeti.AlgebraicGeometry.LineBundleClass.mk product =
      TauCeti.AlgebraicGeometry.LineBundleClass.mk
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular (first + second)) := by
    rw [TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorProduct,
      fan.invariantClassInvertibleSheaf_class 𝕜,
      fan.invariantClassInvertibleSheaf_class 𝕜,
      fan.invariantClassInvertibleSheaf_class 𝕜, map_add]
    rfl
  exact SheafOfModules.tensorUnderlyingIso source.obj target.obj ≪≫
    (TauCeti.SheafOfModules.tensorProductIso
      (fan.algebraicRealization 𝕜 regular).sheaf source.obj target.obj).symm ≪≫
    (TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mp classes).some

noncomputable def invariantClassZeroIsoUnit (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    (fan.invariantClassInvertibleSheaf 𝕜 complete regular 0).obj ≅
      𝟙_ (fan.algebraicRealization 𝕜 regular).Modules := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular
    (fan.completeFan_nonemptyCones complete)
  have classes := fan.invariantClassInvertibleSheaf_iso_divisor 𝕜 complete regular
    (0 : fan.InvariantRayDivisor)
  rw [map_zero] at classes
  exact classes.some ≪≫
    eqToIso (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf
      (map_zero (fan.invariantDivisorCartierHom 𝕜 complete regular))) ≪≫
    BondalThomsen.CartierDivisorTensorEquivalence.zeroIsoUnit

noncomputable def invariantClassTensorEquivalence (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor_class : fan.InvariantRayDivisorClass) :
    (fan.algebraicRealization 𝕜 regular).Modules ≌
      (fan.algebraicRealization 𝕜 regular).Modules := by
  let scheme := fan.algebraicRealization 𝕜 regular
  let source := (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj
  let inverse := (fan.invariantClassInvertibleSheaf 𝕜 complete regular (-divisor_class)).obj
  let source_inverse : source ⊗ inverse ≅ 𝟙_ scheme.Modules :=
    fan.invariantClassTensorAddIso 𝕜 complete regular divisor_class (-divisor_class) ≪≫
      eqToIso (congrArg (fun member =>
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular member).obj)
          (add_neg_cancel divisor_class)) ≪≫ fan.invariantClassZeroIsoUnit 𝕜 complete regular
  let inverse_source : inverse ⊗ source ≅ 𝟙_ scheme.Modules :=
    fan.invariantClassTensorAddIso 𝕜 complete regular (-divisor_class) divisor_class ≪≫
      eqToIso (congrArg (fun member =>
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular member).obj)
          (neg_add_cancel divisor_class)) ≪≫ fan.invariantClassZeroIsoUnit 𝕜 complete regular
  exact CategoryTheory.Equivalence.mk (tensorLeft source) (tensorLeft inverse)
    ((leftUnitorNatIso scheme.Modules).symm ≪≫
      ((tensoringLeft scheme.Modules).mapIso inverse_source).symm ≪≫
      tensorLeftTensor inverse source)
    ((tensorLeftTensor source inverse).symm ≪≫
      (tensoringLeft scheme.Modules).mapIso source_inverse ≪≫
      leftUnitorNatIso scheme.Modules)

noncomputable def invariantClassInternalHomTensorInverseIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor_class : fan.InvariantRayDivisorClass) :
    ihom (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj ≅
      tensorLeft (fan.invariantClassInvertibleSheaf 𝕜 complete regular (-divisor_class)).obj :=
  (ihom.adjunction
    (fan.invariantClassInvertibleSheaf 𝕜 complete regular divisor_class).obj).rightAdjointUniq
      (fan.invariantClassTensorEquivalence 𝕜 complete regular divisor_class).toAdjunction

end TauCeti.Toric.Fan
