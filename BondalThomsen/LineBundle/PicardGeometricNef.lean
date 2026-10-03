module

public import BondalThomsen.LineBundle.GeneralAmpleGeometricNef
public import BondalThomsen.LineBundle.GloballyGeneratedPullback
public import BondalThomsen.LineBundle.GeometricNefClosedImmersionPullback
public import BondalThomsen.LineBundle.SchemePicardGlobalGeneration

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace BondalThomsen

universe schemeUniverse

noncomputable def SchemeLineBundleClassIsNef
    {baseField : Type schemeUniverse} [Field baseField]
    {scheme : Scheme.{schemeUniverse}}
    [scheme.Over (Spec (CommRingCat.of baseField))] : LineBundleClass scheme → Prop :=
  LineBundleClass.lift (fun bundle => AlgebraicGeometry.IsNef (baseField := baseField) bundle.obj)
    (by
      intro first second isomorphic
      obtain ⟨comparison⟩ := isomorphic
      exact propext (AlgebraicGeometry.isNef_iff_of_iso comparison))

@[simp] theorem schemeLineBundleClassIsNef_mk_iff
    {baseField : Type schemeUniverse} [Field baseField]
    {scheme : Scheme.{schemeUniverse}}
    [scheme.Over (Spec (CommRingCat.of baseField))]
    (bundle : InvertibleSheaf scheme) :
    SchemeLineBundleClassIsNef (baseField := baseField) (LineBundleClass.mk bundle) ↔
      AlgebraicGeometry.IsNef (baseField := baseField) bundle.obj := by
  rw [SchemeLineBundleClassIsNef, LineBundleClass.lift_mk]

variable {baseField : Type} [Field baseField] {scheme : Scheme.{0}}
    [scheme.Over (Spec (CommRingCat.of baseField))]

theorem schemeLineBundleClassIsNef_pow_iff
    (bundleClass : LineBundleClass scheme) {exponent : ℕ} (positive : 0 < exponent) :
    SchemeLineBundleClassIsNef (baseField := baseField) (bundleClass ^ exponent) ↔
      SchemeLineBundleClassIsNef (baseField := baseField) bundleClass := by
  obtain ⟨bundle, rfl⟩ := LineBundleClass.mk_surjective bundleClass
  rw [← invertibleSheafTensorPower_class bundle exponent,
    schemeLineBundleClassIsNef_mk_iff, schemeLineBundleClassIsNef_mk_iff]
  exact (AlgebraicGeometry.isNef_iff_of_iso
    (MiyaokaMori.invertibleSheafTensorPowerIso bundle exponent)).trans
      (AlgebraicGeometry.isNef_tensorPow_iff bundle.obj positive)

end BondalThomsen
