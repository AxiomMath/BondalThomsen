module

public import BondalThomsen.Ports.MiyaokaMori.AmpleLineBundle
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Toric.Divisor.PicardEquivalence

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace BondalThomsen

universe schemeUniverse

noncomputable def SchemeLineBundleClassAmple {scheme : Scheme.{schemeUniverse}} :
    LineBundleClass scheme → Prop :=
  LineBundleClass.lift (fun bundle => IsAmple bundle.obj)
    (fun _ _ comparison => propext (isAmple_iff_of_iso comparison.some))

@[simp] theorem schemeLineBundleClassAmple_mk_iff {scheme : Scheme.{schemeUniverse}}
    (bundle : InvertibleSheaf scheme) :
    SchemeLineBundleClassAmple (LineBundleClass.mk bundle) ↔ IsAmple bundle.obj := by
  simp only [SchemeLineBundleClassAmple, LineBundleClass.lift_mk]

theorem isAmple_iff_of_lineBundleClass_eq {scheme : Scheme.{schemeUniverse}}
    {first second : InvertibleSheaf scheme}
    (sameClass : LineBundleClass.mk first = LineBundleClass.mk second) :
    IsAmple first.obj ↔ IsAmple second.obj := by
  obtain ⟨comparison⟩ := LineBundleClass.mk_eq_mk_iff.mp sameClass
  exact isAmple_iff_of_iso comparison

end BondalThomsen

