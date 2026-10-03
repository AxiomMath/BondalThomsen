module

public import BondalThomsen.LineBundle.GloballyGeneratedPullback
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Functoriality

@[expose] public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace BondalThomsen

universe schemeUniverse

variable {Source Target : Scheme.{schemeUniverse}}

noncomputable def SchemeLineBundleClassGloballyGenerated {scheme : Scheme.{schemeUniverse}} :
    LineBundleClass scheme → Prop :=
  LineBundleClass.lift (fun bundle => Nonempty bundle.obj.GeneratingSections)
    (by
      intro first second isomorphic
      obtain ⟨isomorphism⟩ := isomorphic
      exact propext (SheafOfModules.GeneratingSections.equivOfIso isomorphism).nonempty_congr)

@[simp] theorem schemeLineBundleClassGloballyGenerated_mk_iff
    {scheme : Scheme.{schemeUniverse}} (bundle : InvertibleSheaf scheme) :
    SchemeLineBundleClassGloballyGenerated (LineBundleClass.mk bundle) ↔
      Nonempty bundle.obj.GeneratingSections := by
  rw [SchemeLineBundleClassGloballyGenerated, LineBundleClass.lift_mk]

end BondalThomsen
