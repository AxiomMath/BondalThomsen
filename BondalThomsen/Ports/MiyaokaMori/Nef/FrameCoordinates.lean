module

public import BondalThomsen.Ports.MiyaokaMori.ModuleSheafFrameStalk
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Germ
public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}}

theorem res_smul (bundle : scheme.Modules) {smaller region : scheme.Opens}
    (subset : smaller ≤ region) (scalar : Γ(scheme, region)) (sectionValue : Γ(bundle, region)) :
    bundle.res subset (scalar • sectionValue) =
      scheme.presheaf.map (homOfLE subset).op scalar • bundle.res subset sectionValue :=
  Scheme.Modules.map_smul bundle (homOfLE subset) scalar sectionValue

namespace IsFrame

variable {bundle : scheme.Modules} {region : scheme.Opens} {generator : Γ(bundle, region)}

theorem coord_unique (frame : IsFrame bundle region generator) {smaller : scheme.Opens}
    (subset : smaller ≤ region) (sectionValue : Γ(bundle, smaller)) (scalar : Γ(scheme, smaller))
    (representation : scalar • bundle.res subset generator = sectionValue) :
    frame.coord subset sectionValue = scalar :=
  (frame smaller subset).1 ((frame.coord_smul_frame subset sectionValue).trans representation.symm)

theorem coord_eq_zero_iff (frame : IsFrame bundle region generator) {smaller : scheme.Opens}
    (subset : smaller ≤ region) (sectionValue : Γ(bundle, smaller)) :
    frame.coord subset sectionValue = 0 ↔ sectionValue = 0 :=
  (frame.coordEquiv subset).map_eq_zero_iff

theorem coord_map (frame : IsFrame bundle region generator) {smallest smaller : scheme.Opens}
    (firstSubset : smallest ≤ smaller) (secondSubset : smaller ≤ region)
    (sectionValue : Γ(bundle, smaller)) :
    frame.coord (firstSubset.trans secondSubset) (bundle.res firstSubset sectionValue) =
      scheme.presheaf.map (homOfLE firstSubset).op (frame.coord secondSubset sectionValue) := by
  apply frame.coord_unique
  have representation := congrArg (bundle.res firstSubset)
    (frame.coord_smul_frame secondSubset sectionValue)
  rw [← representation, ← bundle.res_res firstSubset secondSubset generator, res_smul]

theorem coord_restrict (frame : IsFrame bundle region generator) {smaller : scheme.Opens}
    (subset : smaller ≤ region) (sectionValue : Γ(bundle, smaller)) :
    (frame.restrict subset).coord le_rfl sectionValue = frame.coord subset sectionValue := by
  apply (frame.restrict subset).coord_unique
  simp only [res_self]
  exact frame.coord_smul_frame subset sectionValue

theorem unit_transition (frame : IsFrame bundle region generator)
    {otherGenerator : Γ(bundle, region)} (otherFrame : IsFrame bundle region otherGenerator) :
    ∃ unit : Γ(scheme, region)ˣ, (unit : Γ(scheme, region)) • generator = otherGenerator := by
  have firstRepresentation := frame.coord_smul_frame le_rfl otherGenerator
  have secondRepresentation := otherFrame.coord_smul_frame le_rfl generator
  simp only [res_self] at firstRepresentation secondRepresentation
  refine ⟨⟨frame.coord le_rfl otherGenerator, otherFrame.coord le_rfl generator, ?_, ?_⟩,
    firstRepresentation⟩
  · have equality := (frame region le_rfl).1
      (a₁ := frame.coord le_rfl otherGenerator * otherFrame.coord le_rfl generator) (a₂ := 1) (by
        simp only [res_self]
        rw [mul_comm, mul_smul, firstRepresentation, secondRepresentation, one_smul])
    exact equality
  · have equality := (otherFrame region le_rfl).1
      (a₁ := otherFrame.coord le_rfl generator * frame.coord le_rfl otherGenerator) (a₂ := 1) (by
        simp only [res_self]
        rw [mul_comm, mul_smul, secondRepresentation, firstRepresentation, one_smul])
    exact equality

theorem coord_globalSection_ne_zero [IsIntegral scheme]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    (frame : IsFrame bundle region generator) [Nonempty region]
    (sectionValue : Γ(bundle, ⊤)) (nonzero : sectionValue ≠ 0) :
    frame.coord le_rfl (bundle.res le_top sectionValue) ≠ 0 := by
  intro coordinateZero
  have restrictedZero := (frame.coord_eq_zero_iff le_rfl _).mp coordinateZero
  apply nonzero
  exact TauCeti.AlgebraicGeometry.InvertibleSheaf.map_injective_of_isIntegral
    ⟨bundle, inferInstance⟩ (homOfLE le_top) (restrictedZero.trans (map_zero _).symm)

end IsFrame

end AlgebraicGeometry.Scheme.Modules
