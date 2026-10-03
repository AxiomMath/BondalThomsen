module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ResidueFieldDegree
public import Mathlib.AlgebraicGeometry.ResidueField

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

theorem AlgebraicGeometry.Scheme.Hom.residueDegree_specMap {sourceRing targetRing : CommRingCat.{u}}
    (ringMap : sourceRing ⟶ targetRing) (point : Spec targetRing) :
    (Spec.map ringMap).residueDegree point =
      @Module.finrank ((Spec.map ringMap) point).asIdeal.ResidueField point.asIdeal.ResidueField _ _
        (@Algebra.toModule _ _ _ _ (Ideal.ResidueField.map _ _ ringMap.hom rfl).toAlgebra) := by
  unfold Scheme.Hom.residueDegree
  let _ : Algebra ((Spec sourceRing).residueField ((Spec.map ringMap) point))
      ((Spec targetRing).residueField point) := ((Spec.map ringMap).residueFieldMap point).hom.toAlgebra
  let _ : Algebra ((Spec.map ringMap) point).asIdeal.ResidueField point.asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ _ ringMap.hom rfl).toAlgebra
  let sourceEquiv : (Spec sourceRing).residueField ((Spec.map ringMap) point) ≃+*
      ((Spec.map ringMap) point).asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso sourceRing ((Spec.map ringMap) point)).commRingCatIsoToRingEquiv
  let targetEquiv : (Spec targetRing).residueField point ≃+* point.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso targetRing point).commRingCatIsoToRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv sourceEquiv targetEquiv ?_
  ext residue
  obtain ⟨stalkValue, rfl⟩ := IsLocalRing.residue_surjective residue
  have residueEquation : ∀ (ring : CommRingCat.{u}) (prime : Spec ring)
      (element : (Spec ring).presheaf.stalk prime),
      (Scheme.Spec.residueFieldIso ring prime).hom ((Spec ring).residue prime element) =
        IsLocalRing.residue _ ((Spec.stalkIso ring prime).hom element) := by
    intro ring prime element
    rw [← ConcreteCategory.comp_apply, Scheme.Spec.residue_residueFieldIso_hom,
      ConcreteCategory.comp_apply]
    rfl
  have mapEquation : ((Spec.map ringMap).residueFieldMap point) ((Spec sourceRing).residue _ stalkValue) =
      (Spec targetRing).residue point (((Spec.map ringMap).stalkMap point) stalkValue) := by
    have equation := ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap (Spec.map ringMap) point)
      stalkValue
    simpa only [ConcreteCategory.comp_apply] using equation
  have stalkEquation : (Spec.stalkIso targetRing point).hom (((Spec.map ringMap).stalkMap point) stalkValue) =
      Localization.localRingHom _ _ ringMap.hom rfl
        ((Spec.stalkIso sourceRing _).hom stalkValue) := by
    have equation := Scheme.localRingHom_comp_stalkIso_apply ringMap point stalkValue
    exact (congrArg (fun element => (Spec.stalkIso targetRing point).hom element) equation.symm).trans
      ((Spec.stalkIso targetRing point).inv_hom_id_apply _)
  change Ideal.ResidueField.map _ _ ringMap.hom rfl
      ((Scheme.Spec.residueFieldIso sourceRing ((Spec.map ringMap) point)).hom
        ((Spec sourceRing).residue _ stalkValue)) =
    (Scheme.Spec.residueFieldIso targetRing point).hom
      (((Spec.map ringMap).residueFieldMap point) ((Spec sourceRing).residue _ stalkValue))
  rw [residueEquation, mapEquation, residueEquation, stalkEquation]
  exact IsLocalRing.ResidueField.map_residue _ _
