module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

theorem TopCat.Presheaf.isReduced_stalk_of_isReduced_obj {space : TopCat.{u}}
    (presheaf : TopCat.Presheaf CommRingCat.{u} space)
    (sectionsReduced : ∀ region : Opens space, _root_.IsReduced (presheaf.obj (op region)))
    (point : space) : _root_.IsReduced (presheaf.stalk point) := by
  refine ⟨fun element nilpotent => ?_⟩
  obtain ⟨exponent, powerZero⟩ := nilpotent
  obtain ⟨region, containsPoint, sectionValue, rfl⟩ := presheaf.exists_germ_eq element
  have germPowerZero : presheaf.germ region point containsPoint (sectionValue ^ exponent) =
      presheaf.germ region point containsPoint 0 := by
    rw [map_pow, powerZero, map_zero]
  obtain ⟨neighborhood, containsNeighborhood, restriction, _, restrictedPowerZero⟩ :=
    presheaf.germ_eq point containsPoint containsPoint _ _ germPowerZero
  rw [map_pow, map_zero] at restrictedPowerZero
  have := sectionsReduced neighborhood
  have restrictedZero : presheaf.map restriction.op sectionValue = 0 :=
    IsReduced.eq_zero _ ⟨exponent, restrictedPowerZero⟩
  rw [← presheaf.germ_res_apply restriction point containsNeighborhood sectionValue,
    restrictedZero, map_zero]

theorem AlgebraicGeometry.Scheme.Hom.isIntegral_image {source target : Scheme.{u}}
    (morphism : source ⟶ target) [IsIntegral source] [QuasiCompact morphism] :
    IsIntegral morphism.image := by
  have imageReduced : IsReduced morphism.image := by
    have : ∀ point : morphism.image, _root_.IsReduced (morphism.image.presheaf.stalk point) :=
      fun point => by
        have pushforwardReduced := TopCat.Presheaf.isReduced_stalk_of_isReduced_obj
          (morphism.toImage.base _* source.presheaf) (fun _ => by dsimp; infer_instance) point
        exact @isReduced_of_injective _ _ _ _ _ _ _ _
          (morphism.stalkFunctor_toImage_injective point) pushforwardReduced
    exact isReduced_of_isReduced_stalk _
  have imageIrreducible : IrreducibleSpace morphism.image := by
    have denseRange : DenseRange morphism.toImage.base := morphism.toImage.denseRange
    have irreducibleRange := (IrreducibleSpace.isIrreducible_univ source).image
      morphism.toImage.base morphism.toImage.continuous.continuousOn
    rw [Set.image_univ] at irreducibleRange
    have irreducibleClosure := irreducibleRange.closure
    rw [denseRange.closure_range] at irreducibleClosure
    exact {
      toPreirreducibleSpace := ⟨irreducibleClosure.2⟩
      toNonempty := ⟨irreducibleClosure.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced _
