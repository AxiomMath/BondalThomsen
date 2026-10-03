module

public import BondalThomsen.Toric.Scheme.OverlapAlgebra
public import BondalThomsen.Fan.CompleteFanGlobalFunctions
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.Ring.Constructions

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem affineToricOverlap_isPullback (fan : Fan embedding) (regular : fan.IsRegular)
    (first second : fan.cones) :
    IsPullback (fan.affineToricOverlapLeft 𝕜 first second)
      (fan.affineToricOverlapRight 𝕜 first second)
      (fan.affineToricChartι 𝕜 regular first) (fan.affineToricChartι 𝕜 regular second) := by
  let := fan.isOpenImmersion_affineToricOverlapLeft 𝕜 first second (regular first.property)
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact fan.affineToricOverlap_comp_affineToricChartι 𝕜 regular first second
  · ext point
    change fan.affineToricChartι 𝕜 regular first point ∈
        Set.range (fan.affineToricChartι 𝕜 regular second) ↔
      point ∈ Set.range (fan.affineToricOverlapLeft 𝕜 first second)
    constructor
    · rintro ⟨second_point, same⟩
      obtain ⟨overlap_point, left_eq, _⟩ :=
        (fan.affineToricChartι_eq_affineToricChartι_iff 𝕜 regular point second_point).mp
          same.symm
      exact ⟨overlap_point, left_eq⟩
    · rintro ⟨overlap_point, rfl⟩
      refine ⟨fan.affineToricOverlapRight 𝕜 first second overlap_point, ?_⟩
      have same := congrArg (fun morphism : fan.affineToricOverlap 𝕜 first second ⟶
        fan.algebraicRealization 𝕜 regular => morphism overlap_point)
        (fan.affineToricOverlap_comp_affineToricChartι 𝕜 regular first second)
      simpa only [Scheme.Hom.comp_apply] using same.symm

noncomputable def chartTensorProductIso (fan : Fan embedding) (first second : fan.cones) :
    Spec (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice first.val ⊗[𝕜]
      (affineCoordinateRing 𝕜) fan.lattice second.val)) ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice first.val))))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice second.val)))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct 𝕜 (affineCoordinateRing 𝕜 fan.lattice first.val)
      (affineCoordinateRing 𝕜 fan.lattice second.val))).isoPullback

noncomputable def overlapToChartProduct (fan : Fan embedding) (first second : fan.cones) :
    fan.affineToricOverlap 𝕜 first second ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice first.val))))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice second.val)))) :=
  Spec.map (CommRingCat.ofHom (fan.overlapTensorMap 𝕜 first second).toRingHom) ≫
    (fan.chartTensorProductIso 𝕜 first second).hom

theorem overlapToChartProduct_fst (fan : Fan embedding) (first second : fan.cones) :
    fan.overlapToChartProduct 𝕜 first second ≫ pullback.fst _ _ =
      fan.affineToricOverlapLeft 𝕜 first second := by
  rw [overlapToChartProduct, chartTensorProductIso, Category.assoc,
    IsPullback.isoPullback_hom_fst, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((fan.overlapTensorMap 𝕜 first second).comp Algebra.TensorProduct.includeLeft).toRingHom)) = _
  rw [overlapTensorMap, Algebra.TensorProduct.productMap_left]
  rfl

theorem overlapToChartProduct_snd (fan : Fan embedding) (first second : fan.cones) :
    fan.overlapToChartProduct 𝕜 first second ≫ pullback.snd _ _ =
      fan.affineToricOverlapRight 𝕜 first second := by
  rw [overlapToChartProduct, chartTensorProductIso, Category.assoc,
    IsPullback.isoPullback_hom_snd, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((fan.overlapTensorMap 𝕜 first second).comp Algebra.TensorProduct.includeRight).toRingHom)) = _
  rw [overlapTensorMap, Algebra.TensorProduct.productMap_right]
  rfl

theorem overlapToChartProduct_isClosedImmersion (fan : Fan embedding) (first second : fan.cones) :
    IsClosedImmersion (fan.overlapToChartProduct 𝕜 first second) := by
  let := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (fan.overlapTensorMap 𝕜 first second).toRingHom)
    (fan.overlapTensorMap_surjective 𝕜 first second)
  unfold overlapToChartProduct
  infer_instance

theorem chartIntersectionComparison_isClosedImmersion (fan : Fan embedding)
    (regular : fan.IsRegular) (first second : fan.cones) :
    IsClosedImmersion (pullback.map
      (fan.affineToricChartι 𝕜 regular first) (fan.affineToricChartι 𝕜 regular second)
      (fan.affineToricChartι 𝕜 regular first ≫ fan.structureMap 𝕜 regular)
      (fan.affineToricChartι 𝕜 regular second ≫ fan.structureMap 𝕜 regular)
      (𝟙 _) (𝟙 _) (fan.structureMap 𝕜 regular) (by simp) (by simp)) := by
  let intersection_iso := (fan.affineToricOverlap_isPullback 𝕜 regular first second).isoPullback
  let product_iso := pullback.congrHom
    (fan.chartι_comp_structureMap 𝕜 regular first)
    (fan.chartι_comp_structureMap 𝕜 regular second)
  let comparison := pullback.map
      (fan.affineToricChartι 𝕜 regular first) (fan.affineToricChartι 𝕜 regular second)
      (fan.affineToricChartι 𝕜 regular first ≫ fan.structureMap 𝕜 regular)
      (fan.affineToricChartι 𝕜 regular second ≫ fan.structureMap 𝕜 regular)
      (𝟙 _) (𝟙 _) (fan.structureMap 𝕜 regular) (by simp) (by simp)
  have same : intersection_iso.hom ≫ comparison ≫ product_iso.hom =
      fan.overlapToChartProduct 𝕜 first second := by
    apply pullback.hom_ext
    · simp [intersection_iso, product_iso, comparison,
        fan.overlapToChartProduct_fst 𝕜 first second]
    · simp [intersection_iso, product_iso, comparison,
        fan.overlapToChartProduct_snd 𝕜 first second]
  have closed : IsClosedImmersion (intersection_iso.hom ≫ comparison ≫ product_iso.hom) := by
    rw [same]
    exact fan.overlapToChartProduct_isClosedImmersion 𝕜 first second
  rw [MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion] at closed
  exact closed

theorem structureMap_isSeparated (fan : Fan embedding) (regular : fan.IsRegular) :
    IsSeparated (fan.structureMap 𝕜 regular) := by
  constructor
  let cover := Scheme.Pullback.openCoverOfLeftRight
    (fan.toricChartOpenCover 𝕜 regular) (fan.toricChartOpenCover 𝕜 regular)
    (fan.structureMap 𝕜 regular) (fan.structureMap 𝕜 regular)
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) cover
  intro pair
  let square := pullback_map_diagonal_isPullback
    (fan.affineToricChartι 𝕜 regular pair.1) (fan.affineToricChartι 𝕜 regular pair.2)
    (fan.structureMap 𝕜 regular)
  let := fan.chartIntersectionComparison_isClosedImmersion 𝕜 regular pair.1 pair.2
  have closed : IsClosedImmersion (square.isoPullback.inv ≫
      pullback.map (fan.affineToricChartι 𝕜 regular pair.1) (fan.affineToricChartι 𝕜 regular pair.2)
        (fan.affineToricChartι 𝕜 regular pair.1 ≫ fan.structureMap 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular pair.2 ≫ fan.structureMap 𝕜 regular)
        (𝟙 _) (𝟙 _) (fan.structureMap 𝕜 regular) (by simp) (by simp)) := by
    infer_instance
  rw [IsPullback.isoPullback_inv_snd] at closed
  exact closed

theorem algebraicRealization_isSeparated (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).IsSeparated := by
  let := fan.structureMap_isSeparated 𝕜 regular
  let : (Spec (CommRingCat.of 𝕜)).IsSeparated := inferInstance
  constructor
  have same : fan.structureMap 𝕜 regular ≫ terminal.from (Spec (CommRingCat.of 𝕜)) =
      terminal.from (fan.algebraicRealization 𝕜 regular) := terminalIsTerminal.hom_ext _ _
  rw [← same]
  infer_instance

end TauCeti.Toric.Fan
