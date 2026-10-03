module

public import BondalThomsen.Toric.Frobenius.FrobeniusMorphism
public import BondalThomsen.Toric.Scheme.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem toricMultiplicationChart_mem_character_basicOpen (fan : Fan embedding)
    {degree : ℕ} (positive : 0 < degree) (cone : fan.cones)
    (character : dualSemigroup fan.lattice cone.val) (point : fan.affineToricChart 𝕜 cone) :
    fan.toricMultiplicationChart 𝕜 degree cone point ∈
        PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd character) (1 : 𝕜)) ↔
      point ∈ PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd character) (1 : 𝕜)) := by
  change (fan.toricMultiplicationRing 𝕜 degree cone.val)
      (MonoidAlgebra.single (ofAdd character) (1 : 𝕜)) ∉ point.asIdeal ↔
    MonoidAlgebra.single (ofAdd character) (1 : 𝕜) ∉ point.asIdeal
  rw [fan.toricMultiplicationRing_character 𝕜, point.isPrime.pow_mem_iff_mem degree positive]

theorem toricMultiplicationChart_mem_face_range (fan : Fan embedding)
    (regular : fan.IsRegular) {degree : ℕ} (positive : 0 < degree)
    (cone : fan.cones) {face_cone : PointedCone ℝ Ambient}
    (face : face_cone.IsFaceOf cone.val) (point : fan.affineToricChart 𝕜 cone) :
    fan.toricMultiplicationChart 𝕜 degree cone point ∈
        Set.range (faceAffineToricSchemeMap 𝕜 fan.lattice face) ↔
      point ∈ Set.range (faceAffineToricSchemeMap 𝕜 fan.lattice face) := by
  obtain ⟨character, contained, equation⟩ :=
    (regular cone.property).exists_mem_dualSemigroup_inf_ker_eq fan.lattice face
  rw [range_faceAffineToricSchemeMap_of_eq 𝕜 fan.lattice (regular cone.property).fg face
    ⟨character, contained⟩ equation]
  exact fan.toricMultiplicationChart_mem_character_basicOpen 𝕜 positive cone ⟨character, contained⟩ point

theorem toricMultiplication_preimage_chart_range (fan : Fan embedding)
    (regular : fan.IsRegular) {degree : ℕ} (positive : 0 < degree) (target : fan.cones) :
    fan.toricMultiplication 𝕜 regular degree ⁻¹' Set.range (fan.affineToricChartι 𝕜 regular target) =
      Set.range (fan.affineToricChartι 𝕜 regular target) := by
  ext point
  constructor
  · rintro ⟨target_point, target_eq⟩
    obtain ⟨source, source_point, source_eq⟩ := fan.exists_affineToricChartι_apply_eq 𝕜 regular point
    have chart_eq := congrArg (fun morphism : fan.affineToricChart 𝕜 source ⟶
      fan.algebraicRealization 𝕜 regular => morphism source_point)
      (fan.affineToricChartι_comp_toricMultiplication 𝕜 regular positive source)
    have overlap_eq : fan.affineToricChartι 𝕜 regular source
        (fan.toricMultiplicationChart 𝕜 degree source source_point) =
          fan.affineToricChartι 𝕜 regular target target_point := by
      simpa only [Scheme.Hom.comp_apply, source_eq, target_eq] using chart_eq.symm
    obtain ⟨overlap_point, left_eq, _⟩ :=
      (fan.affineToricChartι_eq_affineToricChartι_iff 𝕜 regular _ _).mp overlap_eq
    have image_member : fan.toricMultiplicationChart 𝕜 degree source source_point ∈
        Set.range (fan.affineToricOverlapLeft 𝕜 source target) := ⟨overlap_point, left_eq⟩
    rw [affineToricOverlapLeft_def] at image_member
    have source_member := (fan.toricMultiplicationChart_mem_face_range 𝕜 regular positive source
      (fan.inf_isFaceOf_left source.property target.property) source_point).mp image_member
    obtain ⟨preimage_overlap, left_preimage⟩ := source_member
    refine ⟨fan.affineToricOverlapRight 𝕜 source target preimage_overlap, ?_⟩
    have same := congrArg (fun morphism : fan.affineToricOverlap 𝕜 source target ⟶
      fan.algebraicRealization 𝕜 regular => morphism preimage_overlap)
      (fan.affineToricOverlap_comp_affineToricChartι 𝕜 regular source target)
    have left_preimage' : fan.affineToricOverlapLeft 𝕜 source target preimage_overlap = source_point :=
      left_preimage
    simpa only [Scheme.Hom.comp_apply, left_preimage', source_eq] using same.symm
  · rintro ⟨source_point, rfl⟩
    refine ⟨fan.toricMultiplicationChart 𝕜 degree target source_point, ?_⟩
    have same := congrArg (fun morphism : fan.affineToricChart 𝕜 target ⟶
      fan.algebraicRealization 𝕜 regular => morphism source_point)
      (fan.affineToricChartι_comp_toricMultiplication 𝕜 regular positive target)
    simpa only [Scheme.Hom.comp_apply] using same.symm

theorem toricMultiplication_preimage_chart_open (fan : Fan embedding)
    (regular : fan.IsRegular) {degree : ℕ} (positive : 0 < degree) (cone : fan.cones) :
    (TopologicalSpace.Opens.map (fan.toricMultiplication 𝕜 regular degree).base).obj
        (fan.affineToricChartι 𝕜 regular cone).opensRange =
      (fan.affineToricChartι 𝕜 regular cone).opensRange := by
  ext point
  exact Set.ext_iff.mp (fan.toricMultiplication_preimage_chart_range 𝕜 regular positive cone) point

theorem toricMultiplicationChart_isPullback (fan : Fan embedding)
    (regular : fan.IsRegular) {degree : ℕ} (positive : 0 < degree) (cone : fan.cones) :
    IsPullback (fan.toricMultiplicationChart 𝕜 degree cone)
      (fan.affineToricChartι 𝕜 regular cone) (fan.affineToricChartι 𝕜 regular cone)
      (fan.toricMultiplication 𝕜 regular degree) :=
  IsOpenImmersion.isPullback _ _ _ _
    (fan.affineToricChartι_comp_toricMultiplication 𝕜 regular positive cone)
    (fan.toricMultiplication_preimage_chart_open 𝕜 regular positive cone)

set_option backward.isDefEq.respectTransparency false in

theorem toricMultiplication_isFinite (fan : Fan embedding) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) :
    IsFinite (fan.toricMultiplication 𝕜 regular degree) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite)
    (fan.toricChartOpenCover 𝕜 regular)).mpr
  intro cone
  have pullback_square := fan.toricMultiplicationChart_isPullback 𝕜 regular positive cone
  let := fan.toricMultiplicationChart_isFinite 𝕜 regular positive cone
  change IsFinite (pullback.snd (fan.toricMultiplication 𝕜 regular degree)
    (fan.affineToricChartι 𝕜 regular cone))
  have identified := pullback_square.flip.isoPullback_hom_snd
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
    pullback_square.flip.isoPullback.hom _).mp (by
      rw [identified]
      infer_instance)

end TauCeti.Toric.Fan
