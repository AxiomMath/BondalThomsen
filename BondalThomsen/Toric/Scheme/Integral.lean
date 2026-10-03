module

public import BondalThomsen.Fan.CompleteFanGlobalFunctions
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Group.UniqueProds.VectorSpace
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative Set

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem character_uniqueSums (fan : Fan embedding) : UniqueSums (Lattice →+ ℤ) :=
  UniqueSums.of_injective_addHom fan.lattice.realCharacter.toAddHom
    fan.lattice.realCharacter_injective inferInstance

theorem laurentCharacterAlgebra_isDomain (fan : Fan embedding) :
    IsDomain (fan.LaurentCharacterAlgebra 𝕜) := by
  let := fan.character_uniqueSums
  infer_instance

theorem affineCoordinateRing_isDomain (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) : IsDomain (affineCoordinateRing 𝕜 fan.lattice cone) := by
  let := fan.laurentCharacterAlgebra_isDomain 𝕜
  exact Function.Injective.isDomain (fan.coneLaurentMap 𝕜 cone) (fan.coneLaurentMap_injective 𝕜 cone)

theorem affineToricChart_isIntegral (fan : Fan embedding) (cone : fan.cones) :
    IsIntegral (fan.affineToricChart 𝕜 cone) := by
  let := fan.affineCoordinateRing_isDomain 𝕜 cone.val
  infer_instance

theorem denseTorus_isIntegral (fan : Fan embedding) : IsIntegral (fan.denseTorus 𝕜) := by
  let := fan.affineCoordinateRing_isDomain 𝕜 ⊥
  infer_instance

theorem denseTorus_face_denseRange (fan : Fan embedding) (regular : fan.IsRegular)
    (cone : fan.cones) :
    DenseRange (faceAffineToricSchemeMap 𝕜 fan.lattice
      ((fan.isToricCone cone.property).salient.bot_isFaceOf)) := by
  let := fan.denseTorus_isIntegral 𝕜
  let := fan.affineToricChart_isIntegral 𝕜 cone
  let face_map := faceAffineToricSchemeMap 𝕜 fan.lattice
    ((fan.isToricCone cone.property).salient.bot_isFaceOf)
  let : IsOpenImmersion face_map :=
    (regular cone.property).isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _
  exact IsOpenMap.denseRange_of_isPreirreducibleSpace face_map
    face_map.isOpenEmbedding.isOpenMap

theorem denseTorusι_denseRange (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) : DenseRange (fan.denseTorusι 𝕜 regular nonempty) := by
  intro point
  obtain ⟨cone, local_point, rfl⟩ := fan.exists_affineToricChartι_apply_eq 𝕜 regular point
  have local_dense := fan.denseTorus_face_denseRange 𝕜 regular cone local_point
  have local_image_dense := image_closure_subset_closure_image
    (fan.affineToricChartι 𝕜 regular cone).continuous
    (Set.mem_image_of_mem (fan.affineToricChartι 𝕜 regular cone) local_dense)
  have images_eq :
      (fan.affineToricChartι 𝕜 regular cone) ''
          Set.range (faceAffineToricSchemeMap 𝕜 fan.lattice
            ((fan.isToricCone cone.property).salient.bot_isFaceOf)) =
        Set.range (fan.denseTorusι 𝕜 regular nonempty) := by
    rw [← fan.denseTorusι_eq 𝕜 regular nonempty (Nonempty.intro cone),
      fan.denseTorusι_face 𝕜 regular cone]
    ext image_point
    simp only [Set.mem_image, Set.mem_range, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨_, ⟨torus_point, rfl⟩, same⟩
      exact ⟨torus_point, same⟩
    · rintro ⟨torus_point, same⟩
      exact ⟨_, ⟨torus_point, rfl⟩, same⟩
  simpa only [images_eq] using local_image_dense

theorem algebraicRealization_irreducibleSpace (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) :
    IrreducibleSpace (fan.algebraicRealization 𝕜 regular) := by
  let := fan.denseTorus_isIntegral 𝕜
  have image_irreducible := (IrreducibleSpace.isIrreducible_univ (X := fan.denseTorus 𝕜)).image
    (fan.denseTorusι 𝕜 regular nonempty) (fan.denseTorusι 𝕜 regular nonempty).continuous.continuousOn
  rw [Set.image_univ] at image_irreducible
  have closed_irreducible := image_irreducible.closure
  rw [(fan.denseTorusι_denseRange 𝕜 regular nonempty).closure_range] at closed_irreducible
  exact (irreducibleSpace_def _).mpr closed_irreducible

theorem algebraicRealization_isReduced (fan : Fan embedding) (regular : fan.IsRegular) :
    IsReduced (fan.algebraicRealization 𝕜 regular) := by
  apply (IsReduced.iff_of_openCover _ (fan.toricChartOpenCover 𝕜 regular)).mpr
  intro cone
  change IsReduced (fan.affineToricChart 𝕜 cone)
  let := fan.affineToricChart_isIntegral 𝕜 cone
  infer_instance

theorem algebraicRealization_isIntegral (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) : IsIntegral (fan.algebraicRealization 𝕜 regular) := by
  let := fan.algebraicRealization_irreducibleSpace 𝕜 regular nonempty
  let := fan.algebraicRealization_isReduced 𝕜 regular
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end TauCeti.Toric.Fan
