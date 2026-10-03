module

public import BondalThomsen.Fan.FiniteConeExtremalGenerators
public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators

namespace BondalThomsen.FiniteConeExposedFaces

open BondalThomsen.FiniteConeExtremalGenerators

section Algebraic

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]

theorem mem_hull_union_neg_face_generators {generators : Set Space}
    {face : PointedCone ℝ Space} {vector : Space}
    (membership : vector ∈ PointedCone.hull ℝ
      (generators ∪ (fun generator => -generator) '' (generators ∩ (face : Set Space)))) :
    ∃ coneVector ∈ PointedCone.hull ℝ generators,
      ∃ faceVector ∈ face, vector = coneVector - faceVector := by
  induction membership using Submodule.span_induction with
  | mem vector membership =>
      rcases membership with generatorMembership | negativeMembership
      · exact ⟨vector, PointedCone.subset_hull generatorMembership,
          0, face.zero_mem, by simp⟩
      · obtain ⟨generator, generatorMembership, rfl⟩ := negativeMembership
        exact ⟨0, (PointedCone.hull ℝ generators).zero_mem,
          generator, generatorMembership.2, by simp⟩
  | zero =>
      exact ⟨0, (PointedCone.hull ℝ generators).zero_mem, 0, face.zero_mem, by simp⟩
  | add first second _ _ firstDifference secondDifference =>
      obtain ⟨firstCone, firstConeMembership, firstFace, firstFaceMembership, rfl⟩ :=
        firstDifference
      obtain ⟨secondCone, secondConeMembership, secondFace, secondFaceMembership, rfl⟩ :=
        secondDifference
      exact ⟨firstCone + secondCone,
        (PointedCone.hull ℝ generators).add_mem firstConeMembership secondConeMembership,
        firstFace + secondFace, face.add_mem firstFaceMembership secondFaceMembership,
        by abel⟩
  | smul scalar vector _ difference =>
      obtain ⟨coneVector, coneMembership, faceVector, faceMembership, rfl⟩ := difference
      exact ⟨(scalar : ℝ) • coneVector,
        (PointedCone.hull ℝ generators).smul_mem scalar.2 coneMembership,
        (scalar : ℝ) • faceVector, face.smul_mem scalar.2 faceMembership,
        by
          change (scalar : ℝ) • (coneVector - faceVector) = _
          exact smul_sub (scalar : ℝ) coneVector faceVector⟩

theorem neg_not_mem_hull_union_neg_face_generators {generators : Set Space}
    {face : PointedCone ℝ Space} (isFace : face.IsFaceOf (PointedCone.hull ℝ generators))
    {vector : Space} (coneMembership : vector ∈ PointedCone.hull ℝ generators)
    (outsideFace : vector ∉ face) :
    -vector ∉ PointedCone.hull ℝ
      (generators ∪ (fun generator => -generator) '' (generators ∩ (face : Set Space))) := by
  intro membership
  obtain ⟨coneVector, coneVectorMembership, faceVector, faceVectorMembership, equality⟩ :=
    mem_hull_union_neg_face_generators membership
  have sumEquality : vector + coneVector = faceVector := by
    have rearranged := congrArg (fun target => vector + target + faceVector) equality
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using rearranged.symm
  exact outsideFace (isFace.mem_of_add_mem_left coneMembership coneVectorMembership
    (sumEquality.symm ▸ faceVectorMembership))

theorem eq_zero_on_face_of_generators {generators : Set Space} (finite : generators.Finite)
    {face : PointedCone ℝ Space} (isFace : face.IsFaceOf (PointedCone.hull ℝ generators))
    (functional : Space →ₗ[ℝ] ℝ)
    (vanishes : ∀ generator ∈ generators, generator ∈ face → functional generator = 0) :
    ∀ vector ∈ face, functional vector = 0 := by
  intro vector membership
  rw [face_eq_hull_inter finite isFace] at membership
  induction membership using Submodule.span_induction with
  | mem vector membership => exact vanishes vector membership.1 membership.2
  | zero => exact map_zero functional
  | add first second _ _ firstZero secondZero =>
      simp [map_add, firstZero, secondZero]
  | smul scalar vector _ vectorZero =>
      simp [vectorZero]

theorem mem_face_of_eq_zero_of_generator_signs {generators : Set Space}
    (finite : generators.Finite) {face : PointedCone ℝ Space}
    (_isFace : face.IsFaceOf (PointedCone.hull ℝ generators))
    (functional : Space →ₗ[ℝ] ℝ)
    (nonnegative : ∀ generator ∈ generators, 0 ≤ functional generator)
    (positive : ∀ generator ∈ generators, generator ∉ face → 0 < functional generator)
    {vector : Space} (coneMembership : vector ∈ PointedCone.hull ℝ generators)
    (zero : functional vector = 0) : vector ∈ face := by
  classical
  let : Fintype generators := finite.fintype
  rw [← SetLike.mem_coe, hull_eq_nonnegative_combinations] at coneMembership
  obtain ⟨coefficients, coefficientsNonnegative, equality⟩ := coneMembership
  have sumZero : ∑ generator : generators,
      coefficients generator * functional (generator : Space) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, zero] using congrArg functional equality
  have termZero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun generator (_ : generator ∈ Finset.univ) =>
      mul_nonneg (coefficientsNonnegative generator) (nonnegative generator generator.2))).mp
        sumZero
  rw [← equality]
  apply face.sum_mem
  intro generator _
  by_cases faceMembership : (generator : Space) ∈ face
  · exact face.smul_mem (coefficientsNonnegative generator) faceMembership
  · have coefficientZero : coefficients generator = 0 :=
      (mul_eq_zero.mp (termZero generator (Finset.mem_univ generator))).resolve_right
        (positive generator generator.2 faceMembership).ne'
    simp [coefficientZero]

end Algebraic

section Normed

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem exists_separator_of_not_mem_face {generators : Set Space}
    (finite : generators.Finite) {face : PointedCone ℝ Space}
    (isFace : face.IsFaceOf (PointedCone.hull ℝ generators)) {vector : Space}
    (coneMembership : vector ∈ PointedCone.hull ℝ generators) (outsideFace : vector ∉ face) :
    ∃ functional : Space →L[ℝ] ℝ,
      (∀ target ∈ PointedCone.hull ℝ generators, 0 ≤ functional target) ∧
      (∀ target ∈ face, functional target = 0) ∧ 0 < functional vector := by
  let enlargedGenerators :=
    generators ∪ (fun generator => -generator) '' (generators ∩ (face : Set Space))
  have enlargedFinite : enlargedGenerators.Finite :=
    finite.union ((finite.inter_of_left _).image (fun generator => -generator))
  let enlarged : ProperCone ℝ Space :=
    ⟨PointedCone.hull ℝ enlargedGenerators, hull_isClosed_of_finite enlargedFinite⟩
  have coneLe : PointedCone.hull ℝ generators ≤ enlarged.toSubmodule :=
    Submodule.span_mono Set.subset_union_left
  have negativeOutside : -vector ∉ enlarged :=
    neg_not_mem_hull_union_neg_face_generators isFace coneMembership outsideFace
  obtain ⟨functional, nonnegative, negative⟩ :=
    enlarged.hyperplane_separation_point negativeOutside
  have nonnegativeOnCone : ∀ target ∈ PointedCone.hull ℝ generators,
      0 ≤ functional target := fun target membership => nonnegative target (coneLe membership)
  refine ⟨functional, nonnegativeOnCone, ?_, ?_⟩
  · apply eq_zero_on_face_of_generators finite isFace functional.toLinearMap
    intro generator generatorMembership faceMembership
    have positiveSign := nonnegativeOnCone generator (PointedCone.subset_hull generatorMembership)
    have negativeMembership : -generator ∈ enlarged :=
      PointedCone.subset_hull (Set.mem_union_right _
        ⟨generator, ⟨generatorMembership, faceMembership⟩, rfl⟩)
    have negativeSign := nonnegative (-generator) negativeMembership
    rw [map_neg] at negativeSign
    change functional generator = 0
    linarith
  · rw [map_neg] at negative
    linarith

theorem exists_nonnegative_continuous_functional_exposing_face {generators : Set Space}
    (finite : generators.Finite) {face : PointedCone ℝ Space}
    (isFace : face.IsFaceOf (PointedCone.hull ℝ generators)) :
    ∃ functional : Space →L[ℝ] ℝ,
      (∀ vector ∈ PointedCone.hull ℝ generators, 0 ≤ functional vector) ∧
      (∀ vector ∈ PointedCone.hull ℝ generators,
        functional vector = 0 ↔ vector ∈ face) := by
  classical
  let : Fintype generators := finite.fintype
  have separators : ∀ generator : generators, ∃ functional : Space →L[ℝ] ℝ,
      (∀ vector ∈ PointedCone.hull ℝ generators, 0 ≤ functional vector) ∧
      (∀ vector ∈ face, functional vector = 0) ∧
      ((generator : Space) ∉ face → 0 < functional generator) := by
    intro generator
    by_cases faceMembership : (generator : Space) ∈ face
    · exact ⟨0, by simp, by simp, fun outside => (outside faceMembership).elim⟩
    · obtain ⟨functional, nonnegative, vanishes, positive⟩ :=
        exists_separator_of_not_mem_face finite isFace
          (PointedCone.subset_hull generator.2) faceMembership
      exact ⟨functional, nonnegative, vanishes, fun _ => positive⟩
  choose separators nonnegative vanishes positive using separators
  let functional : Space →L[ℝ] ℝ := ∑ generator : generators, separators generator
  have functionalNonnegative : ∀ vector ∈ PointedCone.hull ℝ generators,
      0 ≤ functional vector := by
    intro vector membership
    simp only [functional, sum_apply]
    exact Finset.sum_nonneg fun generator _ => nonnegative generator vector membership
  have functionalVanishes : ∀ vector ∈ face, functional vector = 0 := by
    intro vector membership
    simp only [functional, sum_apply]
    exact Finset.sum_eq_zero fun generator _ => vanishes generator vector membership
  have functionalPositive : ∀ generator ∈ generators,
      generator ∉ face → 0 < functional generator := by
    intro generator membership outsideFace
    let distinguished : generators := ⟨generator, membership⟩
    have bound : separators distinguished generator ≤ functional generator := by
      simp only [functional, sum_apply]
      exact Finset.single_le_sum
        (fun index _ => nonnegative index generator (PointedCone.subset_hull membership))
        (Finset.mem_univ distinguished)
    exact lt_of_lt_of_le (positive distinguished outsideFace) bound
  refine ⟨functional, functionalNonnegative, ?_⟩
  intro vector membership
  constructor
  · exact mem_face_of_eq_zero_of_generator_signs finite isFace functional.toLinearMap
      (fun generator generatorMembership => functionalNonnegative generator
        (PointedCone.subset_hull generatorMembership)) functionalPositive membership
  · exact functionalVanishes vector

theorem exists_nonnegative_linear_functional_exposing_face {generators : Set Space}
    (finite : generators.Finite) {face : PointedCone ℝ Space}
    (isFace : face.IsFaceOf (PointedCone.hull ℝ generators)) :
    ∃ functional : Space →ₗ[ℝ] ℝ,
      (∀ vector ∈ PointedCone.hull ℝ generators, 0 ≤ functional vector) ∧
      {vector | vector ∈ PointedCone.hull ℝ generators ∧ functional vector = 0} =
        (face : Set Space) := by
  obtain ⟨functional, nonnegative, zeroIff⟩ :=
    exists_nonnegative_continuous_functional_exposing_face finite isFace
  refine ⟨functional.toLinearMap, nonnegative, ?_⟩
  ext vector
  constructor
  · rintro ⟨membership, zero⟩
    exact (zeroIff vector membership).mp zero
  · intro membership
    exact ⟨isFace.le membership, (zeroIff vector (isFace.le membership)).mpr membership⟩

end Normed

section Coordinates

variable {Domain Coordinates : Type*} [AddCommGroup Domain] [Module ℝ Domain]
  [NormedAddCommGroup Coordinates] [NormedSpace ℝ Coordinates]

theorem exists_nonnegative_linear_functional_exposing_face_of_linearEquiv
    (coordinates : Domain ≃ₗ[ℝ] Coordinates)
    {generators : Set Domain} (finite : generators.Finite)
    {face : PointedCone ℝ Domain}
    (isFace : face.IsFaceOf (PointedCone.hull ℝ generators)) :
    ∃ functional : Domain →ₗ[ℝ] ℝ,
      (∀ vector ∈ PointedCone.hull ℝ generators, 0 ≤ functional vector) ∧
      {vector | vector ∈ PointedCone.hull ℝ generators ∧ functional vector = 0} =
        (face : Set Domain) := by
  have mappedHull : (PointedCone.hull ℝ generators).map coordinates.toLinearMap =
      PointedCone.hull ℝ (coordinates '' generators) := by
    exact Submodule.map_span (coordinates.toLinearMap : Domain →ₗ[Nonneg ℝ] Coordinates)
      generators
  have mappedFace := isFace.map_equiv coordinates
  rw [mappedHull] at mappedFace
  obtain ⟨coordinateFunctional, nonnegative, zeroLocus⟩ :=
    exists_nonnegative_linear_functional_exposing_face (finite.image coordinates) mappedFace
  let functional := coordinateFunctional.comp coordinates.toLinearMap
  have mappedMembership : ∀ vector ∈ PointedCone.hull ℝ generators,
      coordinates vector ∈ PointedCone.hull ℝ (coordinates '' generators) := by
    intro vector membership
    rw [← mappedHull]
    exact PointedCone.mem_map.mpr ⟨vector, membership, rfl⟩
  refine ⟨functional, fun vector membership =>
    nonnegative (coordinates vector) (mappedMembership vector membership), ?_⟩
  ext vector
  constructor
  · rintro ⟨membership, zero⟩
    have zeroMembership : coordinates vector ∈
        {target | target ∈ PointedCone.hull ℝ (coordinates '' generators) ∧
          coordinateFunctional target = 0} := ⟨mappedMembership vector membership, zero⟩
    rw [zeroLocus] at zeroMembership
    obtain ⟨preimage, preimageMembership, equality⟩ := PointedCone.mem_map.mp zeroMembership
    exact coordinates.injective equality ▸ preimageMembership
  · intro membership
    have faceMembership : coordinates vector ∈ face.map coordinates.toLinearMap :=
      PointedCone.mem_map.mpr ⟨vector, membership, rfl⟩
    change coordinates vector ∈ (face.map coordinates.toLinearMap : Set Coordinates)
      at faceMembership
    rw [← zeroLocus] at faceMembership
    exact ⟨isFace.le membership, faceMembership.2⟩

theorem exists_nonnegative_linear_functional_exposing_ray_of_linearEquiv
    (coordinates : Domain ≃ₗ[ℝ] Coordinates)
    {generators : Set Domain} (finite : generators.Finite) {rayGenerator : Domain}
    (isFace : (PointedCone.hull ℝ {rayGenerator}).IsFaceOf
      (PointedCone.hull ℝ generators)) :
    ∃ functional : Domain →ₗ[ℝ] ℝ,
      (∀ vector ∈ PointedCone.hull ℝ generators, 0 ≤ functional vector) ∧
      functional rayGenerator = 0 ∧
      {vector | vector ∈ PointedCone.hull ℝ generators ∧ functional vector = 0} =
        (PointedCone.hull ℝ {rayGenerator} : Set Domain) := by
  obtain ⟨functional, nonnegative, equality⟩ :=
    exists_nonnegative_linear_functional_exposing_face_of_linearEquiv coordinates finite isFace
  have membership : rayGenerator ∈ PointedCone.hull ℝ {rayGenerator} :=
    PointedCone.subset_hull (Set.mem_singleton rayGenerator)
  refine ⟨functional, nonnegative, ?_, equality⟩
  have zeroMembership : rayGenerator ∈
      {vector | vector ∈ PointedCone.hull ℝ generators ∧ functional vector = 0} := by
    rw [equality]
    exact membership
  exact zeroMembership.2

end Coordinates

end BondalThomsen.FiniteConeExposedFaces
