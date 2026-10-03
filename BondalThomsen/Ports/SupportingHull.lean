module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Combination

@[expose] public section

namespace BondalThomsen

variable {Ambient : Type*} [AddCommGroup Ambient] [Module ℝ Ambient]

theorem convexHull_inter_affine_zero_of_nonneg (points : Finset Ambient)
    (functional : Ambient →ᵃ[ℝ] ℝ) (nonnegative : ∀ point ∈ points, 0 ≤ functional point) :
    convexHull ℝ (points : Set Ambient) ∩ {point | functional point = 0} =
      convexHull ℝ ((points.filter fun point => functional point = 0 :
        Finset Ambient) : Set Ambient) := by
  classical
  apply Set.Subset.antisymm
  · rintro point ⟨in_hull, on_hyperplane⟩
    obtain ⟨weights, weights_nonnegative, weights_sum, center⟩ :=
      Finset.mem_convexHull.mp in_hull
    have functional_sum : ∑ vertex ∈ points, weights vertex * functional vertex = 0 := by
      calc
        ∑ vertex ∈ points, weights vertex * functional vertex =
            points.affineCombination ℝ functional weights := by
          simpa only [smul_eq_mul] using
            (Finset.affineCombination_eq_linear_combination points functional weights
              weights_sum).symm
        _ = functional (points.affineCombination ℝ id weights) :=
          (points.map_affineCombination id weights weights_sum functional).symm
        _ = functional (points.centerMass weights id) := by
          congr 1
          rw [Finset.affineCombination_eq_linear_combination points id weights weights_sum,
            Finset.centerMass_eq_of_sum_1 points id weights_sum]
        _ = functional point := by rw [center]
        _ = 0 := on_hyperplane
    have terms_zero : ∀ vertex ∈ points, weights vertex * functional vertex = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun vertex member =>
        mul_nonneg (weights_nonnegative vertex member) (nonnegative vertex member)).mp
          functional_sum
    have weights_zero : ∀ vertex ∈ points, functional vertex ≠ 0 → weights vertex = 0 := by
      intro vertex member nonzero
      exact (mul_eq_zero.mp (terms_zero vertex member)).resolve_right nonzero
    let face := points.filter fun vertex => functional vertex = 0
    have face_subset : face ⊆ points := Finset.filter_subset _ _
    have face_sum : ∑ vertex ∈ face, weights vertex = 1 := by
      calc
        ∑ vertex ∈ face, weights vertex = ∑ vertex ∈ points, weights vertex :=
          Finset.sum_subset face_subset fun vertex member outside =>
            weights_zero vertex member (by
              intro equality
              apply outside
              simp only [face, Finset.mem_filter, member, equality, and_self])
        _ = 1 := weights_sum
    apply Finset.mem_convexHull.mpr
    refine ⟨weights, fun vertex member => weights_nonnegative vertex (face_subset member),
      face_sum, ?_⟩
    have centers_equal : face.centerMass weights id = points.centerMass weights id := by
      rw [Finset.centerMass_eq_of_sum_1 face id face_sum,
        Finset.centerMass_eq_of_sum_1 points id weights_sum]
      exact Finset.sum_subset face_subset fun vertex member outside => by
        rw [weights_zero vertex member (by
          intro equality
          apply outside
          simp only [face, Finset.mem_filter, member, equality, and_self]), zero_smul]
    exact centers_equal.trans center
  · apply convexHull_min
    · intro point member
      exact ⟨subset_convexHull ℝ (points : Set Ambient) (Finset.mem_filter.mp member).1,
        (Finset.mem_filter.mp member).2⟩
    · exact (convex_convexHull ℝ (points : Set Ambient)).inter
        ((convex_singleton (0 : ℝ)).affine_preimage functional)

theorem convexHull_inter_affine_zero_of_nonneg_set (points : Set Ambient)
    (functional : Ambient →ᵃ[ℝ] ℝ) (nonnegative : ∀ point ∈ points, 0 ≤ functional point) :
    convexHull ℝ points ∩ {point | functional point = 0} =
      convexHull ℝ (points ∩ {point | functional point = 0}) := by
  classical
  apply Set.Subset.antisymm
  · rintro point ⟨in_hull, on_hyperplane⟩
    obtain ⟨Index, _, weights, vertices, weights_nonnegative, weights_sum,
      vertices_mem, combination⟩ := mem_convexHull_iff_exists_fintype.mp in_hull
    let finite_points : Finset Ambient := Finset.univ.image vertices
    have in_finite_hull : point ∈ convexHull ℝ (finite_points : Set Ambient) := by
      exact mem_convexHull_of_exists_fintype weights vertices weights_nonnegative weights_sum
        (fun index => Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩))
        (by simp only [combination])
    have finite_nonnegative : ∀ vertex ∈ finite_points, 0 ≤ functional vertex := by
      intro vertex member
      obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp member
      exact nonnegative (vertices index) (vertices_mem index)
    have in_face : point ∈ convexHull ℝ ((finite_points.filter
        fun vertex => functional vertex = 0 : Finset Ambient) : Set Ambient) := by
      rw [← convexHull_inter_affine_zero_of_nonneg finite_points functional finite_nonnegative]
      exact ⟨in_finite_hull, on_hyperplane⟩
    apply convexHull_mono ?_ in_face
    intro vertex member
    have in_filter := Finset.mem_filter.mp member
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp in_filter.1
    exact ⟨vertices_mem index, in_filter.2⟩
  · apply convexHull_min
    · intro point member
      exact ⟨subset_convexHull ℝ points member.1, member.2⟩
    · exact (convex_convexHull ℝ points).inter
        ((convex_singleton (0 : ℝ)).affine_preimage functional)

end BondalThomsen
