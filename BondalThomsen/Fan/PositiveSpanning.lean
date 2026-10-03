module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

@[expose] public section

namespace BondalThomsen

variable {Ambient : Type*} [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]

theorem linearFunctional_eq_zero_of_positive_spanning (points : Set Ambient)
    (spanning : PointedCone.hull ℝ points = ⊤) (functional : Ambient →ₗ[ℝ] ℝ)
    (nonpositive : ∀ point ∈ points, functional point ≤ 0) : functional = 0 := by
  have everywhere_nonpositive : ∀ vector : Ambient, functional vector ≤ 0 := by
    intro vector
    have member : vector ∈ PointedCone.hull ℝ points := by rw [spanning]; trivial
    induction member using Submodule.span_induction with
    | mem vector member => exact nonpositive vector member
    | zero => simp
    | add first second _ _ first_nonpositive second_nonpositive =>
      rw [map_add]
      exact add_nonpos first_nonpositive second_nonpositive
    | smul coefficient vector _ vector_nonpositive =>
      change functional ((coefficient : ℝ) • vector) ≤ 0
      rw [map_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos coefficient.property vector_nonpositive
  ext vector
  change functional vector = 0
  have negative := everywhere_nonpositive (-vector)
  rw [map_neg] at negative
  exact le_antisymm (everywhere_nonpositive vector) (by linarith)

theorem zero_mem_convexHull_of_positive_spanning (points : Set Ambient)
    (finite : points.Finite) (nonempty : points.Nonempty)
    (spanning : PointedCone.hull ℝ points = ⊤) : (0 : Ambient) ∈ convexHull ℝ points := by
  by_contra outside
  obtain ⟨functional, threshold, bounded, threshold_negative⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ points)
      (finite.isCompact_convexHull ℝ).isClosed outside
  have nonpositive : ∀ point ∈ points, functional point ≤ 0 := by
    intro point member
    have below := bounded point (subset_convexHull ℝ points member)
    simpa only [map_zero] using below.le.trans threshold_negative.le
  have zero := linearFunctional_eq_zero_of_positive_spanning points spanning
    functional.toLinearMap nonpositive
  obtain ⟨point, member⟩ := nonempty
  have below := bounded point (subset_convexHull ℝ points member)
  have value_zero : functional point = 0 := congrArg (fun map : Ambient →ₗ[ℝ] ℝ => map point) zero
  rw [value_zero] at below
  rw [map_zero] at threshold_negative
  linarith

theorem zero_mem_interior_convexHull_of_positive_spanning [FiniteDimensional ℝ Ambient]
    (points : Set Ambient) (finite : points.Finite) (nonempty : points.Nonempty)
    (spanning : PointedCone.hull ℝ points = ⊤) :
    (0 : Ambient) ∈ interior (convexHull ℝ points) := by
  have zero_mem := zero_mem_convexHull_of_positive_spanning points finite nonempty spanning
  have span_top : Submodule.span ℝ points = ⊤ := by
    apply top_unique
    intro vector _
    apply PointedCone.hull_le_span ℝ points
    rw [spanning]
    trivial
  have zero_affine : (0 : Ambient) ∈ affineSpan ℝ points :=
    (convexHull_subset_affineSpan points) zero_mem
  have affine_top : affineSpan ℝ points = ⊤ := by
    apply AffineSubspace.ext
    intro vector
    have equality := affineSpan_insert_zero (k := ℝ) points
    rw [affineSpan_insert_eq_affineSpan ℝ zero_affine, span_top] at equality
    have membership := Set.ext_iff.mp equality vector
    simpa using membership
  have interior_nonempty := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr affine_top
  by_contra outside
  obtain ⟨functional, nonzero, bounded⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point (convex_convexHull ℝ points)
      outside interior_nonempty
  have nonpositive : ∀ point ∈ points, functional point ≤ 0 := by
    intro point member
    simpa only [map_zero] using bounded point (subset_convexHull ℝ points member)
  have zero := linearFunctional_eq_zero_of_positive_spanning points spanning
    functional.toLinearMap nonpositive
  apply nonzero
  ext vector
  exact congrArg (fun map : Ambient →ₗ[ℝ] ℝ => map vector) zero

end BondalThomsen
