module

public import BondalThomsen.DeepFan.SupportCriterion
public import BondalThomsen.Fan.Interior
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Normed.Module.Dual

@[expose] public section

open Finset Set Module Classical
open scoped Topology

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

def anticanonicalPolytope (fan : TauCeti.Toric.Fan embedding) : Set (StrongDual ℝ Ambient) :=
  {functional | ∀ ray : fan.Ray, (-1 : ℝ) ≤ functional (embedding ray.val)}

theorem anticanonicalPolytope_lower_bound_convexHull
    (fan : TauCeti.Toric.Fan embedding) {functional : StrongDual ℝ Ambient}
    (member : functional ∈ fan.anticanonicalPolytope) :
    convexHull ℝ (insert (0 : Ambient) fan.rayGenerators) ⊆
      {point | (-1 : ℝ) ≤ functional point} := by
  apply convexHull_min
  · intro point contains
    rcases contains with zero | ⟨ray, rfl⟩
    · simp [zero]
    · exact member ray
  · exact convex_halfSpace_ge functional.toLinearMap.isLinear (-1)

section FiniteDimension

variable [FiniteDimensional ℝ Ambient]

theorem anticanonicalPolytope_isBounded (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) : Bornology.IsBounded fan.anticanonicalPolytope := by
  let primal := convexHull ℝ (insert (0 : Ambient) fan.rayGenerators)
  have zero_inside : (0 : Ambient) ∈ interior primal := by
    apply BondalThomsen.zero_mem_interior_convexHull_of_positive_spanning
      (insert (0 : Ambient) fan.rayGenerators) (fan.rayGenerators_finite.insert 0)
      (Set.insert_nonempty _ _)
    rw [PointedCone.hull, Submodule.span_insert_zero]
    exact fan.hull_rayGenerators_eq_top complete
  let neighborhood := interior primal ∩ Neg.neg ⁻¹' interior primal
  have neighborhood_open : IsOpen neighborhood :=
    isOpen_interior.inter (isOpen_interior.preimage continuous_neg)
  have zero_member : (0 : Ambient) ∈ neighborhood := by
    exact ⟨zero_inside, by simpa using zero_inside⟩
  have neighborhood_nhds : neighborhood ∈ 𝓝 (0 : Ambient) :=
    neighborhood_open.mem_nhds zero_member
  apply (NormedSpace.isBounded_polar_of_mem_nhds_zero ℝ neighborhood_nhds).subset
  intro functional member
  rw [StrongDual.mem_polar_iff]
  intro point point_member
  have lower := fan.anticanonicalPolytope_lower_bound_convexHull member
    (interior_subset point_member.1)
  have negative_lower := fan.anticanonicalPolytope_lower_bound_convexHull member
    (interior_subset point_member.2)
  change -1 ≤ functional point at lower
  change -1 ≤ functional (-point) at negative_lower
  rw [map_neg] at negative_lower
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

end FiniteDimension

end TauCeti.Toric.Fan
