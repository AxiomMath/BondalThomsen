module

public import BondalThomsen.Fan.StarFan
public import BondalThomsen.Fan.Completeness

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Set Module Filter
open scoped Topology

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem eventually_cones_containing_nearby_point_contain
    (fan : Fan embedding) (point : Ambient) :
    ∀ᶠ nearby in 𝓝 point, ∀ cone ∈ fan.cones, nearby ∈ cone → point ∈ cone := by
  have nearby_containment := (locallyFinite_of_finite
    (fun cone : fan.cones => (cone.val : Set Ambient))).eventually_subset
      (fun cone => fan.cone_isClosed cone.val cone.property) point
  filter_upwards [nearby_containment] with nearby contains cone member nearby_member
  exact contains (show (⟨cone, member⟩ : fan.cones) ∈
    {cone : fan.cones | nearby ∈ cone.val} from nearby_member)

theorem exists_cone_containing_point_perturbation (fan : Fan embedding)
    (complete : fan.IsComplete) (point direction : Ambient) :
    ∃ scalar : ℝ, 0 < scalar ∧ ∃ cone ∈ fan.cones,
      point ∈ cone ∧ point + scalar • direction ∈ cone := by
  let perturbation := fun scalar : ℝ => point + scalar • direction
  have continuous_perturbation : Continuous perturbation :=
    continuous_const.add (continuous_id.smul continuous_const)
  have converges : Tendsto perturbation (𝓝 0) (𝓝 point) := by
    simpa only [perturbation, zero_smul, add_zero] using continuous_perturbation.tendsto 0
  obtain ⟨scalar, positive, local_member⟩ :=
    (converges.eventually (fan.eventually_cones_containing_nearby_point_contain point)).exists_gt
  obtain ⟨cone, member, contains⟩ := fan.isComplete_iff.mp complete (perturbation scalar)
  exact ⟨scalar, positive, cone, member, local_member cone member contains, contains⟩

theorem starCones_cover_of_isComplete (fan : Fan embedding)
    (complete : fan.IsComplete) (ray : fan.Ray) (point : fan.StarAmbient ray) :
    ∃ cone ∈ fan.starCones ray, point ∈ cone := by
  obtain ⟨lifted, lifted_eq⟩ := (Submodule.span ℝ {embedding ray.val}).mkQ_surjective point
  obtain ⟨scalar, positive, cone, member, ray_member, perturbed_member⟩ :=
    fan.exists_cone_containing_point_perturbation complete (embedding ray.val) lifted
  refine ⟨PointedCone.map (fan.starProjection ray) cone,
    ⟨cone, ⟨member, ray_member⟩, rfl⟩, ?_⟩
  have projected : scalar • point ∈ PointedCone.map (fan.starProjection ray) cone := by
    apply PointedCone.mem_map.mpr
    refine ⟨embedding ray.val + scalar • lifted, perturbed_member, ?_⟩
    simp only [map_add, map_smul, fan.starProjection_ray, zero_add]
    change scalar • ((Submodule.span ℝ {embedding ray.val}).mkQ lifted) = scalar • point
    rw [lifted_eq]
  exact (PointedCone.smul_mem_iff _ positive).mp projected

theorem star_isComplete_of_isComplete (fan : Fan embedding)
    (complete : fan.IsComplete) (ray : fan.Ray) : (fan.star ray).IsComplete := by
  apply (fan.star ray).isComplete_iff.mpr
  intro point
  exact fan.starCones_cover_of_isComplete complete ray point

theorem star_cones_nonempty_of_isComplete (fan : Fan embedding)
    (complete : fan.IsComplete) (ray : fan.Ray) : Nonempty (fan.star ray).cones := by
  obtain ⟨cone, member, _⟩ :=
    (fan.star ray).isComplete_iff.mp (fan.star_isComplete_of_isComplete complete ray) 0
  exact ⟨⟨cone, member⟩⟩

end TauCeti.Toric.Fan
