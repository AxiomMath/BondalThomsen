module

public import BondalThomsen.Fan.Basic
public import BondalThomsen.Ports.SupportingHull
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Generation

@[expose] public section

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

namespace TauCeti.Toric.Fan

variable (fan : TauCeti.Toric.Fan embedding)

def rayGenerators : Set Ambient := Set.range (fun ray : fan.Ray => embedding ray.val)

def rayPolytope : Set Ambient := convexHull ℝ fan.rayGenerators

theorem rayGenerators_finite : fan.rayGenerators.Finite := Set.finite_range _

noncomputable def coneRay (cone : PointedCone ℝ Ambient) (member : cone ∈ fan.cones)
    (ray : TauCeti.Toric.ToricRay cone) : fan.Ray := by
  let toric := fan.isToricCone member
  let generator := TauCeti.Toric.primitiveGenerator fan.lattice toric ray
  refine ⟨generator, TauCeti.Toric.primitiveGenerator_isPrimitive fan.lattice toric ray, ?_⟩
  have ray_member : ray.toPointedCone ∈ fan.cones :=
    fan.mem_of_isFaceOf member ray.1.isFaceOf
  have generator_nonzero : embedding generator ≠ 0 := by
    simpa only [map_zero] using fan.lattice.injective.ne
      (TauCeti.Toric.primitiveGenerator_ne_zero fan.lattice toric ray)
  have ray_hull := ray.eq_hull_singleton
    (toric.salient.anti ray.1.isFaceOf.le)
    (TauCeti.Toric.primitiveGenerator_mem fan.lattice toric ray) generator_nonzero
  exact ray_hull ▸ ray_member

theorem cone_le_hull_rayGenerators (cone : PointedCone ℝ Ambient)
    (member : cone ∈ fan.cones) : cone ≤ PointedCone.hull ℝ fan.rayGenerators := by
  rw [← (fan.isToricCone member).hull_primitiveGenerator fan.lattice]
  apply Submodule.span_mono
  rintro point ⟨vector, ⟨ray, rfl⟩, rfl⟩
  exact ⟨fan.coneRay cone member ray, rfl⟩

theorem hull_rayGenerators_eq_top (complete : fan.IsComplete) :
    PointedCone.hull ℝ fan.rayGenerators = ⊤ := by
  apply top_unique
  intro point _
  obtain ⟨cone, member, point_in_cone⟩ := fan.isComplete_iff.mp complete point
  exact fan.cone_le_hull_rayGenerators cone member point_in_cone

include fan in

theorem basisGenerators_affineIndependent {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    AffineIndependent ℝ (fun index => embedding (basis index)) := by
  apply LinearIndependent.affineIndependent ℝ
  convert (fan.lattice.isBaseChange.basis basis).linearIndependent using 1
  funext index
  exact (fan.lattice.isBaseChange.basis_apply basis index).symm

theorem basisGenerators_subset_rayGenerators {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    Set.range (fun index => embedding (basis index)) ⊆ fan.rayGenerators := by
  rintro point ⟨index, rfl⟩
  exact ⟨fan.basisRay basis cone_basis index, rfl⟩

theorem supportingGenerators_eq {dimension : ℕ} (deep : fan.IsDeep dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    fan.rayGenerators ∩ {point | fan.supportingFunctional basis point = 1} =
      Set.range (fun index => embedding (basis index)) := by
  ext point
  constructor
  · rintro ⟨⟨ray, rfl⟩, on_hyperplane⟩
    obtain ⟨index, equality⟩ :=
      (fan.supportingFunctional_ray_eq_one_iff deep basis cone_basis ray).mp on_hyperplane
    exact ⟨index, congrArg embedding equality.symm⟩
  · rintro ⟨index, rfl⟩
    exact ⟨fan.basisGenerators_subset_rayGenerators basis cone_basis ⟨index, rfl⟩,
      fan.supportingFunctional_basis basis index⟩

theorem rayPolytope_supporting_le_one {dimension : ℕ} (deep : fan.IsDeep dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    fan.rayPolytope ⊆ {point | fan.supportingFunctional basis point ≤ 1} := by
  apply convexHull_min
  · rintro point ⟨ray, rfl⟩
    exact fan.supportingFunctional_ray_le_one deep basis cone_basis ray
  · exact convex_halfSpace_le
      ⟨(fan.supportingFunctional basis).map_add, (fan.supportingFunctional basis).map_smul⟩ 1

theorem rayPolytope_inter_supportingHyperplane {dimension : ℕ}
    (deep : fan.IsDeep dimension) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    fan.rayPolytope ∩ {point | fan.supportingFunctional basis point = 1} =
      convexHull ℝ (Set.range (fun index => embedding (basis index))) := by
  let gap : Ambient →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ Ambient 1 - (fan.supportingFunctional basis).toAffineMap
  have nonnegative : ∀ point ∈ fan.rayGenerators, 0 ≤ gap point := by
    rintro point ⟨ray, rfl⟩
    change 0 ≤ 1 - fan.supportingFunctional basis (embedding ray.val)
    exact sub_nonneg.mpr (fan.supportingFunctional_ray_le_one deep basis cone_basis ray)
  have zero_set : {point | gap point = 0} =
      {point | fan.supportingFunctional basis point = 1} := by
    ext point
    change 1 - fan.supportingFunctional basis point = 0 ↔
      fan.supportingFunctional basis point = 1
    exact sub_eq_zero.trans eq_comm
  have supporting := convexHull_inter_affine_zero_of_nonneg_set
    fan.rayGenerators gap nonnegative
  rw [zero_set, fan.supportingGenerators_eq deep basis cone_basis] at supporting
  exact supporting

end TauCeti.Toric.Fan
