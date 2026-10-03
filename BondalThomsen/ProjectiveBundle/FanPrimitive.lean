module

public import BondalThomsen.ProjectiveBundle.FanRays
public import BondalThomsen.DeepFan.PrimitiveRelations

@[expose] public section

namespace BondalThomsen.ProjectiveBundle

open Finset Set Module

variable {rows baseDimension columns : ℕ}

theorem labelRay_mem_maximalCone_iff (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (choice : ConeChoice rows baseDimension columns) (label : RayLabel rows baseDimension columns) :
    latticeEmbedding rows baseDimension columns
      (labelRay matrix base_positive fiber_positive label).val ∈ maximalCone matrix choice ↔
      RayAllowed choice label := by
  constructor
  · intro contains
    have ray_le : PointedCone.hull ℝ
        {latticeEmbedding rows baseDimension columns (rayVector matrix label)} ≤ maximalCone matrix choice :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr contains)
    have face := (fan matrix).isFaceOf_of_le (maximalCone_mem_fan matrix choice)
      (rayVector_hull_mem_fan matrix base_positive fiber_positive label) ray_le
    have salient := (maximalCone_isToricCone matrix choice).salient
    rw [maximalCone_eq_basisHull] at face salient
    obtain ⟨coordinate, equality⟩ := TauCeti.Toric.primitive_eq_basis_of_ray_face
      (latticeEmbedding_isIntegralLattice rows baseDimension columns) (coneBasis matrix choice)
      (rayVector matrix label) (rayVector_isPrimitive matrix base_positive fiber_positive label) face salient
    have basis_member : coneBasis matrix choice coordinate ∈
        rayVector matrix '' {label | RayAllowed choice label} := by
      rw [allowedRayVectors_eq_basis]
      exact ⟨coordinate, rfl⟩
    obtain ⟨other_label, allowed, other_equality⟩ := basis_member
    have same := rayVector_injective matrix base_positive fiber_positive (other_equality.trans equality.symm)
    exact same ▸ allowed
  · intro allowed
    exact PointedCone.subset_hull ⟨label, allowed, rfl⟩

end BondalThomsen.ProjectiveBundle
