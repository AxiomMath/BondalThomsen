module

public import BondalThomsen.ProjectiveBundle.Fan

@[expose] public section

namespace BondalThomsen.ProjectiveBundle

open Finset Set Module

variable {rows baseDimension columns : ℕ}

noncomputable def coordinateEquivFin (rows baseDimension columns : ℕ) :
    Coordinate rows baseDimension columns ≃ Fin (rows * baseDimension + columns) :=
  Fintype.equivOfCardEq (by simp [Coordinate])

noncomputable def coneFinBasis (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    Basis (Fin (rows * baseDimension + columns)) ℤ (Lattice rows baseDimension columns) :=
  (coneBasis matrix choice).reindex (coordinateEquivFin rows baseDimension columns)

theorem coneFinBasis_hull_eq (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    PointedCone.hull ℝ (Set.range (fun index => latticeEmbedding rows baseDimension columns
      (coneFinBasis matrix choice index))) = maximalCone matrix choice := by
  rw [maximalCone_eq_basisHull]
  apply congrArg (PointedCone.hull ℝ)
  ext vector
  constructor
  · rintro ⟨index, rfl⟩
    refine ⟨(coordinateEquivFin rows baseDimension columns).symm index, ?_⟩
    simp [coneFinBasis, Basis.reindex_apply]
  · rintro ⟨coordinate, rfl⟩
    refine ⟨coordinateEquivFin rows baseDimension columns coordinate, ?_⟩
    simp [coneFinBasis, Basis.reindex_apply]

theorem coneFinBasis_isConeBasis (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    (fan matrix).IsConeBasis (coneFinBasis matrix choice) := by
  change PointedCone.hull ℝ _ ∈ (fan matrix).cones
  rw [coneFinBasis_hull_eq]
  exact maximalCone_mem_fan matrix choice

def containingChoice (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (label : RayLabel rows baseDimension columns) : ConeChoice rows baseDimension columns :=
  match label with
  | .inl (factor, none) =>
      ⟨fun other => if other = factor then some ⟨0, base_positive⟩ else none, none⟩
  | .inl (_, some _) => referenceChoice rows baseDimension columns
  | .inr none => ⟨fun _ => none, some ⟨0, fiber_positive⟩⟩
  | .inr (some _) => referenceChoice rows baseDimension columns

theorem containingChoice_allowed (base_positive : 0 < baseDimension)
    (fiber_positive : 0 < columns) (label : RayLabel rows baseDimension columns) :
    RayAllowed (containingChoice base_positive fiber_positive label) label := by
  cases label with
  | inl label => rcases label with ⟨factor, position⟩; cases position <;>
      simp [containingChoice, RayAllowed, referenceChoice]
  | inr label => cases label <;> simp [containingChoice, RayAllowed, referenceChoice]

theorem rayVector_hull_mem_fan (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (label : RayLabel rows baseDimension columns) :
    PointedCone.hull ℝ {latticeEmbedding rows baseDimension columns (rayVector matrix label)} ∈
      (fan matrix).cones := by
  let choice := containingChoice base_positive fiber_positive label
  have integral_member : rayVector matrix label ∈ Set.range (coneBasis matrix choice) := by
    rw [← allowedRayVectors_eq_basis]
    exact ⟨label, containingChoice_allowed base_positive fiber_positive label, rfl⟩
  obtain ⟨coordinate, equality⟩ := integral_member
  have face := PointedCone.isFaceOf_hull_image
    (realConeBasis matrix choice).linearIndependent rfl {coordinate}
  simp only [Set.image_singleton, realConeBasis_apply, equality] at face
  rw [← maximalCone_eq_realBasisHull] at face
  exact (fan matrix).mem_of_isFaceOf (maximalCone_mem_fan matrix choice) face

def labelRay (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (label : RayLabel rows baseDimension columns) :
    (fan (baseDimension := baseDimension) matrix).Ray :=
  ⟨rayVector matrix label, rayVector_isPrimitive matrix base_positive fiber_positive label,
    rayVector_hull_mem_fan matrix base_positive fiber_positive label⟩

@[simp] theorem labelRay_val (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (label : RayLabel rows baseDimension columns) :
    (labelRay matrix base_positive fiber_positive label).val = rayVector matrix label := rfl

theorem ray_eq_rayVector (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (ray : (fan (baseDimension := baseDimension) matrix).Ray) :
    ∃ label, ray.val = rayVector matrix label := by
  obtain ⟨choice, ray_face⟩ := ray.property.2
  have ray_face_basis := ray_face
  rw [maximalCone_eq_basisHull] at ray_face_basis
  have salient := (maximalCone_isToricCone matrix choice).salient
  rw [maximalCone_eq_basisHull] at salient
  obtain ⟨coordinate, equality⟩ := TauCeti.Toric.primitive_eq_basis_of_ray_face
    (latticeEmbedding_isIntegralLattice rows baseDimension columns) (coneBasis matrix choice)
    ray.val ray.property.1 ray_face_basis salient
  have basis_member : coneBasis matrix choice coordinate ∈
      rayVector matrix '' {label | RayAllowed choice label} := by
    rw [allowedRayVectors_eq_basis]
    exact ⟨coordinate, rfl⟩
  obtain ⟨label, _, vector_equality⟩ := basis_member
  exact ⟨label, equality.trans vector_equality.symm⟩

theorem baseRay_injective (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) :
    Function.Injective (fun label : Fin rows × Option (Fin baseDimension) =>
      rayVector matrix (.inl label)) := by
  intro first second equality
  rcases first with ⟨first_factor, first_position⟩
  rcases second with ⟨second_factor, second_position⟩
  cases first_position with
  | none =>
    cases second_position with
    | none =>
      have same_factor : first_factor = second_factor := by
        by_contra distinct
        have coordinate_equality := congrFun equality (.inl (first_factor, ⟨0, base_positive⟩))
        simp [rayVector, baseNegative, distinct] at coordinate_equality
      subst second_factor
      rfl
    | some position =>
      have coordinate_equality := congrFun equality (.inl (second_factor, position))
      by_cases same_factor : second_factor = first_factor <;>
        simp [rayVector, baseNegative, basePositive, same_factor] at coordinate_equality
  | some position =>
    cases second_position with
    | none =>
      have coordinate_equality := congrFun equality (.inl (first_factor, position))
      by_cases same_factor : first_factor = second_factor <;>
        simp [rayVector, baseNegative, basePositive, same_factor] at coordinate_equality
    | some other_position =>
      have basis_equality :
          standardBasis rows baseDimension columns (.inl (first_factor, position)) =
          standardBasis rows baseDimension columns (.inl (second_factor, other_position)) := by
        simpa only [standardBasis, Pi.basisFun_apply, rayVector, Sum.elim_inl,
          Option.elim_some, basePositive] using equality
      have coordinate_equality := (standardBasis rows baseDimension columns).injective basis_equality
      have pair_equality := Sum.inl.inj coordinate_equality
      exact congrArg (fun pair : Fin rows × Fin baseDimension => (pair.1, some pair.2)) pair_equality

theorem fiberRay_injective (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    :
    Function.Injective (fun label : Option (Fin columns) =>
      (rayVector matrix (.inr label) : Lattice rows baseDimension columns)) := by
  intro first second equality
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some column =>
      have coordinate_equality := congrFun equality (.inr column)
      simp [rayVector, fiberNegative, fiberPositive] at coordinate_equality
  | some column =>
    cases second with
    | none =>
      have coordinate_equality := congrFun equality (.inr column)
      simp [rayVector, fiberNegative, fiberPositive] at coordinate_equality
    | some other_column =>
      have basis_equality : standardBasis rows baseDimension columns (.inr column) =
          standardBasis rows baseDimension columns (.inr other_column) := by
        simpa only [standardBasis, Pi.basisFun_apply, rayVector, Sum.elim_inr,
          Option.elim_some, fiberPositive] using equality
      have coordinate_equality := (standardBasis rows baseDimension columns).injective basis_equality
      exact congrArg some (Sum.inr.inj coordinate_equality)

theorem baseRay_ne_fiberRay (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension)
    (base_label : Fin rows × Option (Fin baseDimension)) (fiber_label : Option (Fin columns)) :
    rayVector matrix (.inl base_label) ≠ rayVector matrix (.inr fiber_label) := by
  intro equality
  rcases base_label with ⟨factor, position⟩
  cases position with
  | none =>
    have coordinate_equality := congrFun equality (.inl (factor, ⟨0, base_positive⟩))
    cases fiber_label <;>
      simp [rayVector, baseNegative, fiberPositive, fiberNegative] at coordinate_equality
  | some position =>
    have coordinate_equality := congrFun equality (.inl (factor, position))
    cases fiber_label <;>
      simp [rayVector, basePositive, fiberPositive, fiberNegative] at coordinate_equality

theorem rayVector_injective (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (_fiber_positive : 0 < columns) :
    Function.Injective (rayVector (baseDimension := baseDimension) matrix) := by
  intro first second equality
  cases first with
  | inl first =>
    cases second with
    | inl second => exact congrArg Sum.inl (baseRay_injective matrix base_positive equality)
    | inr second => exact False.elim (baseRay_ne_fiberRay matrix base_positive first second equality)
  | inr first =>
    cases second with
    | inl second => exact False.elim (baseRay_ne_fiberRay matrix base_positive second first equality.symm)
    | inr second => exact congrArg Sum.inr (fiberRay_injective matrix equality)

theorem labelRay_bijective (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns) :
    Function.Bijective (labelRay matrix base_positive fiber_positive) := by
  constructor
  · intro first second equality
    exact rayVector_injective matrix base_positive fiber_positive (congrArg Subtype.val equality)
  · intro ray
    obtain ⟨label, equality⟩ := ray_eq_rayVector matrix ray
    exact ⟨label, Subtype.ext equality.symm⟩

noncomputable def rayEquiv (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns) :
    RayLabel rows baseDimension columns ≃ (fan (baseDimension := baseDimension) matrix).Ray :=
  Equiv.ofBijective (labelRay matrix base_positive fiber_positive)
    (labelRay_bijective matrix base_positive fiber_positive)

end BondalThomsen.ProjectiveBundle
