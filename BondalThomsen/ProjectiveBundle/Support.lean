module

public import BondalThomsen.ProjectiveBundle.FanPrimitive
public import BondalThomsen.Fan.PrimitiveRelationDegree

@[expose] public section

namespace BondalThomsen.ProjectiveBundle

open Finset Set Module

variable {rows baseDimension columns : ℕ}

noncomputable def coneCharacter (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    Lattice rows baseDimension columns →ₗ[ℤ] ℤ :=
  (coneBasis matrix choice).sumCoords

theorem coneCharacter_allowed (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (label : RayLabel rows baseDimension columns)
    (allowed : RayAllowed choice label) : coneCharacter matrix choice (rayVector matrix label) = 1 := by
  have member : rayVector matrix label ∈ Set.range (coneBasis matrix choice) := by
    rw [← allowedRayVectors_eq_basis]
    exact ⟨label, allowed, rfl⟩
  obtain ⟨coordinate, equality⟩ := member
  rw [← equality]
  exact (coneBasis matrix choice).sumCoords_self_apply coordinate

theorem projective_block_sum {Index : Type*} [Fintype Index]
    (values : Option Index → ℤ) (omitted : Option Index)
    (others : ∀ label, label ≠ omitted → values label = 1) :
    ∑ label, values label = (Fintype.card Index : ℤ) + values omitted := by
  classical
  have sum_diff : (∑ label, (values label - 1)) = values omitted - 1 := by
    apply Finset.sum_eq_single omitted
    · intro label _ distinct
      rw [others label distinct, sub_self]
    · simp
  rw [Finset.sum_sub_distrib] at sum_diff
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_one] at sum_diff
  linarith

theorem coneCharacter_fiber_omitted (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    coneCharacter matrix choice (rayVector matrix (.inr choice.fiber)) = -(columns : ℤ) := by
  classical
  have total : (∑ label : Option (Fin columns),
      coneCharacter matrix choice (rayVector matrix (.inr label))) = 0 := by
    rw [Fintype.sum_option]
    have relation := congrArg (coneCharacter matrix choice)
      (fiber_ray_relation (rows := rows) (baseDimension := baseDimension) (columns := columns))
    simpa only [map_add, map_sum, map_zero, rayVector, Sum.elim_inr,
      Option.elim_none, Option.elim_some] using relation
  have block_sum := projective_block_sum
    (fun label : Option (Fin columns) => coneCharacter matrix choice (rayVector matrix (.inr label)))
    choice.fiber (fun label distinct => coneCharacter_allowed matrix choice _ distinct)
  simp only [Fintype.card_fin] at block_sum
  linarith

theorem coneCharacter_fiber (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (label : Option (Fin columns)) :
    coneCharacter matrix choice (rayVector matrix (.inr label)) =
      if label = choice.fiber then -(columns : ℤ) else 1 := by
  classical
  by_cases selected : label = choice.fiber
  · rw [selected, ite_eq_left rfl]
    exact coneCharacter_fiber_omitted matrix choice
  · rw [ite_eq_right selected]
    exact coneCharacter_allowed matrix choice _ selected

def augmentedTwistEntry (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (factor : Fin rows) (label : Option (Fin columns)) : ℤ :=
  label.elim 0 (matrix factor)

theorem coneCharacter_rowTwist (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (factor : Fin rows) :
    coneCharacter matrix choice (rowTwist matrix factor) =
      (∑ column, matrix factor column) -
        ((columns : ℤ) + 1) * augmentedTwistEntry matrix factor choice.fiber := by
  classical
  rw [rowTwist_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  have fiber_value : ∀ column,
      coneCharacter matrix choice (fiberPositive column) =
        1 - if choice.fiber = some column then ((columns : ℤ) + 1) else 0 := by
    intro column
    have value := coneCharacter_fiber matrix choice (some column)
    change coneCharacter matrix choice (fiberPositive column) = _ at value
    rw [value]
    by_cases selected : choice.fiber = some column <;> simp [selected, eq_comm]
  simp only [fiber_value, mul_sub, mul_one, Finset.sum_sub_distrib]
  cases omitted : choice.fiber with
  | none => simp [augmentedTwistEntry]
  | some column => simp [augmentedTwistEntry, mul_comm]

theorem coneCharacter_base_omitted (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (factor : Fin rows) :
    coneCharacter matrix choice (rayVector matrix (.inl (factor, choice.base factor))) =
      (∑ column, matrix factor column) - (baseDimension : ℤ) -
        ((columns : ℤ) + 1) * augmentedTwistEntry matrix factor choice.fiber := by
  classical
  have relation : (∑ label : Option (Fin baseDimension),
      coneCharacter matrix choice (rayVector matrix (.inl (factor, label)))) =
      coneCharacter matrix choice (rowTwist matrix factor) := by
    rw [Fintype.sum_option]
    have evaluated := congrArg (coneCharacter matrix choice) (base_ray_relation matrix factor)
    simpa only [map_add, map_sum, rayVector, Sum.elim_inl,
      Option.elim_none, Option.elim_some] using evaluated
  have block_sum := projective_block_sum
    (fun label : Option (Fin baseDimension) => coneCharacter matrix choice (rayVector matrix (.inl (factor, label))))
    (choice.base factor) (fun label distinct => coneCharacter_allowed matrix choice _ distinct)
  simp only [Fintype.card_fin] at block_sum
  rw [coneCharacter_rowTwist] at relation
  linarith

theorem coneBasis_range_and_character (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ (Lattice rows baseDimension columns))
    (cone_basis : (fan matrix).IsConeBasis basis) :
    ∃ choice : ConeChoice rows baseDimension columns,
      Set.range basis = Set.range (coneBasis matrix choice) ∧
        basis.sumCoords = coneCharacter matrix choice := by
  classical
  have presentation : ∃ choice : ConeChoice rows baseDimension columns,
      (PointedCone.hull ℝ (Set.range (fun index => latticeEmbedding rows baseDimension columns
        (basis index)))).IsFaceOf (maximalCone matrix choice) := cone_basis
  obtain ⟨choice, face⟩ := presentation
  have subset : Set.range basis ⊆ Set.range (coneBasis matrix choice) := by
    rintro vector ⟨index, rfl⟩
    let ray := (fan matrix).basisRay basis cone_basis index
    have ray_value : ray.val = basis index := (fan matrix).basisRay_val basis cone_basis index
    have contains : latticeEmbedding rows baseDimension columns ray.val ∈ maximalCone matrix choice :=
      face.le (PointedCone.subset_hull ⟨index,
        congrArg (latticeEmbedding rows baseDimension columns) ray_value.symm⟩)
    have ray_le : PointedCone.hull ℝ {latticeEmbedding rows baseDimension columns ray.val} ≤
        maximalCone matrix choice := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr contains)
    have ray_face := (fan matrix).isFaceOf_of_le (maximalCone_mem_fan matrix choice) ray.property.2 ray_le
    have salient := (maximalCone_isToricCone matrix choice).salient
    rw [maximalCone_eq_basisHull] at ray_face salient
    obtain ⟨coordinate, equality⟩ := TauCeti.Toric.primitive_eq_basis_of_ray_face
      (latticeEmbedding_isIntegralLattice rows baseDimension columns) (coneBasis matrix choice)
      ray.val ray.property.1 ray_face salient
    exact ⟨coordinate, equality.symm⟩
  have reverse : Set.range (coneBasis matrix choice) ⊆ Set.range basis := by
    rintro vector ⟨coordinate, rfl⟩
    by_contra absent
    have vanishes : (coneBasis matrix choice).coord coordinate =
        (0 : Lattice rows baseDimension columns →ₗ[ℤ] ℤ) := by
      apply basis.ext
      intro index
      obtain ⟨other, equality⟩ := subset (Set.mem_range_self index)
      have distinct : coordinate ≠ other := by
        intro same
        apply absent
        exact ⟨index, (same ▸ equality).symm⟩
      rw [← equality]
      simp [Basis.coord_apply, distinct]
    have impossible := DFunLike.congr_fun vanishes (coneBasis matrix choice coordinate)
    simp [Basis.coord_apply] at impossible
  refine ⟨choice, Set.Subset.antisymm subset reverse, ?_⟩
  apply basis.ext
  intro index
  obtain ⟨coordinate, equality⟩ := subset (Set.mem_range_self index)
  rw [Basis.sumCoords_self_apply, coneCharacter, ← equality, Basis.sumCoords_self_apply]

theorem coneCharacter_nongenerator_lt_one (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (nonnegative : ∀ factor column, 0 ≤ matrix factor column)
    (row_bound : ∀ factor, ∑ column, matrix factor column ≤ (baseDimension : ℤ))
    (choice : ConeChoice rows baseDimension columns) (label : RayLabel rows baseDimension columns)
    (outside : ¬ RayAllowed choice label) : coneCharacter matrix choice (rayVector matrix label) < 1 := by
  cases label with
  | inl label =>
    rcases label with ⟨factor, position⟩
    have omitted : position = choice.base factor := by
      simpa only [RayAllowed, Sum.elim_inl, not_not] using outside
    rw [omitted, coneCharacter_base_omitted]
    have twist_nonnegative : 0 ≤ augmentedTwistEntry matrix factor choice.fiber := by
      cases choice.fiber with
      | none => exact le_rfl
      | some column => exact nonnegative factor column
    have correction_nonnegative : 0 ≤ ((columns : ℤ) + 1) *
        augmentedTwistEntry matrix factor choice.fiber :=
      mul_nonneg (by omega) twist_nonnegative
    have bound := row_bound factor
    omega
  | inr position =>
    have omitted : position = choice.fiber := by
      simpa only [RayAllowed, Sum.elim_inr, not_not] using outside
    rw [omitted, coneCharacter_fiber_omitted]
    omega

theorem hasStrictAnticanonicalConeSupport_of_row_bounds
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (nonnegative : ∀ factor column, 0 ≤ matrix factor column)
    (row_bound : ∀ factor, ∑ column, matrix factor column ≤ (baseDimension : ℤ)) :
    (fan (baseDimension := baseDimension) matrix).HasStrictAnticanonicalConeSupport := by
  intro dimension basis cone_basis ray outside
  obtain ⟨choice, same_range, same_character⟩ := coneBasis_range_and_character matrix basis cone_basis
  obtain ⟨label, rfl⟩ := (labelRay_bijective matrix base_positive fiber_positive).surjective ray
  have not_allowed : ¬ RayAllowed choice label := by
    intro allowed
    apply outside
    rw [same_range, ← allowedRayVectors_eq_basis]
    exact ⟨label, allowed, rfl⟩
  have bound := coneCharacter_nongenerator_lt_one matrix nonnegative row_bound choice label not_allowed
  change (-1 : ℤ) < -basis.sumCoords (rayVector matrix label)
  rw [same_character]
  omega

theorem fixedWeight_hasStrictAnticanonicalConeSupport {ones : ℕ}
    (matrix : FixedWeightMatrix rows columns ones)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (weight_bound : ones ≤ baseDimension) :
    (fan (baseDimension := baseDimension) (fixedWeightTwist matrix)).HasStrictAnticanonicalConeSupport := by
  apply hasStrictAnticanonicalConeSupport_of_row_bounds (fixedWeightTwist matrix)
    base_positive fiber_positive (fixedWeightTwist_nonnegative matrix)
  intro factor
  rw [fixedWeightTwist_row_sum]
  exact_mod_cast weight_bound

theorem paperFamily_hasStrictAnticanonicalConeSupport
    (matrix : FixedWeightMatrix rows columns baseDimension)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns) :
    (fan (baseDimension := baseDimension) (fixedWeightTwist matrix)).HasStrictAnticanonicalConeSupport :=
  fixedWeight_hasStrictAnticanonicalConeSupport matrix base_positive fiber_positive le_rfl

end BondalThomsen.ProjectiveBundle
