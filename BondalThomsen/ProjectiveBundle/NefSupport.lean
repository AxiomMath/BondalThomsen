module

public import BondalThomsen.ProjectiveBundle.Support
public import BondalThomsen.ProjectiveBundle.DivisorClasses
public import BondalThomsen.Toric.Divisor.SupportClasses

@[expose] public section

namespace BondalThomsen.ProjectiveBundle

open Finset Set Module

variable {rows baseDimension columns : ℕ}

noncomputable def bundleDivisorCharacter (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns)
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    Lattice rows baseDimension columns →+ ℤ :=
  (fan matrix).coneDivisorCharacter (coneFinBasis matrix choice)
    (coneFinBasis_isConeBasis matrix choice) divisor

set_option maxHeartbeats 600000 in
theorem bundleDivisorCharacter_allowed (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (choice : ConeChoice rows baseDimension columns)
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor)
    (label : RayLabel rows baseDimension columns) (allowed : RayAllowed choice label) :
    bundleDivisorCharacter matrix choice divisor (rayVector matrix label) =
      -divisor (labelRay matrix base_positive fiber_positive label) := by
  exact (fan matrix).coneDivisorCharacter_ray (coneFinBasis matrix choice)
    (coneFinBasis_isConeBasis matrix choice) divisor
    (labelRay matrix base_positive fiber_positive label) (by
      rw [coneFinBasis_hull_eq]
      exact (labelRay_mem_maximalCone_iff matrix base_positive fiber_positive choice label).mpr allowed)

theorem residualRepresentative_label (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (coefficients : (Fin rows ⊕ Unit) → ℤ) (label : RayLabel rows baseDimension columns) :
    residualRepresentative matrix base_positive fiber_positive coefficients
      (labelRay matrix base_positive fiber_positive label) =
      Sum.elim (fun label : Fin rows × Option (Fin baseDimension) =>
        label.2.elim (coefficients (.inl label.1)) (fun _ => 0))
        (fun label : Option (Fin columns) => label.elim (coefficients (.inr ())) (fun _ => 0)) label := by
  change Sum.elim _ _ ((rayEquiv matrix base_positive fiber_positive).symm
    ((rayEquiv matrix base_positive fiber_positive) label)) = _
  rw [Equiv.symm_apply_apply]

theorem residual_fiber_support_gap (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (coefficients : (Fin rows ⊕ Unit) → ℤ) (choice : ConeChoice rows baseDimension columns) :
    bundleDivisorCharacter matrix choice
        (residualRepresentative matrix base_positive fiber_positive coefficients)
        (rayVector matrix (.inr choice.fiber)) +
      residualRepresentative matrix base_positive fiber_positive coefficients
        (labelRay matrix base_positive fiber_positive (.inr choice.fiber)) = coefficients (.inr ()) := by
  classical
  let character := bundleDivisorCharacter matrix choice
    (residualRepresentative matrix base_positive fiber_positive coefficients)
  have relation := congrArg character
    (fiber_ray_relation (rows := rows) (baseDimension := baseDimension) (columns := columns))
  have sum_values : (∑ label : Option (Fin columns),
      (character (rayVector matrix (.inr label)) +
        residualRepresentative matrix base_positive fiber_positive coefficients
          (labelRay matrix base_positive fiber_positive (.inr label)))) = coefficients (.inr ()) := by
    rw [Finset.sum_add_distrib, Fintype.sum_option]
    have character_sum : character fiberNegative +
        ∑ column : Fin columns, character (fiberPositive column) = 0 := by
      simpa only [map_add, map_sum, map_zero] using relation
    simp only [rayVector, Sum.elim_inr, Option.elim_none, Option.elim_some] at *
    rw [character_sum]
    simp [residualRepresentative_label]
  rw [Finset.sum_eq_single choice.fiber] at sum_values
  · exact sum_values
  · intro label _ distinct
    change bundleDivisorCharacter matrix choice _ (rayVector matrix (.inr label)) + _ = 0
    rw [bundleDivisorCharacter_allowed matrix base_positive fiber_positive choice _ (.inr label) distinct]
    exact neg_add_cancel _
  · simp

theorem residual_character_fiberPositive (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (coefficients : (Fin rows ⊕ Unit) → ℤ) (choice : ConeChoice rows baseDimension columns)
    (column : Fin columns) :
    bundleDivisorCharacter matrix choice
      (residualRepresentative matrix base_positive fiber_positive coefficients) (fiberPositive column) =
      if choice.fiber = some column then coefficients (.inr ()) else 0 := by
  classical
  by_cases omitted : choice.fiber = some column
  · have gap := residual_fiber_support_gap matrix base_positive fiber_positive coefficients choice
    rw [omitted] at gap
    simpa [rayVector, residualRepresentative_label, omitted] using gap
  · have value := bundleDivisorCharacter_allowed matrix base_positive fiber_positive choice
      (residualRepresentative matrix base_positive fiber_positive coefficients)
      (.inr (some column)) (fun equality => omitted equality.symm)
    simpa [rayVector, residualRepresentative_label, omitted] using value

theorem residual_character_rowTwist (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (coefficients : (Fin rows ⊕ Unit) → ℤ) (choice : ConeChoice rows baseDimension columns)
    (factor : Fin rows) :
    bundleDivisorCharacter matrix choice
      (residualRepresentative matrix base_positive fiber_positive coefficients) (rowTwist matrix factor) =
      coefficients (.inr ()) * augmentedTwistEntry matrix factor choice.fiber := by
  classical
  change (bundleDivisorCharacter matrix choice
    (residualRepresentative matrix base_positive fiber_positive coefficients)).toIntLinearMap
      (rowTwist matrix factor) = _
  rw [rowTwist_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul, AddMonoidHom.coe_toIntLinearMap,
    residual_character_fiberPositive matrix base_positive fiber_positive coefficients choice]
  cases omitted : choice.fiber with
  | none => simp [augmentedTwistEntry]
  | some column => simp [augmentedTwistEntry, mul_comm]

theorem residual_base_support_gap (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (coefficients : (Fin rows ⊕ Unit) → ℤ) (choice : ConeChoice rows baseDimension columns)
    (factor : Fin rows) :
    bundleDivisorCharacter matrix choice
        (residualRepresentative matrix base_positive fiber_positive coefficients)
        (rayVector matrix (.inl (factor, choice.base factor))) +
      residualRepresentative matrix base_positive fiber_positive coefficients
        (labelRay matrix base_positive fiber_positive (.inl (factor, choice.base factor))) =
      coefficients (.inl factor) +
        coefficients (.inr ()) * augmentedTwistEntry matrix factor choice.fiber := by
  classical
  let character := bundleDivisorCharacter matrix choice
    (residualRepresentative matrix base_positive fiber_positive coefficients)
  have relation := congrArg character (base_ray_relation matrix factor)
  have sum_values : (∑ label : Option (Fin baseDimension),
      (character (rayVector matrix (.inl (factor, label))) +
        residualRepresentative matrix base_positive fiber_positive coefficients
          (labelRay matrix base_positive fiber_positive (.inl (factor, label))))) =
      coefficients (.inl factor) + coefficients (.inr ()) * augmentedTwistEntry matrix factor choice.fiber := by
    rw [Finset.sum_add_distrib, Fintype.sum_option]
    have character_sum : character (baseNegative matrix factor) +
        ∑ position : Fin baseDimension, character (basePositive factor position) =
        character (rowTwist matrix factor) := by
      simpa only [map_add, map_sum] using relation
    simp only [rayVector, Sum.elim_inl, Option.elim_none, Option.elim_some]
    rw [character_sum]
    simp [character, residualRepresentative_label, residual_character_rowTwist, add_comm]
  rw [Finset.sum_eq_single (choice.base factor)] at sum_values
  · exact sum_values
  · intro label _ distinct
    change bundleDivisorCharacter matrix choice _ (rayVector matrix (.inl (factor, label))) + _ = 0
    rw [bundleDivisorCharacter_allowed matrix base_positive fiber_positive choice _ (.inl (factor, label)) distinct]
    exact neg_add_cancel _
  · simp

theorem bundleDivisorCharacter_eq_of_basisRange (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ (Lattice rows baseDimension columns))
    (cone_basis : (fan matrix).IsConeBasis basis) (choice : ConeChoice rows baseDimension columns)
    (same_range : Set.range basis = Set.range (coneBasis matrix choice))
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    (fan matrix).coneDivisorCharacter basis cone_basis divisor =
      bundleDivisorCharacter matrix choice divisor := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  let ray := (fan matrix).basisRay basis cone_basis index
  have ray_value : ray.val = basis index := (fan matrix).basisRay_val basis cone_basis index
  have contains : latticeEmbedding rows baseDimension columns ray.val ∈
      PointedCone.hull ℝ (Set.range (fun other => latticeEmbedding rows baseDimension columns
        (coneFinBasis matrix choice other))) := by
    rw [coneFinBasis_hull_eq, maximalCone_eq_basisHull, ray_value]
    have member : basis index ∈ Set.range (coneBasis matrix choice) :=
      same_range ▸ Set.mem_range_self index
    obtain ⟨coordinate, equality⟩ := member
    exact PointedCone.subset_hull ⟨coordinate, congrArg
      (latticeEmbedding rows baseDimension columns) equality⟩
  change (fan matrix).coneDivisorCharacter basis cone_basis divisor (basis index) =
    bundleDivisorCharacter matrix choice divisor (basis index)
  rw [(fan matrix).coneDivisorCharacter_basis]
  exact ((fan matrix).coneDivisorCharacter_ray (coneFinBasis matrix choice)
    (coneFinBasis_isConeBasis matrix choice) divisor ray contains).symm

theorem hasRaySupportInequalities_iff_choices (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    (fan matrix).HasRaySupportInequalities divisor ↔
      ∀ choice : ConeChoice rows baseDimension columns, ∀ label : RayLabel rows baseDimension columns,
        -divisor (labelRay matrix base_positive fiber_positive label) ≤
          bundleDivisorCharacter matrix choice divisor (rayVector matrix label) := by
  constructor
  · intro support choice label
    exact support _ (coneFinBasis matrix choice) (coneFinBasis_isConeBasis matrix choice)
      (labelRay matrix base_positive fiber_positive label)
  · intro support dimension basis cone_basis ray
    obtain ⟨choice, same_range, _⟩ := coneBasis_range_and_character matrix basis cone_basis
    rw [bundleDivisorCharacter_eq_of_basisRange matrix basis cone_basis choice same_range divisor]
    obtain ⟨label, rfl⟩ := (labelRay_bijective matrix base_positive fiber_positive).surjective ray
    exact support choice label

theorem residual_hasRaySupportInequalities_iff (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (coefficients : (Fin rows ⊕ Unit) → ℤ) :
    (fan matrix).HasRaySupportInequalities
        (residualRepresentative matrix base_positive fiber_positive coefficients) ↔
      0 ≤ coefficients (.inr ()) ∧
        ∀ factor : Fin rows, ∀ selected : Option (Fin columns),
          0 ≤ coefficients (.inl factor) + coefficients (.inr ()) * augmentedTwistEntry matrix factor selected := by
  rw [hasRaySupportInequalities_iff_choices matrix base_positive fiber_positive]
  constructor
  · intro support
    have fiber_bound := support (referenceChoice rows baseDimension columns) (.inr none)
    have fiber_gap := residual_fiber_support_gap matrix base_positive fiber_positive coefficients
      (referenceChoice rows baseDimension columns)
    change bundleDivisorCharacter matrix (referenceChoice rows baseDimension columns) _
      (rayVector matrix (.inr none)) +
      residualRepresentative matrix base_positive fiber_positive coefficients
        (labelRay matrix base_positive fiber_positive (.inr none)) = coefficients (.inr ()) at fiber_gap
    refine ⟨by linarith, ?_⟩
    intro factor selected
    let choice : ConeChoice rows baseDimension columns := ⟨fun _ => none, selected⟩
    have base_bound := support choice (.inl (factor, none))
    have base_gap := residual_base_support_gap matrix base_positive fiber_positive coefficients choice factor
    change bundleDivisorCharacter matrix choice _ (rayVector matrix (.inl (factor, none))) + _ = _ at base_gap
    linarith
  · rintro ⟨fiber_bound, base_bounds⟩ choice label
    by_cases allowed : RayAllowed choice label
    · rw [bundleDivisorCharacter_allowed matrix base_positive fiber_positive choice _ label allowed]
    · cases label with
      | inl label =>
        rcases label with ⟨factor, position⟩
        have omitted : position = choice.base factor := by
          simpa only [RayAllowed, Sum.elim_inl, not_not] using allowed
        rw [omitted]
        have gap := residual_base_support_gap matrix base_positive fiber_positive coefficients choice factor
        have bound := base_bounds factor choice.fiber
        linarith
      | inr position =>
        have omitted : position = choice.fiber := by
          simpa only [RayAllowed, Sum.elim_inr, not_not] using allowed
        rw [omitted]
        have gap := residual_fiber_support_gap matrix base_positive fiber_positive coefficients choice
        linarith

theorem residual_hasRaySupportInequalities_iff_nonnegative
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (nonnegative : ∀ factor column, 0 ≤ matrix factor column)
    (coefficients : (Fin rows ⊕ Unit) → ℤ) :
    (fan matrix).HasRaySupportInequalities
        (residualRepresentative matrix base_positive fiber_positive coefficients) ↔
      ∀ coordinate, 0 ≤ coefficients coordinate := by
  rw [residual_hasRaySupportInequalities_iff matrix base_positive fiber_positive]
  constructor
  · rintro ⟨fiber_bound, base_bounds⟩ coordinate
    cases coordinate with
    | inl factor => simpa [augmentedTwistEntry] using base_bounds factor none
    | inr fiber_index => cases fiber_index; exact fiber_bound
  · intro bounds
    refine ⟨bounds (.inr ()), ?_⟩
    intro factor selected
    apply add_nonneg (bounds (.inl factor))
    apply mul_nonneg (bounds (.inr ()))
    cases selected with
    | none => exact le_rfl
    | some column => exact nonnegative factor column

theorem hasRaySupportInequalities_add_principal_iff
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor)
    (character : Lattice rows baseDimension columns →+ ℤ) :
    (fan matrix).HasRaySupportInequalities (divisor + (fan matrix).principalRayDivisor character) ↔
      (fan matrix).HasRaySupportInequalities divisor := by
  unfold TauCeti.Toric.Fan.HasRaySupportInequalities
  simp only [Finsupp.add_apply, (fan matrix).coneDivisorCharacter_add,
    (fan matrix).coneDivisorCharacter_principal, AddMonoidHom.add_apply,
    AddMonoidHom.neg_apply, (fan matrix).principalRayDivisor_apply]
  constructor
  · intro support dimension basis cone_basis ray
    have bound := support dimension basis cone_basis ray
    linarith
  · intro support dimension basis cone_basis ray
    have bound := support dimension basis cone_basis ray
    linarith

theorem hasRaySupportInequalities_normalized_iff
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    (fan matrix).HasRaySupportInequalities (normalizedDivisor matrix base_positive fiber_positive divisor) ↔
      (fan matrix).HasRaySupportInequalities divisor := by
  change (fan matrix).HasRaySupportInequalities
    (divisor - (fan matrix).principalRayDivisor (eliminationCharacter matrix base_positive fiber_positive divisor)) ↔ _
  rw [sub_eq_add_neg, ← map_neg]
  exact hasRaySupportInequalities_add_principal_iff matrix divisor _

theorem hasRaySupportInequalities_iff_residual_nonnegative
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (nonnegative : ∀ factor column, 0 ≤ matrix factor column)
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    (fan matrix).HasRaySupportInequalities divisor ↔
      ∀ coordinate, 0 ≤ residualCoordinates matrix base_positive fiber_positive divisor coordinate := by
  rw [← hasRaySupportInequalities_normalized_iff matrix base_positive fiber_positive divisor,
    normalizedDivisor_eq_residualRepresentative]
  exact residual_hasRaySupportInequalities_iff_nonnegative matrix base_positive fiber_positive nonnegative _

theorem hasRaySupportInequalities_iff_classCoordinates_nonnegative
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (base_positive : 0 < baseDimension) (fiber_positive : 0 < columns)
    (nonnegative : ∀ factor column, 0 ≤ matrix factor column)
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    (fan matrix).HasRaySupportInequalities divisor ↔
      ∀ coordinate, 0 ≤ divisorClassEquiv matrix base_positive fiber_positive
        ((fan matrix).invariantRayDivisorClass divisor) coordinate := by
  rw [divisorClassEquiv_mk]
  exact hasRaySupportInequalities_iff_residual_nonnegative matrix base_positive fiber_positive
    nonnegative divisor

end BondalThomsen.ProjectiveBundle
