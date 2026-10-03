module

public import BondalThomsen.ProjectiveBundle.Combinatorics
public import BondalThomsen.Fan.RegularBasisCone
public import BondalThomsen.Fan.ConeBasisFaces

@[expose] public section

namespace BondalThomsen.ProjectiveBundle

open Finset Set Module

variable {rows baseDimension columns : ℕ}

abbrev Ambient (rows baseDimension columns : ℕ) :=
  Coordinate rows baseDimension columns → ℝ

def latticeEmbedding (rows baseDimension columns : ℕ) :
    Lattice rows baseDimension columns →+ Ambient rows baseDimension columns :=
  (Int.castAddHom ℝ).compLeft _

theorem latticeEmbedding_isIntegralLattice (rows baseDimension columns : ℕ) :
    TauCeti.Toric.IsIntegralLattice (latticeEmbedding rows baseDimension columns) := by
  apply TauCeti.Toric.isIntegralLattice_of_basis
    (standardBasis rows baseDimension columns)
    (Pi.basisFun ℝ (Coordinate rows baseDimension columns))
  intro coordinate
  ext other
  simp [latticeEmbedding, standardBasis, Pi.basisFun_apply, Pi.single_apply, apply_ite]

def RayAllowed (choice : ConeChoice rows baseDimension columns) :
    RayLabel rows baseDimension columns → Prop :=
  Sum.elim (fun label => label.2 ≠ choice.base label.1) (fun label => label ≠ choice.fiber)

def maximalCone (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) : PointedCone ℝ (Ambient rows baseDimension columns) :=
  PointedCone.hull ℝ ((fun label => latticeEmbedding rows baseDimension columns
    (rayVector matrix label)) '' {label | RayAllowed choice label})

theorem exists_projective_coefficients {Index : Type*} [Fintype Index]
    (vector : Index → ℝ) :
    ∃ omitted : Option Index, ∃ weights : Option Index → ℝ,
      (∀ label, 0 ≤ weights label) ∧ weights omitted = 0 ∧
        ∀ index, vector index = weights (some index) - weights none := by
  classical
  let augmented : Option Index → ℝ := fun label => label.elim 0 vector
  obtain ⟨omitted, _, minimum⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Option Index)) augmented (by simp)
  refine ⟨omitted, fun label => augmented label - augmented omitted, ?_, sub_self _, ?_⟩
  · intro label
    exact sub_nonneg.mpr (minimum label (Finset.mem_univ _))
  · intro index
    simp [augmented]

theorem exists_ray_decomposition (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (point : Ambient rows baseDimension columns) :
    ∃ choice : ConeChoice rows baseDimension columns,
      ∃ weights : RayLabel rows baseDimension columns → ℝ,
        (∀ label, 0 ≤ weights label) ∧
        (∀ label, ¬RayAllowed choice label → weights label = 0) ∧
        point = ∑ label, weights label • latticeEmbedding rows baseDimension columns
          (rayVector matrix label) := by
  classical
  have base_decomposition : ∀ factor : Fin rows,
      ∃ omitted : Option (Fin baseDimension), ∃ weights : Option (Fin baseDimension) → ℝ,
        (∀ label, 0 ≤ weights label) ∧ weights omitted = 0 ∧
          ∀ position, point (.inl (factor, position)) = weights (some position) - weights none :=
    fun factor => exists_projective_coefficients (fun position => point (.inl (factor, position)))
  choose base_omitted base_weights base_nonnegative base_zero base_coordinates using base_decomposition
  let residual : Fin columns → ℝ := fun column => point (.inr column) -
    ∑ factor : Fin rows, base_weights factor none * (matrix factor column : ℝ)
  obtain ⟨fiber_omitted, fiber_weights, fiber_nonnegative, fiber_zero, fiber_coordinates⟩ :=
    exists_projective_coefficients residual
  refine ⟨⟨base_omitted, fiber_omitted⟩,
    Sum.elim (fun label => base_weights label.1 label.2) fiber_weights, ?_, ?_, ?_⟩
  · intro label
    cases label with
    | inl label => exact base_nonnegative label.1 label.2
    | inr label => exact fiber_nonnegative label
  · intro label not_allowed
    cases label with
    | inl label =>
      have equality : label.2 = base_omitted label.1 := by
        simpa only [RayAllowed, Sum.elim_inl, not_not] using not_allowed
      change base_weights label.1 label.2 = 0
      rw [equality]
      exact base_zero label.1
    | inr label =>
      have equality : label = fiber_omitted := by
        simpa only [RayAllowed, Sum.elim_inr, not_not] using not_allowed
      exact equality ▸ fiber_zero
  · ext coordinate
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_option,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, latticeEmbedding, AddMonoidHom.compLeft_apply,
      Sum.elim_inl, Sum.elim_inr]
    cases coordinate with
    | inl coordinate =>
      rcases coordinate with ⟨factor, position⟩
      simp [rayVector, baseNegative, basePositive, fiberNegative, fiberPositive,
        Pi.single_apply, apply_ite, base_coordinates]
      rw [Finset.sum_add_distrib]
      simp only [ite_and]
      simp
      ring
    | inr column =>
      simp [rayVector, baseNegative, basePositive, fiberNegative, fiberPositive,
        Pi.single_apply, apply_ite]
      have coordinate_eq := fiber_coordinates column
      dsimp [residual] at coordinate_eq
      linarith

theorem maximalCones_cover (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (point : Ambient rows baseDimension columns) :
    ∃ choice : ConeChoice rows baseDimension columns, point ∈ maximalCone matrix choice := by
  classical
  obtain ⟨choice, weights, nonnegative, zero_omitted, decomposition⟩ :=
    exists_ray_decomposition matrix point
  refine ⟨choice, ?_⟩
  rw [decomposition]
  apply Submodule.sum_mem
  intro label _
  by_cases allowed : RayAllowed choice label
  · exact PointedCone.smul_mem _ (nonnegative label)
      (PointedCone.subset_hull ⟨label, allowed, rfl⟩)
  · rw [zero_omitted label allowed, zero_smul]
    exact Submodule.zero_mem _

theorem allowedRayVectors_eq_basis (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    rayVector matrix '' {label | RayAllowed choice label} = Set.range (coneBasis matrix choice) := by
  classical
  ext vector
  constructor
  · rintro ⟨label, allowed, rfl⟩
    cases label with
    | inl label =>
      rcases label with ⟨factor, position⟩
      cases position with
      | none =>
        have selected_exists : ∃ position, choice.base factor = some position := by
          cases equality : choice.base factor with
          | none => exact False.elim (allowed equality.symm)
          | some position => exact ⟨position, rfl⟩
        obtain ⟨position, selected⟩ := selected_exists
        exact ⟨.inl (factor, position), coneBasis_base_selected matrix choice factor position selected⟩
      | some position =>
        have unselected : choice.base factor ≠ some position := fun equality => allowed equality.symm
        exact ⟨.inl (factor, position), coneBasis_base_unselected matrix choice factor position unselected⟩
    | inr label =>
      cases label with
      | none =>
        have selected_exists : ∃ column, choice.fiber = some column := by
          cases equality : choice.fiber with
          | none => exact False.elim (allowed equality.symm)
          | some column => exact ⟨column, rfl⟩
        obtain ⟨column, selected⟩ := selected_exists
        exact ⟨.inr column, coneBasis_fiber_selected matrix choice column selected⟩
      | some column =>
        have unselected : choice.fiber ≠ some column := fun equality => allowed equality.symm
        exact ⟨.inr column, coneBasis_fiber_unselected matrix choice column unselected⟩
  · rintro ⟨coordinate, rfl⟩
    cases coordinate with
    | inl coordinate =>
      rcases coordinate with ⟨factor, position⟩
      by_cases selected : choice.base factor = some position
      · refine ⟨.inl (factor, none), ?_, ?_⟩
        · simp [RayAllowed, selected]
        · exact (coneBasis_base_selected matrix choice factor position selected).symm
      · refine ⟨.inl (factor, some position), ?_, ?_⟩
        · exact fun equality => selected equality.symm
        · exact (coneBasis_base_unselected matrix choice factor position selected).symm
    | inr column =>
      by_cases selected : choice.fiber = some column
      · refine ⟨.inr none, ?_, ?_⟩
        · simp [RayAllowed, selected]
        · exact (coneBasis_fiber_selected matrix choice column selected).symm
      · refine ⟨.inr (some column), ?_, ?_⟩
        · exact fun equality => selected equality.symm
        · exact (coneBasis_fiber_unselected matrix choice column selected).symm

theorem maximalCone_eq_basisHull (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    maximalCone matrix choice = PointedCone.hull ℝ
      (Set.range (fun coordinate => latticeEmbedding rows baseDimension columns
        (coneBasis matrix choice coordinate))) := by
  unfold maximalCone
  have image_eq := congrArg (Set.image (latticeEmbedding rows baseDimension columns))
    (allowedRayVectors_eq_basis matrix choice)
  rw [Set.image_image, ← Set.range_comp'] at image_eq
  exact congrArg (PointedCone.hull ℝ) image_eq

noncomputable def realConeBasis (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    Basis (Coordinate rows baseDimension columns) ℝ (Ambient rows baseDimension columns) :=
  (latticeEmbedding_isIntegralLattice rows baseDimension columns).isBaseChange.basis
    (coneBasis matrix choice)

theorem realConeBasis_apply (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) (coordinate : Coordinate rows baseDimension columns) :
    realConeBasis matrix choice coordinate = latticeEmbedding rows baseDimension columns
      (coneBasis matrix choice coordinate) := by
  exact (latticeEmbedding_isIntegralLattice rows baseDimension columns).isBaseChange.basis_apply _ _

theorem maximalCone_eq_realBasisHull (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    maximalCone matrix choice = PointedCone.hull ℝ (Set.range (realConeBasis matrix choice)) := by
  rw [maximalCone_eq_basisHull]
  apply congrArg (PointedCone.hull ℝ)
  apply congrArg Set.range
  exact funext (fun coordinate => (realConeBasis_apply matrix choice coordinate).symm)

theorem maximalCone_isToricCone (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    TauCeti.Toric.IsToricCone (latticeEmbedding rows baseDimension columns) (maximalCone matrix choice) := by
  classical
  constructor
  · apply TauCeti.Toric.isLatticeRational_iff.mpr
    refine ⟨Finset.univ.image (coneBasis matrix choice), ?_⟩
    rw [maximalCone_eq_basisHull, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      ← Set.range_comp']
  · rintro point member nonzero negative_member
    rw [maximalCone_eq_realBasisHull] at member negative_member
    have nonnegative := (BondalThomsen.mem_basisCone_iff (realConeBasis matrix choice) point).mp member
    have negative_nonnegative :=
      (BondalThomsen.mem_basisCone_iff (realConeBasis matrix choice) (-point)).mp negative_member
    apply nonzero
    apply (realConeBasis matrix choice).repr.injective
    ext coordinate
    have first := nonnegative coordinate
    have second := negative_nonnegative coordinate
    simp only [map_neg, Finsupp.neg_apply] at second
    simp only [map_zero, Finsupp.zero_apply]
    linarith

theorem maximalCone_isRegularCone (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    TauCeti.Toric.IsRegularCone (latticeEmbedding rows baseDimension columns) (maximalCone matrix choice) :=
  TauCeti.Toric.isRegularCone_of_basisHull
    (latticeEmbedding_isIntegralLattice rows baseDimension columns) (coneBasis matrix choice) _
    (maximalCone_isToricCone matrix choice) (maximalCone_eq_basisHull matrix choice)

theorem projective_coefficients_unique {Index : Type*}
    (first second : Option Index → ℝ) (first_omitted second_omitted : Option Index)
    (first_nonnegative : ∀ label, 0 ≤ first label)
    (second_nonnegative : ∀ label, 0 ≤ second label)
    (first_zero : first first_omitted = 0) (second_zero : second second_omitted = 0)
    (coordinates : ∀ index, first (some index) - first none =
      second (some index) - second none) : first = second := by
  have differences : ∀ label, first label - second label = first none - second none := by
    intro label
    cases label with
    | none => rfl
    | some index => have equality := coordinates index; linarith
  have first_bound := differences first_omitted
  have second_bound := differences second_omitted
  have first_nonnegative_at := first_nonnegative second_omitted
  have second_nonnegative_at := second_nonnegative first_omitted
  have same_none : first none = second none := by linarith
  funext label
  have equality := differences label
  linarith

theorem mem_rayHull_iff (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (allowed : Set (RayLabel rows baseDimension columns))
    (point : Ambient rows baseDimension columns) :
    point ∈ PointedCone.hull ℝ ((fun label => latticeEmbedding rows baseDimension columns
      (rayVector matrix label)) '' allowed) ↔
      ∃ weights : RayLabel rows baseDimension columns → ℝ,
        (∀ label, 0 ≤ weights label) ∧
        (∀ label, label ∉ allowed → weights label = 0) ∧
        point = ∑ label, weights label • latticeEmbedding rows baseDimension columns
          (rayVector matrix label) := by
  classical
  constructor
  · intro member
    induction member using Submodule.span_induction with
    | mem vector member =>
      obtain ⟨label, allowed_label, rfl⟩ := member
      refine ⟨Pi.single label 1, ?_, ?_, ?_⟩
      · intro other
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · intro other not_allowed
        have distinct : other ≠ label := fun equality => not_allowed (equality ▸ allowed_label)
        simp [distinct]
      · simp [Pi.single_apply]
    | zero => exact ⟨fun _ => 0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩
    | add first second _ _ first_witness second_witness =>
      obtain ⟨first_weights, first_nonnegative, first_zero, first_sum⟩ := first_witness
      obtain ⟨second_weights, second_nonnegative, second_zero, second_sum⟩ := second_witness
      refine ⟨fun label => first_weights label + second_weights label,
        fun label => add_nonneg (first_nonnegative label) (second_nonnegative label), ?_, ?_⟩
      · intro label not_allowed
        change first_weights label + second_weights label = 0
        rw [first_zero label not_allowed, second_zero label not_allowed, add_zero]
      · simp only [add_smul, Finset.sum_add_distrib, ← first_sum, ← second_sum]
    | smul scalar vector _ witness =>
      obtain ⟨weights, nonnegative, zero_omitted, decomposition⟩ := witness
      refine ⟨fun label => (scalar : ℝ) * weights label,
        fun label => mul_nonneg scalar.property (nonnegative label), ?_, ?_⟩
      · intro label not_allowed
        change (scalar : ℝ) * weights label = 0
        rw [zero_omitted label not_allowed, mul_zero]
      · change (scalar : ℝ) • vector = _
        rw [decomposition, Finset.smul_sum]
        simp only [mul_smul]
  · rintro ⟨weights, nonnegative, zero_omitted, rfl⟩
    apply Submodule.sum_mem
    intro label _
    by_cases member : label ∈ allowed
    · exact PointedCone.smul_mem _ (nonnegative label)
        (PointedCone.subset_hull ⟨label, member, rfl⟩)
    · rw [zero_omitted label member, zero_smul]
      exact Submodule.zero_mem _

theorem raySum_base_apply (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (weights : RayLabel rows baseDimension columns → ℝ)
    (factor : Fin rows) (position : Fin baseDimension) :
    (∑ label, weights label • latticeEmbedding rows baseDimension columns
      (rayVector matrix label)) (.inl (factor, position)) =
      weights (.inl (factor, some position)) - weights (.inl (factor, none)) := by
  classical
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_option,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, latticeEmbedding, AddMonoidHom.compLeft_apply]
  simp [rayVector, baseNegative, basePositive, fiberNegative, fiberPositive,
    Pi.single_apply, apply_ite]
  rw [Finset.sum_add_distrib]
  simp only [ite_and]
  simp
  ring

theorem raySum_fiber_apply (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (weights : RayLabel rows baseDimension columns → ℝ) (column : Fin columns) :
    (∑ label, weights label • latticeEmbedding rows baseDimension columns
      (rayVector matrix label)) (.inr column) =
      (∑ factor, weights (.inl (factor, none)) * (matrix factor column : ℝ)) +
        weights (.inr (some column)) - weights (.inr none) := by
  classical
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_option,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, latticeEmbedding, AddMonoidHom.compLeft_apply]
  simp [rayVector, baseNegative, basePositive, fiberNegative, fiberPositive,
    Pi.single_apply, apply_ite]
  ring

theorem normalized_ray_coefficients_unique
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (first_choice second_choice : ConeChoice rows baseDimension columns)
    (first_weights second_weights : RayLabel rows baseDimension columns → ℝ)
    (first_nonnegative : ∀ label, 0 ≤ first_weights label)
    (second_nonnegative : ∀ label, 0 ≤ second_weights label)
    (first_zero : ∀ label, ¬RayAllowed first_choice label → first_weights label = 0)
    (second_zero : ∀ label, ¬RayAllowed second_choice label → second_weights label = 0)
    (same_point :
      ∑ label, first_weights label • latticeEmbedding rows baseDimension columns
        (rayVector matrix label) =
      ∑ label, second_weights label • latticeEmbedding rows baseDimension columns
        (rayVector matrix label)) : first_weights = second_weights := by
  have same_base : ∀ factor label,
      first_weights (.inl (factor, label)) = second_weights (.inl (factor, label)) := by
    intro factor
    apply congrFun
    apply projective_coefficients_unique
      (fun label => first_weights (.inl (factor, label)))
      (fun label => second_weights (.inl (factor, label)))
      (first_choice.base factor) (second_choice.base factor)
      (fun label => first_nonnegative (.inl (factor, label)))
      (fun label => second_nonnegative (.inl (factor, label)))
    · exact first_zero _ (by simp [RayAllowed])
    · exact second_zero _ (by simp [RayAllowed])
    · intro position
      have coordinate_equality := congrFun same_point (.inl (factor, position))
      simpa only [raySum_base_apply] using coordinate_equality
  have same_fiber : ∀ label, first_weights (.inr label) = second_weights (.inr label) := by
    apply congrFun
    apply projective_coefficients_unique
      (fun label => first_weights (.inr label)) (fun label => second_weights (.inr label))
      first_choice.fiber second_choice.fiber
      (fun label => first_nonnegative (.inr label))
      (fun label => second_nonnegative (.inr label))
    · exact first_zero _ (by simp [RayAllowed])
    · exact second_zero _ (by simp [RayAllowed])
    · intro column
      have coordinate_equality := congrFun same_point (.inr column)
      simp only [raySum_fiber_apply, same_base] at coordinate_equality
      linarith
  funext label
  cases label with
  | inl label => exact same_base label.1 label.2
  | inr label => exact same_fiber label

theorem maximalCone_inf_eq_rayHull (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (first_choice second_choice : ConeChoice rows baseDimension columns) :
    maximalCone matrix first_choice ⊓ maximalCone matrix second_choice =
      PointedCone.hull ℝ ((fun label => latticeEmbedding rows baseDimension columns
        (rayVector matrix label)) ''
          {label | RayAllowed first_choice label ∧ RayAllowed second_choice label}) := by
  apply PointedCone.ext
  intro point
  constructor
  · rintro ⟨first_member, second_member⟩
    obtain ⟨first_weights, first_nonnegative, first_zero, first_sum⟩ :=
      (mem_rayHull_iff matrix _ point).mp first_member
    obtain ⟨second_weights, second_nonnegative, second_zero, second_sum⟩ :=
      (mem_rayHull_iff matrix _ point).mp second_member
    have equality := normalized_ray_coefficients_unique matrix first_choice second_choice
      first_weights second_weights first_nonnegative second_nonnegative first_zero second_zero
      (first_sum.symm.trans second_sum)
    apply (mem_rayHull_iff matrix _ point).mpr
    refine ⟨first_weights, first_nonnegative, ?_, first_sum⟩
    intro label not_allowed
    by_cases first_allowed : RayAllowed first_choice label
    · rw [equality]
      exact second_zero label (fun second_allowed => not_allowed ⟨first_allowed, second_allowed⟩)
    · exact first_zero label first_allowed
  · intro member
    constructor
    · exact (Submodule.span_mono (Set.image_mono (fun _ allowed => allowed.1))) member
    · exact (Submodule.span_mono (Set.image_mono (fun _ allowed => allowed.2))) member

theorem maximalCone_inf_isFaceOf_left (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (first_choice second_choice : ConeChoice rows baseDimension columns) :
    (maximalCone matrix first_choice ⊓ maximalCone matrix second_choice).IsFaceOf
      (maximalCone matrix first_choice) := by
  rw [maximalCone_inf_eq_rayHull, maximalCone_eq_realBasisHull]
  apply BondalThomsen.basisSubsetCone_isFaceOf
  intro vector member
  obtain ⟨label, allowed, rfl⟩ := member
  have ray_member : latticeEmbedding rows baseDimension columns (rayVector matrix label) ∈
      Set.range (realConeBasis matrix first_choice) := by
    have integral_member : rayVector matrix label ∈ Set.range (coneBasis matrix first_choice) := by
      rw [← allowedRayVectors_eq_basis]
      exact ⟨label, allowed.1, rfl⟩
    obtain ⟨coordinate, equality⟩ := integral_member
    exact ⟨coordinate, (realConeBasis_apply matrix first_choice coordinate).trans
      (congrArg (latticeEmbedding rows baseDimension columns) equality)⟩
  exact ray_member

def proposedCones (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    Set (PointedCone ℝ (Ambient rows baseDimension columns)) :=
  {cone | ∃ choice : ConeChoice rows baseDimension columns, cone.IsFaceOf (maximalCone matrix choice)}

noncomputable instance coneChoiceFintype (rows baseDimension columns : ℕ) :
    Fintype (ConeChoice rows baseDimension columns) := by
  classical
  exact Fintype.ofInjective (fun choice => (choice.base, choice.fiber))
    (by intro first second equality; cases first; cases second; cases equality; rfl)

theorem proposedCones_finite (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    (proposedCones (baseDimension := baseDimension) matrix).Finite := by
  classical
  have face_finite : ∀ choice : ConeChoice rows baseDimension columns,
      Finite (maximalCone matrix choice).Face := fun choice =>
    PointedCone.FG.finite_face (maximalCone_isToricCone matrix choice).fg
  let := face_finite
  have range_finite := Set.finite_range
    (fun indexed : Σ choice : ConeChoice rows baseDimension columns,
      (maximalCone matrix choice).Face => indexed.2.toPointedCone)
  convert range_finite using 1
  ext cone
  constructor
  · rintro ⟨choice, face⟩
    exact ⟨⟨choice, ⟨cone, face⟩⟩, rfl⟩
  · rintro ⟨⟨choice, face⟩, rfl⟩
    exact ⟨choice, face.isFaceOf⟩

theorem proposedCones_isRegular (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    {cone : PointedCone ℝ (Ambient rows baseDimension columns)} (member : cone ∈ proposedCones matrix) :
    TauCeti.Toric.IsRegularCone (latticeEmbedding rows baseDimension columns) cone := by
  obtain ⟨choice, face⟩ := member
  exact (maximalCone_isRegularCone matrix choice).of_isFaceOf face

theorem proposedCones_mem_of_isFaceOf (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    {cone face : PointedCone ℝ (Ambient rows baseDimension columns)}
    (member : cone ∈ proposedCones matrix) (is_face : face.IsFaceOf cone) :
    face ∈ proposedCones matrix := by
  obtain ⟨choice, original_face⟩ := member
  exact ⟨choice, is_face.trans original_face⟩

theorem proposedCones_cover (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (point : Ambient rows baseDimension columns) :
    ∃ cone ∈ proposedCones matrix, point ∈ cone := by
  obtain ⟨choice, member⟩ := maximalCones_cover matrix point
  exact ⟨maximalCone matrix choice, ⟨choice, PointedCone.IsFaceOf.refl _⟩, member⟩

theorem proposedCones_inf_isFaceOf_left (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    {first second : PointedCone ℝ (Ambient rows baseDimension columns)}
    (first_member : first ∈ proposedCones matrix) (second_member : second ∈ proposedCones matrix) :
    (first ⊓ second).IsFaceOf first := by
  obtain ⟨first_choice, first_face⟩ := first_member
  obtain ⟨second_choice, second_face⟩ := second_member
  have intersection_face := (first_face.inf second_face).trans
    (maximalCone_inf_isFaceOf_left matrix first_choice second_choice)
  exact (intersection_face.isFaceOf_iff_le first_face).mpr inf_le_left

noncomputable def fan (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    TauCeti.Toric.Fan (latticeEmbedding rows baseDimension columns) where
  lattice := latticeEmbedding_isIntegralLattice rows baseDimension columns
  cones := proposedCones matrix
  finite_cones := proposedCones_finite matrix
  isToricCone := fun {_} member => (proposedCones_isRegular matrix member).toIsToricCone
  mem_of_isFaceOf := fun {_ _} member face => proposedCones_mem_of_isFaceOf matrix member face
  inf_isFaceOf_left := fun {_ _} first_member second_member =>
    proposedCones_inf_isFaceOf_left matrix first_member second_member

theorem fan_isComplete (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    (fan (baseDimension := baseDimension) matrix).IsComplete := by
  apply (TauCeti.Toric.Fan.isComplete_iff _).mpr
  exact proposedCones_cover matrix

theorem fan_isRegular (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    (fan (baseDimension := baseDimension) matrix).IsRegular :=
  fun {_} member => proposedCones_isRegular matrix member

theorem maximalCone_mem_fan (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (choice : ConeChoice rows baseDimension columns) :
    maximalCone matrix choice ∈ (fan matrix).cones :=
  ⟨choice, PointedCone.IsFaceOf.refl _⟩

end BondalThomsen.ProjectiveBundle
