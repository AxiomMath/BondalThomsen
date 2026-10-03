module

public import BondalThomsen.Matroid.RootMatroid
public import BondalThomsen.Fan.FanoBound
public import BondalThomsen.Fan.FanRootObstruction
public import BondalThomsen.Ports.Matroid.IsomorphismRank
public import BondalThomsen.Matroid.MinorTransport
public import BondalThomsen.Matroid.K4RepresentationUniqueness

@[expose] public section

open Module Set BondalThomsen

namespace BondalThomsen

def k4GroundEquiv : Fin 6 ≃ k4Matroid.E where
  toFun edge := ⟨edge, by simp⟩
  invFun edge := edge.val
  left_inv _ := rfl
  right_inv _ := rfl

def k4RestrictionLabels {Label : Type*} {smaller : Matroid Label}
    (isomorphism : Matroid.Iso k4Matroid smaller) : Fin 6 ≃ smaller.E :=
  k4GroundEquiv.trans isomorphism.toEquiv

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem simpleRestriction_directions_injective (fan : TauCeti.Toric.Fan embedding)
    {smaller : Matroid fan.Ray} (restriction : smaller.IsRestriction fan.rayMatroid)
    (simple : smaller.Simple) :
    Function.Injective (fun element : smaller.E => fan.toRayDirection element.val) := by
  intro first second equality
  have parallel : fan.rayMatroid.Parallel first.val second.val :=
    (fan.rayMatroid_parallel_iff_direction_eq _ _).mpr (congrArg Subtype.val equality)
  have pair := Matroid.simple_iff_forall_pair_indep.mp simple
    first.val second.val first.property second.property
  apply Subtype.ext
  exact (Matroid.parallel_iff_isNonloop_isNonloop_indep_imp_eq.mp parallel).2.2
    (restriction.indep_iff.mp pair).1

theorem six_simpleRestriction_exhausts_rays (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep 3)
    (reference : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (restriction : smaller.IsRestriction fan.rayMatroid) (simple : smaller.Simple)
    (cardinality : Nat.card smaller.E = 6) (ray : fan.Ray) :
    ∃ selected : smaller.E, ray.val = selected.val.val ∨ ray.val = -selected.val.val := by
  have injective := fan.simpleRestriction_directions_injective restriction simple
  have bijective := injective.bijective_of_nat_card_le (by
    rw [cardinality]
    exact fan.ray_directions_card_le_six complete regular deep reference)
  obtain ⟨selected, equality⟩ := bijective.2 (fan.toRayDirection ray)
  have directions : fan.rayDirection ray = fan.rayDirection selected.val :=
    (congrArg Subtype.val equality).symm
  exact ⟨selected, (TauCeti.Slope.mk_eq_mk_iff ray.property.1 selected.val.property.1).mp directions⟩

def k4SelectedRays (fan : TauCeti.Toric.Fan embedding) {smaller : Matroid fan.Ray}
    (isomorphism : Matroid.Iso k4Matroid smaller) : Fin 6 → fan.Ray :=
  fun edge => (k4RestrictionLabels isomorphism edge).val

noncomputable def k4SelectedMatrix (fan : TauCeti.Toric.Fan embedding)
    (basis : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (isomorphism : Matroid.Iso k4Matroid smaller) : Matrix (Fin 3) (Fin 6) ℤ :=
  (fan.rayMatrix basis).submatrix id (fan.k4SelectedRays isomorphism)

omit [FiniteDimensional ℝ Ambient] in

theorem k4SelectedMatrix_matroid (fan : TauCeti.Toric.Fan embedding)
    (basis : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (restriction : smaller.IsRestriction fan.rayMatroid)
    (isomorphism : Matroid.Iso k4Matroid smaller) :
    BondalThomsen.rayMatroid (Field := ℚ)
      (fun edge row => (fan.k4SelectedMatrix basis isomorphism row edge : ℚ)) = k4Matroid := by
  apply Matroid.ext_indep (by simp)
  intro selected _
  have source_image : Subtype.val '' (k4GroundEquiv '' selected) = selected := by
    ext edge
    simp [k4GroundEquiv]
  have target_image : Subtype.val ''
      (isomorphism.toEquiv '' (k4GroundEquiv '' selected)) =
        fan.k4SelectedRays isomorphism '' selected := by
    simp only [Set.image_image]
    rfl
  have transfer := isomorphism.indep_image_iff' (k4GroundEquiv '' selected)
  rw [source_image, target_image, restriction.indep_iff] at transfer
  have contained : fan.k4SelectedRays isomorphism '' selected ⊆ smaller.E := by
    rintro _ ⟨edge, _, rfl⟩
    exact (k4RestrictionLabels isomorphism edge).property
  rw [and_iff_left contained, fan.rayMatroid_eq_coordinates basis, BondalThomsen.rayMatroid_indep_iff]
    at transfer
  rw [BondalThomsen.rayMatroid_indep_iff]
  have injective : Function.Injective (fan.k4SelectedRays isomorphism) :=
    Subtype.val_injective.comp (k4RestrictionLabels isomorphism).injective
  constructor
  · intro independent
    apply transfer.mpr
    exact independent.image_of_comp (fan.k4SelectedRays isomorphism)
      (fun ray row => (basis.repr ray.val row : ℚ))
  · intro independent
    exact ((transfer.mp independent).comp_of_image injective.injOn)

noncomputable def realMatrixUnit (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 3))
    ((operation : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℝ)) (by
      have determinant_cast :
          ((operation : Matrix (Fin 3) (Fin 3) ℤ).det : ℝ) =
            ((operation : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℝ)).det :=
        (Int.castRingHom ℝ).map_det _
      rw [← determinant_cast]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp operation.isUnit).map (Int.castRingHom ℝ))

theorem realMatrixUnit_apply (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ)
    (vector : Fin 3 → ℝ) :
    realMatrixUnit operation vector =
      ((operation : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℝ)).mulVec vector := by
  simp [realMatrixUnit, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

noncomputable def k4RootCoordinates (fan : TauCeti.Toric.Fan embedding)
    (basis : Basis (Fin 3) ℤ Lattice) (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) :
    Ambient →ₗ[ℝ] (Fin 4 → ℝ) :=
  (k4RootLift ℝ).comp ((realMatrixUnit operation).symm.toLinearMap.comp
    (fan.lattice.isBaseChange.basis basis).equivFun.toLinearMap)

omit [FiniteDimensional ℝ Ambient] in
theorem k4RootCoordinates_injective (fan : TauCeti.Toric.Fan embedding)
    (basis : Basis (Fin 3) ℤ Lattice) (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) :
    Function.Injective (fan.k4RootCoordinates basis operation) :=
  (k4RootLift_injective ℝ).comp
    ((realMatrixUnit operation).symm.injective.comp
      (fan.lattice.isBaseChange.basis basis).equivFun.injective)

omit [FiniteDimensional ℝ Ambient] in

theorem k4RootCoordinates_selected (fan : TauCeti.Toric.Fan embedding)
    (basis : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (isomorphism : Matroid.Iso k4Matroid smaller)
    (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) (signs : Fin 6 → ℤ)
    (equality : fan.k4SelectedMatrix basis isomorphism =
      (operation : Matrix (Fin 3) (Fin 3) ℤ) * k4RootMatrix ℤ * Matrix.diagonal signs)
    (edge : Fin 6) :
    fan.k4RootCoordinates basis operation (embedding (fan.k4SelectedRays isomorphism edge).val) =
      (signs edge : ℝ) • directedRoot (k4EdgeSource edge) (k4EdgeTarget edge) := by
  have basis_coordinates : (fan.lattice.isBaseChange.basis basis).equivFun
      (embedding (fan.k4SelectedRays isomorphism edge).val) =
        fun row => (fan.k4SelectedMatrix basis isomorphism row edge : ℝ) := by
    ext row
    rw [Basis.equivFun_apply]
    exact fan.lattice.isBaseChange.basis_repr_comp_apply basis
      (fan.k4SelectedRays isomorphism edge).val row
  have selected_coordinates : (fun row => (fan.k4SelectedMatrix basis isomorphism row edge : ℝ)) =
      realMatrixUnit operation ((signs edge : ℝ) • (k4RootMatrix ℝ).col edge) := by
    ext row
    have entry := congrFun (congrFun equality row) edge
    rw [Matrix.mul_diagonal, Matrix.mul_apply] at entry
    rw [realMatrixUnit_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
      Matrix.map_apply]
    rw [entry, Int.cast_mul, Int.cast_sum]
    simp only [Int.cast_mul]
    have cast_root : ∀ index, (k4RootMatrix ℤ index edge : ℝ) = k4RootMatrix ℝ index edge := by
      intro index
      fin_cases index <;> fin_cases edge <;> norm_num [k4RootMatrix]
    simp_rw [cast_root]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index _
    change ((operation : Matrix (Fin 3) (Fin 3) ℤ) row index : ℝ) *
      k4RootMatrix ℝ index edge * (signs edge : ℝ) =
      ((operation : Matrix (Fin 3) (Fin 3) ℤ) row index : ℝ) *
        ((signs edge : ℝ) * k4RootMatrix ℝ index edge)
    ring
  change k4RootLift ℝ ((realMatrixUnit operation).symm
    ((fan.lattice.isBaseChange.basis basis).equivFun
      (embedding (fan.k4SelectedRays isomorphism edge).val))) = _
  rw [basis_coordinates, selected_coordinates, LinearEquiv.symm_apply_apply, map_smul,
    k4RootLift_column]

theorem k4RootCoordinates_all_rays (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep 3)
    (reference basis : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (restriction : smaller.IsRestriction fan.rayMatroid)
    (isomorphism : Matroid.Iso k4Matroid smaller)
    (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) (signs : Fin 6 → ℤ)
    (signed : ∀ edge, signs edge = 1 ∨ signs edge = -1)
    (equality : fan.k4SelectedMatrix basis isomorphism =
      (operation : Matrix (Fin 3) (Fin 3) ℤ) * k4RootMatrix ℤ * Matrix.diagonal signs)
    (ray : fan.Ray) :
    ∃ edge, fan.k4RootCoordinates basis operation (embedding ray.val) =
        directedRoot (k4EdgeSource edge) (k4EdgeTarget edge) ∨
      fan.k4RootCoordinates basis operation (embedding ray.val) =
        -directedRoot (k4EdgeSource edge) (k4EdgeTarget edge) := by
  have cardinality : Nat.card smaller.E = 6 := by
    rw [← Nat.card_congr (k4RestrictionLabels isomorphism)]
    simp
  obtain ⟨selected, same | opposite⟩ := fan.six_simpleRestriction_exhausts_rays
    complete regular deep reference restriction (isomorphism.simple k4Matroid_simple) cardinality ray
  · obtain ⟨edge, rfl⟩ := (k4RestrictionLabels isomorphism).surjective selected
    have normalized := fan.k4RootCoordinates_selected basis isomorphism operation signs equality edge
    refine ⟨edge, ?_⟩
    rw [same]
    rcases signed edge with positive | negative
    · left
      simpa [positive, k4SelectedRays] using normalized
    · right
      simpa [negative, k4SelectedRays] using normalized
  · obtain ⟨edge, rfl⟩ := (k4RestrictionLabels isomorphism).surjective selected
    have normalized := fan.k4RootCoordinates_selected basis isomorphism operation signs equality edge
    refine ⟨edge, ?_⟩
    rw [opposite, map_neg, map_neg]
    rcases signed edge with positive | negative
    · right
      simpa [positive, k4SelectedRays] using congrArg Neg.neg normalized
    · left
      simpa [negative, k4SelectedRays] using congrArg Neg.neg normalized

def k4AvailableRootGraph (fan : TauCeti.Toric.Fan embedding)
    (basis : Basis (Fin 3) ℤ Lattice) (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) :
    Digraph (Fin 4) where
  Adj source target := ∃ ray : fan.Ray,
    fan.k4RootCoordinates basis operation (embedding ray.val) = directedRoot source target

omit [FiniteDimensional ℝ Ambient] in

theorem k4AvailableRootGraph_semicomplete (fan : TauCeti.Toric.Fan embedding)
    (basis : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (isomorphism : Matroid.Iso k4Matroid smaller)
    (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) (signs : Fin 6 → ℤ)
    (signed : ∀ edge, signs edge = 1 ∨ signs edge = -1)
    (equality : fan.k4SelectedMatrix basis isomorphism =
      (operation : Matrix (Fin 3) (Fin 3) ℤ) * k4RootMatrix ℤ * Matrix.diagonal signs) :
    DigraphSemicomplete (fan.k4AvailableRootGraph basis operation) := by
  intro source target distinct
  obtain ⟨edge, forward | backward⟩ := k4Edge_endpoints_exhaustive source target distinct
  · have normalized := fan.k4RootCoordinates_selected basis isomorphism operation signs equality edge
    rw [forward.1, forward.2] at normalized
    rcases signed edge with positive | negative
    · exact Or.inl ⟨fan.k4SelectedRays isomorphism edge, by simpa [positive] using normalized⟩
    · refine Or.inr ⟨fan.k4SelectedRays isomorphism edge, ?_⟩
      have reverse : -directedRoot source target = directedRoot target source := by
        simp [directedRoot]
      simpa [negative, reverse] using normalized
  · have normalized := fan.k4RootCoordinates_selected basis isomorphism operation signs equality edge
    rw [backward.1, backward.2] at normalized
    rcases signed edge with positive | negative
    · exact Or.inr ⟨fan.k4SelectedRays isomorphism edge, by simpa [positive] using normalized⟩
    · refine Or.inl ⟨fan.k4SelectedRays isomorphism edge, ?_⟩
      have reverse : -directedRoot target source = directedRoot source target := by
        simp [directedRoot]
      simpa [negative, reverse] using normalized

theorem k4RootCoordinates_configuration (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep 3)
    (reference basis : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (restriction : smaller.IsRestriction fan.rayMatroid)
    (isomorphism : Matroid.Iso k4Matroid smaller)
    (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) (signs : Fin 6 → ℤ)
    (signed : ∀ edge, signs edge = 1 ∨ signs edge = -1)
    (equality : fan.k4SelectedMatrix basis isomorphism =
      (operation : Matrix (Fin 3) (Fin 3) ℤ) * k4RootMatrix ℤ * Matrix.diagonal signs) :
    fan.k4RootCoordinates basis operation '' fan.rayGenerators =
      digraphRoots (fan.k4AvailableRootGraph basis operation) := by
  ext vector
  constructor
  · rintro ⟨_, ⟨ray, rfl⟩, rfl⟩
    obtain ⟨edge, forward | backward⟩ := fan.k4RootCoordinates_all_rays complete regular deep
      reference basis restriction isomorphism operation signs signed equality ray
    · exact ⟨k4EdgeSource edge, k4EdgeTarget edge, ⟨ray, forward⟩, forward⟩
    · have reverse : -directedRoot (k4EdgeSource edge) (k4EdgeTarget edge) =
          directedRoot (k4EdgeTarget edge) (k4EdgeSource edge) := by simp [directedRoot]
      rw [reverse] at backward
      exact ⟨k4EdgeTarget edge, k4EdgeSource edge, ⟨ray, backward⟩, backward⟩
  · rintro ⟨source, target, ⟨ray, root⟩, rfl⟩
    exact ⟨embedding ray.val, ⟨ray, rfl⟩, root⟩

theorem no_k4Restriction_of_integral_equivalence (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep 3)
    (reference basis : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (restriction : smaller.IsRestriction fan.rayMatroid)
    (isomorphism : Matroid.Iso k4Matroid smaller)
    (operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) (signs : Fin 6 → ℤ)
    (signed : ∀ edge, signs edge = 1 ∨ signs edge = -1)
    (equality : fan.k4SelectedMatrix basis isomorphism =
      (operation : Matrix (Fin 3) (Fin 3) ℤ) * k4RootMatrix ℤ * Matrix.diagonal signs) : False := by
  let real_basis := fan.lattice.isBaseChange.basis reference
  let : Nontrivial Ambient :=
    real_basis.equivFun.symm.injective.nontrivial
  exact fan.not_semicomplete_rootConfiguration complete regular deep reference
    (fan.k4AvailableRootGraph basis operation)
    (fan.k4AvailableRootGraph_semicomplete basis isomorphism operation signs signed equality)
    (fan.k4RootCoordinates basis operation) (fan.k4RootCoordinates_injective basis operation)
    (fan.k4RootCoordinates_configuration complete regular deep reference basis restriction
      isomorphism operation signs signed equality)

end TauCeti.Toric.Fan
