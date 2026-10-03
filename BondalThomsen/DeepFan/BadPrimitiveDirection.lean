module

public import BondalThomsen.Fan.PrimitiveRelationBasis
public import BondalThomsen.Fan.PrimitivePairingFiber

@[expose] public section

namespace TauCeti.Toric.Fan

open Module Finset Set
open scoped TensorProduct

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    {relation : PrimitiveLatticeRelation fan left right} {distinguished : left}
    {dimension : ℕ}

def PrimitiveLatticeRelation.badRightValue (relation : PrimitiveLatticeRelation fan left right) : ℚ :=
  -(Fintype.card left : ℚ) / (∑ ray : right, relation.coefficients ray : ℕ)

noncomputable def PrimitiveRelationConeBasis.badDirection
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension) : Lattice →+ ℚ :=
  (cone_basis.basis.constr ℚ (Function.extend cone_basis.indices
    (Sum.elim (fun _ => (-1 : ℚ)) (fun _ => relation.badRightValue)) (fun _ => (0 : ℚ)))).toAddMonoidHom

theorem PrimitiveRelationConeBasis.badDirection_other
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (ray : {ray : left // ray ≠ distinguished}) :
    cone_basis.badDirection ray.val.val.val = -1 := by
  rw [← cone_basis.left_eq ray]
  change (cone_basis.basis.constr ℚ _)
    (cone_basis.basis (cone_basis.indices (Sum.inl ray))) = -1
  rw [Basis.constr_basis]
  exact congrFun (Function.extend_comp cone_basis.indices.injective _ _) (Sum.inl ray)

theorem PrimitiveRelationConeBasis.badDirection_right
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension) (ray : right) :
    cone_basis.badDirection ray.val.val = relation.badRightValue := by
  rw [← cone_basis.right_eq ray]
  change (cone_basis.basis.constr ℚ _)
    (cone_basis.basis (cone_basis.indices (Sum.inr ray))) = relation.badRightValue
  rw [Basis.constr_basis]
  exact congrFun (Function.extend_comp cone_basis.indices.injective _ _) (Sum.inr ray)

theorem PrimitiveLatticeRelation.badRightValue_weighted_sum
    (relation : PrimitiveLatticeRelation fan left right)
    (positive_sum : 0 < ∑ ray : right, relation.coefficients ray) :
    ∑ ray : right, (relation.coefficients ray : ℚ) * relation.badRightValue =
      -(Fintype.card left : ℚ) := by
  rw [← sum_mul, ← Nat.cast_sum]
  have nonzero : (∑ ray : right, relation.coefficients ray : ℚ) ≠ 0 := by
    rw [← Nat.cast_sum]
    exact_mod_cast Nat.ne_of_gt positive_sum
  unfold PrimitiveLatticeRelation.badRightValue
  field_simp [nonzero]

theorem PrimitiveRelationConeBasis.badDirection_distinguished
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (positive_sum : 0 < ∑ ray : right, relation.coefficients ray) :
    cone_basis.badDirection distinguished.val.val = -1 := by
  classical
  have paired := congrArg cone_basis.badDirection relation.lattice_eq
  have weighted := relation.badRightValue_weighted_sum positive_sum
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_natCast,
    cone_basis.badDirection_right, weighted] at paired
  rw [Fintype.sum_eq_add_sum_subtype_ne _ distinguished] at paired
  simp only [cone_basis.badDirection_other, sum_const, card_univ, nsmul_eq_mul] at paired
  have left_nonempty : Nonempty left := ⟨distinguished⟩
  have card_positive : 0 < Fintype.card left := Fintype.card_pos
  have other_card : Fintype.card {ray : left // ray ≠ distinguished} = Fintype.card left - 1 := by
    simp
  rw [other_card] at paired
  have card_cast : ((Fintype.card left - 1 : ℕ) : ℚ) = Fintype.card left - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [card_cast] at paired
  linarith

theorem PrimitiveRelationConeBasis.badDirection_left
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (positive_sum : 0 < ∑ ray : right, relation.coefficients ray) (ray : left) :
    cone_basis.badDirection ray.val.val = -1 := by
  by_cases same : ray = distinguished
  · subst ray
    exact cone_basis.badDirection_distinguished positive_sum
  · exact cone_basis.badDirection_other ⟨ray, same⟩

theorem PrimitiveLatticeRelation.rational_lattice_eq
    (relation : PrimitiveLatticeRelation fan left right) :
    (∑ ray : left, (1 : ℚ) ⊗ₜ[ℤ] ray.val.val) =
      ∑ ray : right, (relation.coefficients ray : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] ray.val.val) := by
  have mapped := congrArg ((TensorProduct.mk ℤ ℚ Lattice) 1) relation.lattice_eq
  simpa only [map_sum, map_smul, TensorProduct.mk_apply, TensorProduct.tmul_smul,
    ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast] using mapped

noncomputable def PrimitiveRelationConeBasis.anticanonicalDatum
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension) : Lattice →+ ℤ :=
  -cone_basis.basis.sumCoords.toAddMonoidHom

theorem PrimitiveRelationConeBasis.anticanonicalDatum_basis
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension) (index : Fin dimension) :
    cone_basis.anticanonicalDatum (cone_basis.basis index) = -1 := by
  simp [PrimitiveRelationConeBasis.anticanonicalDatum]

theorem PrimitiveRelationConeBasis.anticanonicalDatum_eq
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (vector : Lattice) (weights : left → ℚ)
    (expansion : (1 : ℚ) ⊗ₜ[ℤ] vector =
      ∑ ray : left, weights ray • ((1 : ℚ) ⊗ₜ[ℤ] ray.val.val)) :
    (cone_basis.anticanonicalDatum vector : ℚ) =
      -(∑ ray : left, weights ray) +
        ((Fintype.card left : ℚ) - (∑ ray : right, relation.coefficients ray : ℕ)) *
          weights distinguished := by
  classical
  let datum : Lattice →+ ℚ := (Int.castAddHom ℚ).comp cone_basis.anticanonicalDatum
  let rational_datum := datum.toIntLinearMap.liftBaseChange ℚ
  have other_values : ∀ ray : {ray : left // ray ≠ distinguished}, datum ray.val.val.val = -1 := by
    intro ray
    rw [← cone_basis.left_eq ray]
    change (cone_basis.anticanonicalDatum (cone_basis.basis _) : ℚ) = -1
    rw [cone_basis.anticanonicalDatum_basis]
    norm_num
  have right_values : ∀ ray : right, datum ray.val.val = -1 := by
    intro ray
    rw [← cone_basis.right_eq ray]
    change (cone_basis.anticanonicalDatum (cone_basis.basis _) : ℚ) = -1
    rw [cone_basis.anticanonicalDatum_basis]
    norm_num
  have other_card : (Fintype.card {ray : left // ray ≠ distinguished} : ℚ) =
      (Fintype.card left : ℚ) - 1 := by
    have : Nonempty left := ⟨distinguished⟩
    have positive : 0 < Fintype.card left := Fintype.card_pos
    have natural_eq : Fintype.card {ray : left // ray ≠ distinguished} = Fintype.card left - 1 := by
      simp
    rw [natural_eq, Nat.cast_sub (by omega)]
    norm_num
  have distinguished_value : datum distinguished.val.val =
      (Fintype.card left : ℚ) - (∑ ray : right, relation.coefficients ray : ℕ) - 1 := by
    have paired := congrArg datum relation.lattice_eq
    simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_natCast, right_values,
      mul_neg_one, sum_neg_distrib, ← Nat.cast_sum] at paired
    rw [Fintype.sum_eq_add_sum_subtype_ne _ distinguished] at paired
    simp only [other_values, sum_const, card_univ, nsmul_eq_mul, other_card] at paired
    linarith
  have value : (cone_basis.anticanonicalDatum vector : ℚ) =
      ∑ ray : left, weights ray * datum ray.val.val := by
    change datum vector = _
    have evaluated := congrArg rational_datum expansion
    simpa only [rational_datum, map_sum, map_smul,
      LinearMap.liftBaseChange_one_tmul, smul_eq_mul, AddMonoidHom.coe_toIntLinearMap] using evaluated
  rw [value, Fintype.sum_eq_add_sum_subtype_ne _ distinguished, distinguished_value]
  have other_sum : ∑ ray : {ray : left // ray ≠ distinguished},
      weights ray.val * datum ray.val.val.val =
      -(∑ ray : {ray : left // ray ≠ distinguished}, weights ray.val) := by
    simp only [other_values, mul_neg_one, sum_neg_distrib]
  rw [other_sum, Fintype.sum_eq_add_sum_subtype_ne (fun ray : left => weights ray) distinguished]
  ring

theorem PrimitiveRelationConeBasis.badDirection_nonnegative_of_dropOne_support
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (positive_sum : 0 < ∑ ray : right, relation.coefficients ray)
    (positive_degree : (∑ ray : right, relation.coefficients ray : ℕ) < Fintype.card left)
    (drop_one : ∀ ray : left, PrimitiveRelationConeBasis relation ray dimension)
    (vector : Lattice)
    (member : (1 : ℚ) ⊗ₜ[ℤ] vector ∈
      Submodule.span ℚ (Set.range (fun ray : left => (1 : ℚ) ⊗ₜ[ℤ] ray.val.val)))
    (strict_support : ∀ ray : left, (-1 : ℚ) < (drop_one ray).anticanonicalDatum vector) :
    0 ≤ cone_basis.badDirection vector := by
  classical
  obtain ⟨weights, expansion⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp member
  have support_eq := fun ray : left =>
    (drop_one ray).anticanonicalDatum_eq vector weights expansion.symm
  have support_nonnegative : ∀ ray : left, 0 ≤ (drop_one ray).anticanonicalDatum vector := by
    intro ray
    have bound : (-1 : ℤ) < (drop_one ray).anticanonicalDatum vector := by
      exact_mod_cast strict_support ray
    omega
  have inequalities : ∀ ray : left,
      (∑ other : left, (weights other : ℝ)) -
        ((Fintype.card left : ℝ) - (∑ other : right, relation.coefficients other : ℕ)) *
          (weights ray : ℝ) ≤ 0 := by
    intro ray
    have bounded : (∑ other : left, weights other) -
        ((Fintype.card left : ℚ) - (∑ other : right, relation.coefficients other : ℕ)) *
          weights ray ≤ 0 := by
      have nonnegative : (0 : ℚ) ≤ (drop_one ray).anticanonicalDatum vector := by
        exact_mod_cast support_nonnegative ray
      rw [support_eq ray] at nonnegative
      linarith
    exact_mod_cast bounded
  have degree_positive : 0 < (Fintype.card left : ℝ) -
      (∑ ray : right, relation.coefficients ray : ℕ) := by
    have : ((∑ ray : right, relation.coefficients ray : ℕ) : ℝ) < Fintype.card left := by
      exact_mod_cast positive_degree
    linarith
  have degree_small : (Fintype.card left : ℝ) -
      (∑ ray : right, relation.coefficients ray : ℕ) < Fintype.card left := by
    have : (0 : ℝ) < (∑ ray : right, relation.coefficients ray : ℕ) := by
      exact_mod_cast positive_sum
    linarith
  have total_nonpositive := BondalThomsen.primitive_span_sum_nonpositive
    (fun ray : left => (weights ray : ℝ))
    ((Fintype.card left : ℝ) - (∑ ray : right, relation.coefficients ray : ℕ))
      degree_positive degree_small inequalities
  have rational_nonpositive : (∑ ray : left, weights ray) ≤ 0 := by
    exact_mod_cast total_nonpositive
  have motion_value : cone_basis.badDirection vector = -(∑ ray : left, weights ray) := by
    have evaluated := congrArg (cone_basis.badDirection.toIntLinearMap.liftBaseChange ℚ) expansion
    simpa only [map_sum, map_smul, LinearMap.liftBaseChange_one_tmul,
      AddMonoidHom.coe_toIntLinearMap, cone_basis.badDirection_left positive_sum,
      smul_eq_mul, mul_neg_one, sum_neg_distrib] using
        evaluated.symm
  rw [motion_value]
  exact neg_nonneg.mpr rational_nonpositive

end TauCeti.Toric.Fan
