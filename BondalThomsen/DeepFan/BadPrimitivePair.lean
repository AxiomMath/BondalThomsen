module

public import BondalThomsen.DeepFan.BadPrimitiveDirection
public import BondalThomsen.FloorClasses.TwoFloorClasses
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

namespace TauCeti.Toric.Fan

open Module Finset Set
open scoped TensorProduct

section Algebraic

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    {relation : PrimitiveLatticeRelation fan left right} {distinguished : left}
    {dimension : ℕ}

theorem PrimitiveRelationConeBasis.exists_generic_primitive_pairing
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (large_right : 2 ≤ ∑ ray : right, relation.coefficients ray) :
    ∃ pairing : Lattice →+ ℚ,
      pairing distinguished.val.val = 1 ∧
      (∀ ray : {ray : left // ray ≠ distinguished}, pairing ray.val.val.val = 0) ∧
      (∀ ray : right, 0 < pairing ray.val.val ∧ pairing ray.val.val < 1) ∧
      (∑ ray : right, (relation.coefficients ray : ℚ) * pairing ray.val.val = 1) ∧
      (∀ ray : fan.Ray, ∀ level : ℤ, pairing ray.val = level →
        (1 : ℚ) ⊗ₜ[ℤ] ray.val ∈
          Submodule.span ℚ (Set.range (fun primitive : left => (1 : ℚ) ⊗ₜ[ℤ] primitive.val.val))) := by
  classical
  obtain ⟨parameters, interval, weighted⟩ := BondalThomsen.bad_relation_parameters
    relation.coefficients large_right
  obtain ⟨center, other_values, right_values, distinguished_value⟩ :=
    cone_basis.exists_rational_pairing (fun _ => 0) parameters
  have center_distinguished : center distinguished.val.val = 1 := by
    simpa only [weighted, sum_const_zero, sub_zero] using distinguished_value
  let primitives : left → Lattice := fun ray => ray.val.val
  let outside := {ray : fan.Ray // (1 : ℚ) ⊗ₜ[ℤ] ray.val ∉
    Submodule.span ℚ (Set.range (fun primitive : left => (1 : ℚ) ⊗ₜ[ℤ] primitives primitive))}
  have nonconstant : ∀ ray : outside,
      ∃ variation : BondalThomsen.PrimitivePairingAvoidance.vanishingDirections primitives,
        variation.1 ray.val.val ≠ 0 := fun ray =>
    BondalThomsen.PrimitivePairingFiber.exists_nonzero_vanishing_of_notMem_rational_span
      primitives ray.val.val ray.property
  obtain ⟨paired, difference, paired_interval, avoids⟩ :=
    BondalThomsen.PrimitivePairingAvoidance.exists_pairing_in_fiber_avoiding_integers
      center.toIntLinearMap (BondalThomsen.PrimitivePairingAvoidance.vanishingDirections primitives)
      (fun ray : outside => ray.val.val) nonconstant (fun ray : right => ray.val.val)
      (fun _ => 0) (fun _ => 1) (by
        intro ray
        simpa only [AddMonoidHom.coe_toIntLinearMap, right_values ray] using interval ray)
  let pairing := paired.toAddMonoidHom
  have same_left : ∀ ray : left, pairing ray.val.val = center ray.val.val := by
    have zero := (BondalThomsen.PrimitivePairingAvoidance.mem_vanishingDirections primitives
      (paired - center.toIntLinearMap)).mp difference
    intro ray
    change paired ray.val.val = center ray.val.val
    exact sub_eq_zero.mp (zero ray)
  have paired_other : ∀ ray : {ray : left // ray ≠ distinguished}, pairing ray.val.val.val = 0 :=
    fun ray => (same_left ray.val).trans (other_values ray)
  have paired_weighted : ∑ ray : right, (relation.coefficients ray : ℚ) * pairing ray.val.val = 1 := by
    have relation_values := congrArg pairing relation.lattice_eq
    rw [map_sum, map_sum] at relation_values
    simp only [map_zsmul, zsmul_eq_mul, Int.cast_natCast] at relation_values
    have primitive_sum : ∑ ray : left, pairing ray.val.val = 1 := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ distinguished]
      simp only [paired_other, sum_const_zero, add_zero, same_left distinguished, center_distinguished]
    change (∑ ray : left, pairing ray.val.val) =
      ∑ ray : right, (relation.coefficients ray : ℚ) * pairing ray.val.val at relation_values
    exact relation_values.symm.trans primitive_sum
  refine ⟨pairing, (same_left distinguished).trans center_distinguished, paired_other,
    paired_interval, paired_weighted, ?_⟩
  intro ray level equality
  by_contra not_member
  exact avoids ⟨ray, not_member⟩ level equality

theorem PrimitiveRelationConeBasis.coordinate_zero_on_primitive_span
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (index : Fin dimension) (outside : index ∉ Set.range cone_basis.indices)
    (vector : Lattice)
    (member : (1 : ℚ) ⊗ₜ[ℤ] vector ∈
      Submodule.span ℚ (Set.range (fun primitive : left => (1 : ℚ) ⊗ₜ[ℤ] primitive.val.val))) :
    cone_basis.basis.repr vector index = 0 := by
  classical
  let coordinate := (cone_basis.basis.baseChange ℚ).coord index
  have off_index : ∀ selected, cone_basis.indices selected ≠ index :=
    fun selected equality => outside ⟨selected, equality⟩
  have other_zero : ∀ ray : {ray : left // ray ≠ distinguished},
      coordinate ((1 : ℚ) ⊗ₜ[ℤ] ray.val.val.val) = 0 := by
    intro ray
    rw [← cone_basis.left_eq ray]
    simp only [coordinate, Basis.coord_apply, Basis.baseChange_repr_tmul,
      Basis.repr_self_apply, off_index (Sum.inl ray), ite_false, zero_smul]
  have right_zero : ∀ ray : right, coordinate ((1 : ℚ) ⊗ₜ[ℤ] ray.val.val) = 0 := by
    intro ray
    rw [← cone_basis.right_eq ray]
    simp only [coordinate, Basis.coord_apply, Basis.baseChange_repr_tmul,
      Basis.repr_self_apply, off_index (Sum.inr ray), ite_false, zero_smul]
  have distinguished_zero : coordinate ((1 : ℚ) ⊗ₜ[ℤ] distinguished.val.val) = 0 := by
    have evaluated := congrArg coordinate relation.rational_lattice_eq
    rw [map_sum, map_sum, Fintype.sum_eq_add_sum_subtype_ne _ distinguished] at evaluated
    simpa only [other_zero, map_smul, right_zero, smul_zero, sum_const_zero, add_zero] using evaluated
  have all_zero : ∀ ray : left, coordinate ((1 : ℚ) ⊗ₜ[ℤ] ray.val.val) = 0 := by
    intro ray
    by_cases same : ray = distinguished
    · simpa only [same] using distinguished_zero
    · exact other_zero ⟨ray, same⟩
  have annihilates : Submodule.span ℚ
      (Set.range (fun primitive : left => (1 : ℚ) ⊗ₜ[ℤ] primitive.val.val)) ≤ coordinate.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ray, rfl⟩
    exact LinearMap.mem_ker.mpr (all_zero ray)
  have zero := LinearMap.mem_ker.mp (annihilates member)
  simpa only [coordinate, Basis.coord_apply, Basis.baseChange_repr_tmul,
    zsmul_eq_mul, mul_one, Int.cast_eq_zero] using zero

theorem PrimitiveRelationConeBasis.integral_ray_not_basis_generator
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (pairing : Lattice →+ ℚ)
    (right_interval : ∀ ray : right, 0 < pairing ray.val.val ∧ pairing ray.val.val < 1)
    (ray : fan.Ray) (additional : ray ∉ left) (level : ℤ) (integral : pairing ray.val = level)
    (member : (1 : ℚ) ⊗ₜ[ℤ] ray.val ∈
      Submodule.span ℚ (Set.range (fun primitive : left => (1 : ℚ) ⊗ₜ[ℤ] primitive.val.val))) :
    ray.val ∉ Set.range cone_basis.basis := by
  classical
  rintro ⟨index, generator⟩
  have selected : index ∈ Set.range cone_basis.indices := by
    by_contra outside
    have zero := cone_basis.coordinate_zero_on_primitive_span index outside ray.val member
    rw [← generator] at zero
    simp only [Basis.repr_self_apply, ite_true] at zero
    omega
  obtain ⟨selected, index_eq⟩ := selected
  rcases selected with primitive | right_ray
  · have same : ray = primitive.val.val := by
      apply Subtype.ext
      exact generator.symm.trans (by rw [← index_eq, cone_basis.left_eq])
    exact additional (same ▸ primitive.val.property)
  · have same : ray = right_ray.val := by
      apply Subtype.ext
      exact generator.symm.trans (by rw [← index_eq, cone_basis.right_eq])
    have interval := right_interval right_ray
    have integral_right : pairing right_ray.val.val = level := same ▸ integral
    rw [integral_right] at interval
    have positive : (0 : ℤ) < level := by exact_mod_cast interval.1
    have small : level < (1 : ℤ) := by exact_mod_cast interval.2
    omega

end Algebraic

section FloorClasses

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {fan : TauCeti.Toric.Fan embedding}
    {left right : Finset fan.Ray} [DecidableEq fan.Ray]

theorem PrimitiveLatticeRelation.exists_two_distinct_floorClasses_of_dropOne_support
    (relation : PrimitiveLatticeRelation fan left right) (complete : fan.IsComplete)
    {dimension : ℕ}
    (drop_one : ∀ primitive : left, PrimitiveRelationConeBasis relation primitive dimension)
    (large_right : 2 ≤ ∑ ray : right, relation.coefficients ray)
    (positive_degree : (∑ ray : right, relation.coefficients ray : ℕ) < Fintype.card left)
    (strict_support : ∀ primitive : left, ∀ ray : fan.Ray,
      ray.val ∉ Set.range (drop_one primitive).basis →
        (-1 : ℚ) < (drop_one primitive).anticanonicalDatum ray.val) :
    ∃ distinguished : left, ∃ pairing : Lattice →+ ℚ, ∃ parameter : ℚ,
      0 < parameter ∧
      pairing distinguished.val.val = 1 ∧
      (∀ ray : {ray : left // ray ≠ distinguished}, pairing ray.val.val.val = 0) ∧
      (∀ ray : right, 0 < pairing ray.val.val ∧ pairing ray.val.val < 1) ∧
      fan.floorRayDivisor (pairing + parameter • (drop_one distinguished).badDirection) -
          fan.floorRayDivisor pairing =
        fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ left then -1 else 0) ∧
      fan.floorRayDivisorClass (pairing + parameter • (drop_one distinguished).badDirection) ≠
        fan.floorRayDivisorClass pairing := by
  classical
  obtain ⟨primitive, member⟩ := relation.primitive_collection.1
  let distinguished : left := ⟨primitive, member⟩
  let cone_basis := drop_one distinguished
  obtain ⟨pairing, distinguished_value, other_values, right_interval, _, integral_span⟩ :=
    cone_basis.exists_generic_primitive_pairing large_right
  have positive_sum : 0 < ∑ ray : right, relation.coefficients ray := by omega
  have prescribed_integral : ∀ ray ∈ left, Int.fract (pairing ray.val) = 0 := by
    intro ray member
    by_cases same : (⟨ray, member⟩ : left) = distinguished
    · have value : pairing ray.val = 1 := by
        simpa only [← same] using distinguished_value
      simp only [value, Int.fract_one]
    · rw [other_values ⟨⟨ray, member⟩, same⟩, Int.fract_zero]
  have prescribed_direction : ∀ ray ∈ left, cone_basis.badDirection ray.val = -1 :=
    fun ray member => cone_basis.badDirection_left positive_sum ⟨ray, member⟩
  have other_direction : ∀ ray ∉ left, Int.fract (pairing ray.val) = 0 →
      0 ≤ cone_basis.badDirection ray.val := by
    intro ray additional integral
    obtain ⟨level, level_eq⟩ := Int.fract_eq_zero_iff.mp integral
    have paired_level : pairing ray.val = level := level_eq.symm
    have rational_member := integral_span ray level paired_level
    apply cone_basis.badDirection_nonnegative_of_dropOne_support positive_sum positive_degree
      drop_one ray.val rational_member
    intro primitive
    exact strict_support primitive ray
      ((drop_one primitive).integral_ray_not_basis_generator pairing right_interval ray
        additional level paired_level rational_member)
  obtain ⟨parameter, positive, difference, different⟩ :=
    fan.exists_two_distinct_floorRayDivisorClasses complete pairing cone_basis.badDirection
      left relation.primitive_collection.1 prescribed_integral prescribed_direction other_direction
  exact ⟨distinguished, pairing, parameter, positive, distinguished_value, other_values,
    right_interval, difference, different⟩

end FloorClasses

end TauCeti.Toric.Fan
