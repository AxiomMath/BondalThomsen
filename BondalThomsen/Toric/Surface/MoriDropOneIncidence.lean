module

public import BondalThomsen.Fan.WallGeometry
public import BondalThomsen.Fan.PrimitiveRelationBasis
public import BondalThomsen.Toric.Positivity.WallCurveDegree
public import BondalThomsen.Toric.Positivity.SupportConcavity
public import BondalThomsen.Toric.Surface.WallRestrictionDescent

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Set
open TauCeti.AlgebraicGeometry

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance surfaceRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

theorem exists_coneBasis_across_facet_without_deep
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (removed : Fin dimension) :
    ∃ adjacent : Basis (Fin dimension) ℤ Lattice,
      fan.IsConeBasis adjacent ∧
      (∀ index, index ≠ removed → adjacent index = basis index) ∧
      (basis.repr (adjacent removed) removed = -1) ∧
      ∀ vector : Lattice, adjacent.repr vector removed = -basis.repr vector removed := by
  classical
  obtain ⟨adapted, adapted_cone, facet_member, point, point_member, negative⟩ :=
    fan.exists_basis_across_facet complete regular basis removed
  let original_cone := PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))
  let adapted_hull := PointedCone.hull ℝ (Set.range (fun index => embedding (adapted index)))
  let coefficients := fun index : Fin dimension => if index = removed then (0 : ℝ) else 1
  have original_generators : ∀ index, embedding (basis index) ∈ original_cone :=
    fun index => PointedCone.subset_hull ⟨index, rfl⟩
  have facet_original : ∑ index, coefficients index • embedding (basis index) ∈ original_cone :=
    Submodule.sum_mem _ fun index _ => PointedCone.smul_mem _
      (by simp only [coefficients]; split_ifs <;> norm_num) (original_generators index)
  have shared : ∀ index, index ≠ removed → embedding (basis index) ∈ adapted_hull := by
    intro index distinct
    exact ((fan.inf_isFaceOf_left cone_basis adapted_cone).mem_of_sum_smul_mem
      original_generators (fun index => by simp only [coefficients]; split_ifs <;> norm_num)
      ⟨facet_original, facet_member⟩ index (by simp [coefficients, distinct])).2
  have generator_match : ∀ index : {index : Fin dimension // index ≠ removed},
      ∃ row, basis index.val = adapted row := by
    intro index
    obtain ⟨row, same⟩ := fan.ray_eq_basis_of_mem_coneBasis adapted adapted_cone
      (fan.basisRay basis cone_basis index.val) (shared index.val index.property)
    exact ⟨row, same.symm⟩
  choose matching matched using generator_match
  have matching_injective : Function.Injective matching := by
    intro first second same
    apply Subtype.ext
    apply basis.injective
    rw [matched, matched, same]
  obtain ⟨permutation, extends_matching⟩ := Cardinal.extend_function_finite
    (⟨matching, matching_injective⟩ : {index : Fin dimension | index ≠ removed} ↪ Fin dimension)
    (show Nonempty (Fin dimension ≃ Fin dimension) from ⟨Equiv.refl _⟩)
  let adjacent := adapted.reindex permutation.symm
  have shared_basis : ∀ index, index ≠ removed → adjacent index = basis index := by
    intro index distinct
    change adapted.reindex permutation.symm index = basis index
    rw [Basis.reindex_apply]
    change adapted (permutation index) = basis index
    rw [extends_matching ⟨index, distinct⟩]
    exact (matched ⟨index, distinct⟩).symm
  have ranges : Set.range (fun index => embedding (adjacent index)) =
      Set.range (fun index => embedding (adapted index)) := by
    change Set.range (embedding ∘ adjacent) = Set.range (embedding ∘ adapted)
    rw [Set.range_comp, Set.range_comp]
    congr 1
    exact Basis.range_reindex adapted permutation.symm
  have adjacent_cone : fan.IsConeBasis adjacent := by
    change PointedCone.hull ℝ (Set.range (fun index => embedding (adjacent index))) ∈ fan.cones
    rw [ranges]
    exact adapted_cone
  have coordinate_others : ∀ index, index ≠ removed →
      basis.repr (adjacent index) removed = 0 := by
    intro index distinct
    rw [shared_basis index distinct]
    simp [distinct]
  have coordinate_formula : ∀ vector : Lattice,
      basis.repr vector removed = adjacent.repr vector removed *
        basis.repr (adjacent removed) removed := by
    intro vector
    conv_lhs => rw [← adjacent.sum_repr vector]
    rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single removed]
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro index _ distinct
      simp [map_smul, coordinate_others index distinct]
    · simp
  have unit_coefficient : IsUnit (basis.repr (adjacent removed) removed) := by
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨adjacent.repr (basis removed) removed, ?_⟩
    simpa using (coordinate_formula (basis removed)).symm
  have coefficient_neg : basis.repr (adjacent removed) removed < 0 := by
    let real_original := fan.lattice.isBaseChange.basis basis
    let real_adjacent := fan.lattice.isBaseChange.basis adjacent
    have point_nonnegative : ∀ index, 0 ≤ real_adjacent.repr point index := by
      apply (BondalThomsen.mem_basisCone_iff real_adjacent point).mp
      have point_adjacent : point ∈ PointedCone.hull ℝ
          (Set.range (fun index => embedding (adjacent index))) := by
        rwa [ranges]
      convert point_adjacent using 1
      congr 1
      ext vector
      simp only [Set.mem_range]
      constructor <;> rintro ⟨index, rfl⟩ <;> refine ⟨index, ?_⟩
      · exact (fan.lattice.isBaseChange.basis_apply adjacent index).symm
      · exact fan.lattice.isBaseChange.basis_apply adjacent index
    have real_formula : real_original.repr point removed =
        real_adjacent.repr point removed * (basis.repr (adjacent removed) removed : ℝ) := by
      conv_lhs => rw [← real_adjacent.sum_repr point]
      rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single removed]
      · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        congr 1
        change real_original.repr
          ((fan.lattice.isBaseChange.basis adjacent) removed) removed = _
        rw [fan.lattice.isBaseChange.basis_apply]
        change real_original.repr (embedding.toIntLinearMap (adjacent removed)) removed = _
        exact fan.lattice.isBaseChange.basis_repr_comp_apply basis (adjacent removed) removed
      · intro index _ distinct
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        have zero : real_original.repr (real_adjacent index) removed = 0 := by
          change real_original.repr
            ((fan.lattice.isBaseChange.basis adjacent) index) removed = 0
          rw [fan.lattice.isBaseChange.basis_apply,
            fan.lattice.isBaseChange.basis_repr_comp_apply, coordinate_others index distinct]
          simp
        rw [zero, mul_zero]
      · simp
    by_contra nonnegative
    have bound : 0 ≤ (basis.repr (adjacent removed) removed : ℝ) := by
      exact_mod_cast le_of_not_gt nonnegative
    rw [real_formula] at negative
    exact not_lt_of_ge (mul_nonneg (point_nonnegative removed) bound) negative
  have coefficient_minus_one : basis.repr (adjacent removed) removed = -1 := by
    rcases Int.isUnit_iff.mp unit_coefficient with positive | negative_unit
    · omega
    · exact negative_unit
  refine ⟨adjacent, adjacent_cone, shared_basis, coefficient_minus_one, fun vector => ?_⟩
  have formula := coordinate_formula vector
  rw [coefficient_minus_one, mul_neg_one] at formula
  omega

omit [FiniteDimensional ℝ Ambient] in
theorem adjacentCartierCharacterDifference_eq_coordinate_gap
    (fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (divisor : fan.InvariantRayDivisor) (vector : Lattice) :
    (fan.coneDivisorCharacter adjacent adjacent_cone divisor -
      fan.coneDivisorCharacter basis cone_basis divisor) vector =
      basis.repr vector removed *
        (fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis removed) +
          divisor (fan.basisRay basis cone_basis removed)) := by
  classical
  let difference := fan.coneDivisorCharacter adjacent adjacent_cone divisor -
    fan.coneDivisorCharacter basis cone_basis divisor
  have vanishes : ∀ index, index ≠ removed → difference (basis index) = 0 := by
    intro index distinct
    have same_ray : fan.basisRay adjacent adjacent_cone index = fan.basisRay basis cone_basis index :=
      Subtype.ext (shared index distinct)
    dsimp only [difference]
    rw [AddMonoidHom.sub_apply, fan.coneDivisorCharacter_basis basis cone_basis divisor index]
    have value : fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis index) =
        -divisor (fan.basisRay basis cone_basis index) := by
      rw [← shared index distinct,
        fan.coneDivisorCharacter_basis adjacent adjacent_cone divisor index, same_ray]
    rw [value, sub_self]
  change difference vector = _
  conv_lhs => rw [← basis.sum_repr vector]
  rw [map_sum, Finset.sum_eq_single removed]
  · rw [map_zsmul]
    change basis.repr vector removed * difference (basis removed) = _
    dsimp only [difference]
    rw [AddMonoidHom.sub_apply,
      fan.coneDivisorCharacter_basis basis cone_basis divisor removed, sub_neg_eq_add]
  · intro index _ distinct
    rw [map_zsmul, vanishes index distinct, smul_zero]
  · simp

omit [FiniteDimensional ℝ Ambient] in
theorem adjacentRealCartierCharacterDifference_eq_coordinate_gap
    (fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (divisor : fan.InvariantRayDivisor) (point : Ambient) :
    fan.lattice.realCharacter (fan.coneDivisorCharacter adjacent adjacent_cone divisor) point -
        fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor) point =
      (fan.lattice.isBaseChange.basis basis).repr point removed *
        ((fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis removed) +
          divisor (fan.basisRay basis cone_basis removed) : ℤ) : ℝ) := by
  classical
  let real_basis := fan.lattice.isBaseChange.basis basis
  let difference := fan.lattice.realCharacter
    (fan.coneDivisorCharacter adjacent adjacent_cone divisor -
      fan.coneDivisorCharacter basis cone_basis divisor)
  have value : ∀ index, difference (real_basis index) =
      if index = removed then
        ((fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis removed) +
          divisor (fan.basisRay basis cone_basis removed) : ℤ) : ℝ)
      else 0 := by
    intro index
    dsimp only [difference, real_basis]
    rw [fan.lattice.isBaseChange.basis_apply]
    change fan.lattice.realCharacter
        (fan.coneDivisorCharacter adjacent adjacent_cone divisor -
          fan.coneDivisorCharacter basis cone_basis divisor) (embedding (basis index)) = _
    rw [fan.lattice.realCharacter_apply,
      fan.adjacentCartierCharacterDifference_eq_coordinate_gap basis adjacent cone_basis
        adjacent_cone removed shared divisor]
    simp only [Basis.repr_self, Finsupp.single_apply]
    split_ifs with same
    · subst index
      simp
    · simp
  have evaluation : difference point =
      fan.lattice.realCharacter (fan.coneDivisorCharacter adjacent adjacent_cone divisor) point -
        fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor) point := by
    simp only [difference, map_sub, LinearMap.sub_apply]
  rw [← evaluation]
  conv_lhs => rw [← real_basis.sum_repr point]
  rw [map_sum, Finset.sum_eq_single removed]
  · rw [map_smul, value]
    simp only [ite_true, smul_eq_mul]
    rfl
  · intro index _ distinct
    rw [map_smul, value, ite_eq_right distinct, smul_zero]
  · simp

omit [FiniteDimensional ℝ Ambient] in
theorem adjacentRealCartierCharacter_le_on_basisCone_of_gap_nonnegative
    (fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (divisor : fan.InvariantRayDivisor)
    (gap_nonnegative : 0 ≤ fan.coneDivisorCharacter adjacent adjacent_cone divisor
      (basis removed) + divisor (fan.basisRay basis cone_basis removed))
    (point : Ambient) (contains : point ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor) point ≤
      fan.lattice.realCharacter (fan.coneDivisorCharacter adjacent adjacent_cone divisor) point := by
  have coordinates : ∀ index, 0 ≤ (fan.lattice.isBaseChange.basis basis).repr point index := by
    apply (BondalThomsen.mem_basisCone_iff (fan.lattice.isBaseChange.basis basis) point).mp
    convert contains using 1
    congr 1
    ext vector
    simp only [Set.mem_range]
    constructor <;> rintro ⟨index, rfl⟩ <;> refine ⟨index, ?_⟩
    · exact (fan.lattice.isBaseChange.basis_apply basis index).symm
    · exact fan.lattice.isBaseChange.basis_apply basis index
  apply sub_nonneg.mp
  rw [fan.adjacentRealCartierCharacterDifference_eq_coordinate_gap basis adjacent cone_basis
    adjacent_cone removed shared divisor]
  exact mul_nonneg (coordinates removed) (by exact_mod_cast gap_nonnegative)

omit [FiniteDimensional ℝ Ambient] in
theorem adjacentRealCartierCharacter_le_on_adjacentCone_of_gap_nonnegative
    (fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (coordinate_sign : basis.repr (adjacent removed) removed = -1)
    (divisor : fan.InvariantRayDivisor)
    (gap_nonnegative : 0 ≤ fan.coneDivisorCharacter adjacent adjacent_cone divisor
      (basis removed) + divisor (fan.basisRay basis cone_basis removed))
    (point : Ambient) (contains : point ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (adjacent index)))) :
    fan.lattice.realCharacter (fan.coneDivisorCharacter adjacent adjacent_cone divisor) point ≤
      fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor) point := by
  let difference := fan.coneDivisorCharacter basis cone_basis divisor -
    fan.coneDivisorCharacter adjacent adjacent_cone divisor
  have nonnegative : ∀ index, 0 ≤ difference (adjacent index) := by
    intro index
    by_cases same : index = removed
    · subst index
      have evaluation := fan.adjacentCartierCharacterDifference_eq_coordinate_gap basis adjacent
        cone_basis adjacent_cone removed shared divisor (adjacent removed)
      rw [coordinate_sign] at evaluation
      dsimp only [difference]
      simp only [AddMonoidHom.sub_apply] at evaluation ⊢
      linarith
    · have same_ray : fan.basisRay adjacent adjacent_cone index =
          fan.basisRay basis cone_basis index := Subtype.ext (shared index same)
      dsimp only [difference]
      rw [AddMonoidHom.sub_apply, shared index same]
      have value : fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis index) =
          -divisor (fan.basisRay basis cone_basis index) := by
        rw [← shared index same, fan.coneDivisorCharacter_basis, same_ray]
      rw [fan.coneDivisorCharacter_basis, value, sub_self]
  have dual_member : difference ∈ TauCeti.Toric.dualSemigroup fan.lattice
      (PointedCone.hull ℝ (embedding '' Set.range adjacent)) := by
    rw [TauCeti.Toric.mem_dualSemigroup_hull_image]
    rintro vector ⟨index, rfl⟩
    exact nonnegative index
  have in_hull : point ∈ PointedCone.hull ℝ (embedding '' Set.range adjacent) := by
    convert contains using 1
    congr 1
    ext vector
    simp
  have bound := (TauCeti.Toric.mem_dualSemigroup fan.lattice difference).mp dual_member in_hull
  simp only [difference, map_sub, LinearMap.sub_apply] at bound
  exact sub_nonneg.mp bound

theorem adjacentDivisorSupportFunction_eq_min_of_gap_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (coordinate_sign : basis.repr (adjacent removed) removed = -1)
    (divisor : fan.InvariantRayDivisor)
    (gap_nonnegative : 0 ≤ fan.coneDivisorCharacter adjacent adjacent_cone divisor
      (basis removed) + divisor (fan.basisRay basis cone_basis removed))
    (point : Ambient)
    (contains : point ∈ (PointedCone.hull ℝ
        (Set.range (fun index => embedding (basis index))) : Set Ambient) ∪
      (PointedCone.hull ℝ (Set.range (fun index => embedding (adjacent index))) : Set Ambient)) :
    fan.divisorSupportFunction complete regular divisor point =
      min (fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor) point)
        (fan.lattice.realCharacter (fan.coneDivisorCharacter adjacent adjacent_cone divisor) point) := by
  rcases contains with contains | contains
  · rw [fan.divisorSupportFunction_on_coneBasis complete regular divisor basis cone_basis _ contains]
    exact (min_eq_left (fan.adjacentRealCartierCharacter_le_on_basisCone_of_gap_nonnegative
      basis adjacent cone_basis adjacent_cone removed shared divisor gap_nonnegative point contains)).symm
  · rw [fan.divisorSupportFunction_on_coneBasis complete regular divisor adjacent adjacent_cone
      _ contains]
    exact (min_eq_right (fan.adjacentRealCartierCharacter_le_on_adjacentCone_of_gap_nonnegative
      basis adjacent cone_basis adjacent_cone removed shared coordinate_sign divisor gap_nonnegative
      point contains)).symm

theorem adjacentDivisorSupportFunction_concaveOn_of_gap_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (coordinate_sign : basis.repr (adjacent removed) removed = -1)
    (divisor : fan.InvariantRayDivisor)
    (gap_nonnegative : 0 ≤ fan.coneDivisorCharacter adjacent adjacent_cone divisor
      (basis removed) + divisor (fan.basisRay basis cone_basis removed))
    (domain : Set Ambient) (convex_domain : Convex ℝ domain)
    (within : domain ⊆ (PointedCone.hull ℝ
        (Set.range (fun index => embedding (basis index))) : Set Ambient) ∪
      (PointedCone.hull ℝ (Set.range (fun index => embedding (adjacent index))) : Set Ambient)) :
    ConcaveOn ℝ domain (fan.divisorSupportFunction complete regular divisor) := by
  have concave_min :=
    ((fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor)).concaveOn
      convex_domain).inf
      ((fan.lattice.realCharacter (fan.coneDivisorCharacter adjacent adjacent_cone divisor)).concaveOn
        convex_domain)
  apply concave_min.congr
  intro point contains
  exact (fan.adjacentDivisorSupportFunction_eq_min_of_gap_nonnegative complete regular basis
    adjacent cone_basis adjacent_cone removed shared coordinate_sign divisor gap_nonnegative
    point (within contains)).symm

theorem wallRestrictionSourceCharacter_eq_coneCharacter
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (ray : fan.Ray) (removed : Fin dimension) (equality : basis removed = ray.val) :
    fan.wallRestrictionSourceCharacter complete regular divisor ray
        (fan.wallDescentProjectedCone ray ⟨_, cone_basis⟩
          (by rw [← equality]; exact PointedCone.subset_hull ⟨removed, rfl⟩)) =
      fan.coneDivisorCharacter basis cone_basis divisor := by
  let cone : fan.cones := ⟨_, cone_basis⟩
  have contains : embedding ray.val ∈ cone.val := by
    rw [← equality]
    exact PointedCone.subset_hull ⟨removed, rfl⟩
  have lifted := fan.wallDescentProjectedCone_lift ray cone contains
  change fan.coneDivisorCharacter
      (fan.divisorChartBasis complete regular
        (fan.starConeLift ray (fan.wallDescentProjectedCone ray cone contains))).val.2
      (fan.divisorChartBasis complete regular
        (fan.starConeLift ray (fan.wallDescentProjectedCone ray cone contains))).property.1 divisor = _
  rw [lifted]
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change fan.coneDivisorCharacter (fan.divisorChartBasis complete regular cone).val.2
      (fan.divisorChartBasis complete regular cone).property.1 divisor (basis index) =
    fan.coneDivisorCharacter basis cone_basis divisor (basis index)
  have in_cone : embedding (basis index) ∈ cone.val := PointedCone.subset_hull ⟨index, rfl⟩
  have value := fan.coneDivisorCharacter_ray
    (fan.divisorChartBasis complete regular cone).val.2
    (fan.divisorChartBasis complete regular cone).property.1 divisor
    (fan.basisRay basis cone_basis index)
    ((fan.divisorChartBasis complete regular cone).property.2.le in_cone)
  exact value.trans (fan.coneDivisorCharacter_basis basis cone_basis divisor index).symm

end TauCeti.Toric.Fan
