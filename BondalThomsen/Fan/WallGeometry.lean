module

public import BondalThomsen.Fan.GenericCone
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen Filter
open scoped Topology

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem exists_basis_across_facet (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin dimension) ℤ Lattice) (removed : Fin dimension) :
    ∃ adjacent : Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis adjacent ∧
      (∑ index, (if index = removed then (0 : ℝ) else 1) • embedding (basis index)) ∈
        PointedCone.hull ℝ (Set.range (fun index => embedding (adjacent index))) ∧
      ∃ point ∈ PointedCone.hull ℝ (Set.range (fun index => embedding (adjacent index))),
        (fan.lattice.isBaseChange.basis basis).repr point removed < 0 := by
  classical
  let facet_point := ∑ index, (if index = removed then (0 : ℝ) else 1) •
    embedding (basis index)
  have nearby := (locallyFinite_of_finite
    (fun cone : fan.cones => (cone.val : Set Ambient))).eventually_subset
      (fun cone => fan.cone_isClosed cone.val cone.property) facet_point
  let perturbation := fun scalar : ℝ => facet_point - scalar • embedding (basis removed)
  have continuous_perturbation : Continuous perturbation :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have converges : Tendsto perturbation (𝓝 0) (𝓝 facet_point) := by
    simpa only [perturbation, zero_smul, sub_zero] using continuous_perturbation.tendsto 0
  obtain ⟨scalar, scalar_positive, local_member⟩ := (converges.eventually nearby).exists_gt
  obtain ⟨size, adjacent, adjacent_member, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (perturbation scalar)
  have size_eq : size = dimension := by
    have original_rank := finrank_eq_card_basis basis
    have adjacent_rank := finrank_eq_card_basis adjacent
    simp only [Fintype.card_fin] at original_rank adjacent_rank
    omega
  subst size
  let cone := PointedCone.hull ℝ (Set.range (fun index => embedding (adjacent index)))
  have facet_member : facet_point ∈ cone :=
    local_member (show (⟨cone, adjacent_member⟩ : fan.cones) ∈
      {cone : fan.cones | perturbation scalar ∈ cone.val} from contains)
  refine ⟨adjacent, adjacent_member, facet_member, perturbation scalar, contains, ?_⟩
  let real_basis := fan.lattice.isBaseChange.basis basis
  have coordinate_basis : ∀ index,
      real_basis.repr (embedding (basis index)) removed = if index = removed then 1 else 0 := by
    intro index
    change real_basis.repr (embedding.toIntLinearMap (basis index)) removed = _
    rw [← fan.lattice.isBaseChange.basis_apply basis]
    exact real_basis.repr_self_apply index removed
  have facet_coordinate : real_basis.repr facet_point removed = 0 := by
    simp only [facet_point, map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, coordinate_basis]
    apply Finset.sum_eq_zero
    intro index _
    split_ifs <;> simp
  change real_basis.repr (facet_point - scalar • embedding (basis removed)) removed < 0
  rw [map_sub, Finsupp.sub_apply, facet_coordinate, map_smul, Finsupp.smul_apply,
    smul_eq_mul, coordinate_basis, ite_eq_left rfl, mul_one, zero_sub]
  exact neg_neg_of_pos scalar_positive

theorem wallAdjacency_of_complete_regular_deep (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) : FanWallAdjacency fan dimension := by
  classical
  intro basis cone_basis removed
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
  let real_adapted := fan.lattice.isBaseChange.basis adapted
  have generator_match : ∀ index : {index : Fin dimension // index ≠ removed},
      ∃ row, basis index.val = adapted row := by
    intro index
    have real_nonnegative : ∀ row,
        0 ≤ real_adapted.repr (embedding (basis index.val)) row := by
      apply (mem_basisCone_iff real_adapted _).mp
      convert shared index.val index.property using 1
      congr 1
      ext vector
      simp only [Set.mem_range]
      constructor <;> rintro ⟨row, rfl⟩ <;> refine ⟨row, ?_⟩
      · exact (fan.lattice.isBaseChange.basis_apply adapted row).symm
      · exact fan.lattice.isBaseChange.basis_apply adapted row
    have integer_nonnegative : ∀ row, 0 ≤ adapted.repr (basis index.val) row := by
      intro row
      have bound := real_nonnegative row
      change (fan.lattice.isBaseChange.basis adapted).repr
        (embedding.toIntLinearMap (basis index.val)) row ≥ 0 at bound
      rw [fan.lattice.isBaseChange.basis_repr_comp_apply] at bound
      change 0 ≤ (adapted.repr (basis index.val) row : ℝ) at bound
      exact_mod_cast bound
    have integer_nonzero : (fun row => adapted.repr (basis index.val) row) ≠ 0 := by
      intro zero
      have vector_zero : basis index.val = 0 := by
        apply adapted.repr.injective
        ext row
        simpa using congrFun zero row
      exact basis.ne_zero index.val vector_zero
    obtain ⟨row, coordinates⟩ := (deep adapted adapted_cone
      (fan.basisRay basis cone_basis index.val)).eq_basis_vector_of_nonnegative
        integer_nonnegative integer_nonzero
    refine ⟨row, ?_⟩
    apply adapted.repr.injective
    ext column
    simpa [Basis.repr_self_apply, Finsupp.single_apply, eq_comm] using coordinates column
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
      apply (mem_basisCone_iff real_adjacent point).mp
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
    have bound : 0 ≤ (basis.repr (adjacent removed) removed : ℝ) := by exact_mod_cast le_of_not_gt nonnegative
    rw [real_formula] at negative
    exact not_lt_of_ge (mul_nonneg (point_nonnegative removed) bound) negative
  have coefficient_minus_one : basis.repr (adjacent removed) removed = -1 := by
    rcases Int.isUnit_iff.mp unit_coefficient with positive | negative
    · omega
    · exact negative
  refine ⟨adjacent, adjacent_cone, fun vector => ?_⟩
  have formula := coordinate_formula vector
  rw [coefficient_minus_one, mul_neg_one] at formula
  omega

end TauCeti.Toric.Fan
