module

public import BondalThomsen.Fan.SmoothFanoPolytopeFiniteness
public import BondalThomsen.Fan.WallGeometry
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Set Finset BondalThomsen
open scoped Classical

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem exists_wallExchange_of_complete_regular
    (fan : Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (removed : Fin dimension) :
    ∃ adjacent : Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis adjacent ∧
      (∀ index, index ≠ removed → adjacent index = basis index) ∧
      basis.repr (adjacent removed) removed = -1 ∧
      (∀ vector : Lattice, adjacent.repr vector removed = -basis.repr vector removed) := by
  classical
  obtain ⟨adapted, adaptedCone, facetMember, point, pointMember, negative⟩ :=
    fan.exists_basis_across_facet complete regular basis removed
  let originalCone := PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))
  let adaptedHull := PointedCone.hull ℝ (Set.range (fun index => embedding (adapted index)))
  let coefficients := fun index : Fin dimension => if index = removed then (0 : ℝ) else 1
  have originalGenerators : ∀ index, embedding (basis index) ∈ originalCone :=
    fun index => PointedCone.subset_hull ⟨index, rfl⟩
  have facetOriginal : ∑ index, coefficients index • embedding (basis index) ∈ originalCone :=
    Submodule.sum_mem _ fun index _ => PointedCone.smul_mem _
      (by simp only [coefficients]; split_ifs <;> norm_num) (originalGenerators index)
  have shared : ∀ index, index ≠ removed → embedding (basis index) ∈ adaptedHull := by
    intro index distinct
    exact ((fan.inf_isFaceOf_left coneBasis adaptedCone).mem_of_sum_smul_mem
      originalGenerators (fun index => by simp only [coefficients]; split_ifs <;> norm_num)
      ⟨facetOriginal, facetMember⟩ index (by simp [coefficients, distinct])).2
  have generatorMatch : ∀ index : {index : Fin dimension // index ≠ removed},
      ∃ row, basis index.val = adapted row := by
    intro index
    obtain ⟨row, equality⟩ := fan.ray_eq_basis_of_mem_coneBasis adapted adaptedCone
      (fan.basisRay basis coneBasis index.val) (shared index.val index.property)
    exact ⟨row, equality.symm⟩
  choose matching matched using generatorMatch
  have matchingInjective : Function.Injective matching := by
    intro first second equality
    apply Subtype.ext
    apply basis.injective
    rw [matched, matched, equality]
  obtain ⟨permutation, extendsMatching⟩ := Cardinal.extend_function_finite
    (⟨matching, matchingInjective⟩ : {index : Fin dimension | index ≠ removed} ↪ Fin dimension)
    (show Nonempty (Fin dimension ≃ Fin dimension) from ⟨Equiv.refl _⟩)
  let adjacent := adapted.reindex permutation.symm
  have sharedBasis : ∀ index, index ≠ removed → adjacent index = basis index := by
    intro index distinct
    change adapted.reindex permutation.symm index = basis index
    rw [Basis.reindex_apply]
    change adapted (permutation index) = basis index
    rw [extendsMatching ⟨index, distinct⟩]
    exact (matched ⟨index, distinct⟩).symm
  have ranges : Set.range (fun index => embedding (adjacent index)) =
      Set.range (fun index => embedding (adapted index)) := by
    change Set.range (embedding ∘ adjacent) = Set.range (embedding ∘ adapted)
    rw [Set.range_comp, Set.range_comp]
    congr 1
    exact Basis.range_reindex adapted permutation.symm
  have adjacentCone : fan.IsConeBasis adjacent := by
    change PointedCone.hull ℝ (Set.range (fun index => embedding (adjacent index))) ∈ fan.cones
    rw [ranges]
    exact adaptedCone
  have coordinateOthers : ∀ index, index ≠ removed → basis.repr (adjacent index) removed = 0 := by
    intro index distinct
    rw [sharedBasis index distinct]
    simp [distinct]
  have coordinateFormula : ∀ vector : Lattice, basis.repr vector removed =
      adjacent.repr vector removed * basis.repr (adjacent removed) removed := by
    intro vector
    conv_lhs => rw [← adjacent.sum_repr vector]
    rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single removed]
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro index _ distinct
      simp [map_smul, coordinateOthers index distinct]
    · simp
  have unitCoefficient : IsUnit (basis.repr (adjacent removed) removed) := by
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨adjacent.repr (basis removed) removed, ?_⟩
    simpa using (coordinateFormula (basis removed)).symm
  have coefficientNegative : basis.repr (adjacent removed) removed < 0 := by
    let realOriginal := fan.lattice.isBaseChange.basis basis
    let realAdjacent := fan.lattice.isBaseChange.basis adjacent
    have pointNonnegative : ∀ index, 0 ≤ realAdjacent.repr point index := by
      apply (mem_basisCone_iff realAdjacent point).mp
      have pointAdjacent : point ∈ PointedCone.hull ℝ
          (Set.range (fun index => embedding (adjacent index))) := by
        rwa [ranges]
      convert pointAdjacent using 1
      congr 1
      ext vector
      simp only [Set.mem_range]
      constructor <;> rintro ⟨index, rfl⟩ <;> refine ⟨index, ?_⟩
      · exact (fan.lattice.isBaseChange.basis_apply adjacent index).symm
      · exact fan.lattice.isBaseChange.basis_apply adjacent index
    have realFormula : realOriginal.repr point removed = realAdjacent.repr point removed *
        (basis.repr (adjacent removed) removed : ℝ) := by
      conv_lhs => rw [← realAdjacent.sum_repr point]
      rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single removed]
      · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        congr 1
        change realOriginal.repr ((fan.lattice.isBaseChange.basis adjacent) removed) removed = _
        rw [fan.lattice.isBaseChange.basis_apply]
        change realOriginal.repr (embedding.toIntLinearMap (adjacent removed)) removed = _
        exact fan.lattice.isBaseChange.basis_repr_comp_apply basis (adjacent removed) removed
      · intro index _ distinct
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        have zero : realOriginal.repr (realAdjacent index) removed = 0 := by
          change realOriginal.repr ((fan.lattice.isBaseChange.basis adjacent) index) removed = 0
          rw [fan.lattice.isBaseChange.basis_apply,
            fan.lattice.isBaseChange.basis_repr_comp_apply, coordinateOthers index distinct]
          simp
        rw [zero, mul_zero]
      · simp
    by_contra nonnegative
    have bound : 0 ≤ (basis.repr (adjacent removed) removed : ℝ) := by
      exact_mod_cast le_of_not_gt nonnegative
    rw [realFormula] at negative
    exact not_lt_of_ge (mul_nonneg (pointNonnegative removed) bound) negative
  have coefficientMinusOne : basis.repr (adjacent removed) removed = -1 := by
    rcases Int.isUnit_iff.mp unitCoefficient with positive | negative
    · omega
    · exact negative
  refine ⟨adjacent, adjacentCone, sharedBasis, coefficientMinusOne, fun vector => ?_⟩
  have formula := coordinateFormula vector
  rw [coefficientMinusOne, mul_neg_one] at formula
  omega

omit [FiniteDimensional ℝ Ambient] in
theorem wallExchange_height_formula
    (_fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice) (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1) (vector : Lattice) :
    adjacent.sumCoords vector = basis.sumCoords vector +
      (basis.sumCoords (adjacent removed) - 1) * basis.repr vector removed := by
  have characters : adjacent.sumCoords = basis.sumCoords +
      (basis.sumCoords (adjacent removed) - 1) • basis.coord removed := by
    apply adjacent.ext
    intro index
    by_cases equality : index = removed
    · subst index
      simp only [Basis.sumCoords_self_apply, LinearMap.add_apply, LinearMap.smul_apply,
        Basis.coord_apply, opposite, smul_eq_mul]
      ring
    · rw [Basis.sumCoords_self_apply, shared index equality]
      simp [Basis.coord_apply, equality]
  have evaluation := congrArg (fun character : Lattice →ₗ[ℤ] ℤ => character vector) characters
  simpa only [LinearMap.add_apply, LinearMap.smul_apply, Basis.coord_apply, smul_eq_mul] using evaluation

theorem rayCoordinate_ge_height_sub_one_of_strictSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (strict : fan.HasStrictAnticanonicalConeSupport) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (ray : fan.Ray) (index : Fin dimension) :
    basis.sumCoords ray.val - 1 ≤ basis.repr ray.val index := by
  obtain ⟨adjacent, adjacentCone, shared, opposite, _⟩ :=
    fan.exists_wallExchange_of_complete_regular complete regular basis coneBasis index
  have outside : (fan.basisRay adjacent adjacentCone index).val ∉ Set.range basis := by
    rintro ⟨coordinate, equality⟩
    have coordinates := congrArg (fun vector => basis.repr vector index) equality
    change basis.repr (basis coordinate) index = basis.repr (adjacent index) index at coordinates
    rw [opposite] at coordinates
    simp only [Basis.repr_self_apply] at coordinates
    by_cases equal : coordinate = index
    · simp only [equal] at coordinates
      omega
    · rw [ite_eq_right equal] at coordinates
      omega
  have adjacentHeight := fan.rayHeight_nonpositive_of_strictSupport_nongenerator
    strict basis coneBasis (fan.basisRay adjacent adjacentCone index) outside
  have rayHeight := fan.rayHeight_le_one_of_strictSupport strict basis coneBasis ray
  have changedHeight := fan.rayHeight_le_one_of_strictSupport strict adjacent adjacentCone ray
  rw [fan.wallExchange_height_formula basis adjacent index shared opposite] at changedHeight
  by_cases coordinateNonnegative : 0 ≤ basis.repr ray.val index
  · omega
  · have productBound : basis.repr ray.val index * (1 - basis.sumCoords (adjacent index)) ≤
        basis.repr ray.val index := by
      have heightNonpositive : basis.sumCoords (adjacent index) ≤ 0 := adjacentHeight
      nlinarith
    nlinarith

theorem specialConeBasis_rayCoordinate_lower_bound
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (strict : fan.HasStrictAnticanonicalConeSupport) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (special : fan.IsSpecialConeBasis basis)
    (ray : fan.Ray) (index : Fin dimension) :
    -((dimension : ℤ) + 1) ≤ basis.repr ray.val index := by
  have heightBound := (fan.specialConeBasis_rayHeight_bounds strict basis special ray).1
  have coordinateBound := fan.rayCoordinate_ge_height_sub_one_of_strictSupport
    complete regular strict basis special.1 ray index
  omega

theorem specialConeBasis_rayCoordinate_bounds
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (strict : fan.HasStrictAnticanonicalConeSupport) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (special : fan.IsSpecialConeBasis basis)
    (ray : fan.Ray) (index : Fin dimension) :
    -((dimension : ℤ) + 1) ≤ basis.repr ray.val index ∧
      basis.repr ray.val index ≤ (dimension : ℤ) ^ 2 := by
  have lower := fan.specialConeBasis_rayCoordinate_lower_bound complete regular strict basis special ray index
  have coordinateLower := fan.specialConeBasis_rayCoordinate_lower_bound complete regular strict basis special ray
  have heightUpper := (fan.specialConeBasis_rayHeight_bounds strict basis special ray).2
  have otherLower : -(dimension : ℤ) ^ 2 + 1 ≤
      ∑ coordinate ∈ Finset.univ.erase index, basis.repr ray.val coordinate := by
    have lowerSum := (Finset.univ.erase index).card_nsmul_le_sum
      (fun coordinate => basis.repr ray.val coordinate) (-((dimension : ℤ) + 1))
      (fun coordinate _ => coordinateLower coordinate)
    have dimensionPositive : 1 ≤ dimension := Nat.succ_le_iff.mpr (Fin.pos index)
    have erasedCard : (Finset.univ.erase index).card = dimension - 1 := by simp
    rw [erasedCard, nsmul_eq_mul] at lowerSum
    have predecessorCast : ((dimension - 1 : ℕ) : ℤ) = (dimension : ℤ) - 1 := by
      exact Nat.cast_sub dimensionPositive
    rw [predecessorCast] at lowerSum
    nlinarith
  have sumEquality : basis.sumCoords ray.val = basis.repr ray.val index +
      ∑ coordinate ∈ Finset.univ.erase index, basis.repr ray.val coordinate := by
    have coordinates : basis.sumCoords ray.val = ∑ coordinate, basis.repr ray.val coordinate := by
      simp [Basis.sumCoords, Finsupp.sum_fintype]
    rw [coordinates]
    exact (Finset.add_sum_erase Finset.univ (fun coordinate => basis.repr ray.val coordinate)
      (Finset.mem_univ index)).symm
  exact ⟨lower, by nlinarith⟩

def normalizedRayCoordinates (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) : Set (Fin dimension → ℤ) :=
  Set.range (fun ray : fan.Ray => fun index => basis.repr ray.val index)

def smoothFanoCoordinateBox (dimension : ℕ) : Set (Fin dimension → ℤ) :=
  {coordinates | ∀ index, -((dimension : ℤ) + 1) ≤ coordinates index ∧
    coordinates index ≤ (dimension : ℤ) ^ 2}

theorem smoothFanoCoordinateBox_finite (dimension : ℕ) :
    (smoothFanoCoordinateBox dimension).Finite := by
  exact Set.Finite.pi' fun _ => Set.finite_Icc (-((dimension : ℤ) + 1)) ((dimension : ℤ) ^ 2)

theorem specialConeBasis_normalizedRayCoordinates_subset_box
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (strict : fan.HasStrictAnticanonicalConeSupport) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (special : fan.IsSpecialConeBasis basis) :
    fan.normalizedRayCoordinates basis ⊆ smoothFanoCoordinateBox dimension := by
  rintro coordinates ⟨ray, rfl⟩ index
  exact fan.specialConeBasis_rayCoordinate_bounds complete regular strict basis special ray index

end TauCeti.Toric.Fan
