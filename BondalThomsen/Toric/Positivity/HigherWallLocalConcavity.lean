module

public import BondalThomsen.Toric.Surface.GeometricNefSupport

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Module Filter
open scoped Topology

noncomputable section

namespace BondalThomsen

variable {Space : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space]

omit [FiniteDimensional ℝ Space] in
theorem adjacentBasis_omitted_coordinate_neg {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℝ Space) (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1) (point : Space) :
    basis.repr point removed = -adjacent.repr point removed := by
  have same : basis.coord removed = -adjacent.coord removed := by
    apply adjacent.ext
    intro index
    by_cases equal : index = removed
    · subst index
      simpa only [LinearMap.neg_apply, Basis.coord_apply, Basis.repr_self_apply,
        ite_true] using opposite
    · rw [LinearMap.neg_apply]
      change basis.repr (adjacent index) removed = -adjacent.repr (adjacent index) removed
      have original_zero : basis.repr (adjacent index) removed = 0 := by
        rw [shared index equal]
        simp [equal]
      rw [original_zero]
      simp [equal]
  exact LinearMap.congr_fun same point

omit [FiniteDimensional ℝ Space] in
theorem adjacentBasis_coordinates_on_facet {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℝ Space) (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (point : Space) (zero_coordinate : basis.repr point removed = 0)
    (index : Fin dimension) (distinct : index ≠ removed) :
    adjacent.repr point index = basis.repr point index := by
  classical
  change adjacent.coord index point = _
  conv_lhs => rw [← basis.sum_repr point]
  rw [map_sum, Finset.sum_eq_single index]
  · rw [map_smul, ← shared index distinct]
    simp
  · intro other _ different
    by_cases equal : other = removed
    · subst other
      rw [zero_coordinate, zero_smul, map_zero]
    · rw [map_smul, ← shared other equal]
      simp [Basis.coord_apply, different]
  · simp

theorem adjacentBasis_union_mem_nhds_of_positive_facet {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℝ Space) (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (point : Space) (zero_coordinate : basis.repr point removed = 0)
    (positive_coordinates : ∀ index, index ≠ removed → 0 < basis.repr point index) :
    (PointedCone.hull ℝ (Set.range basis) : Set Space) ∪
      (PointedCone.hull ℝ (Set.range adjacent) : Set Space) ∈ 𝓝 point := by
  let neighborhood := {nearby : Space | ∀ index, index ≠ removed →
    0 < basis.repr nearby index ∧ 0 < adjacent.repr nearby index}
  have open_neighborhood : IsOpen neighborhood := by
    have presentation : neighborhood = ⋂ index : {index : Fin dimension | index ≠ removed},
        {nearby : Space | 0 < basis.coord index.val nearby} ∩
          {nearby : Space | 0 < adjacent.coord index.val nearby} := by
      ext nearby
      simp [neighborhood]
    rw [presentation]
    apply isOpen_iInter_of_finite
    intro index
    exact (isOpen_lt continuous_const (basis.coord index.val).continuous_of_finiteDimensional).inter
      (isOpen_lt continuous_const (adjacent.coord index.val).continuous_of_finiteDimensional)
  have contains : point ∈ neighborhood := by
    intro index distinct
    rw [adjacentBasis_coordinates_on_facet basis adjacent removed shared point
      zero_coordinate index distinct]
    exact ⟨positive_coordinates index distinct, positive_coordinates index distinct⟩
  apply Filter.mem_of_superset (open_neighborhood.mem_nhds contains)
  intro nearby member
  by_cases positive_side : 0 ≤ basis.repr nearby removed
  · apply Or.inl
    apply (mem_basisCone_iff basis nearby).mpr
    intro index
    by_cases equal : index = removed
    · simpa only [equal] using positive_side
    · exact (member index equal).1.le
  · apply Or.inr
    apply (mem_basisCone_iff adjacent nearby).mpr
    intro index
    by_cases equal : index = removed
    · subst index
      have coordinate := adjacentBasis_omitted_coordinate_neg basis adjacent removed
        shared opposite nearby
      linarith
    · exact (member index equal).2.le

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in
def HasAdjacentWallCartierInequalities (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) : Prop :=
  ∀ dimension : ℕ, ∀ basis adjacent : Basis (Fin dimension) ℤ Lattice,
    ∀ cone_basis : fan.IsConeBasis basis, ∀ adjacent_cone : fan.IsConeBasis adjacent,
    ∀ removed : Fin dimension,
      (∀ index, index ≠ removed → adjacent index = basis index) →
      basis.repr (adjacent removed) removed = -1 →
      0 ≤ fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis removed) +
        divisor (fan.basisRay basis cone_basis removed)

omit [FiniteDimensional ℝ Ambient] in
theorem hasAdjacentWallCartierInequalities_of_raySupport
    (fan : Fan embedding) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor) :
    fan.HasAdjacentWallCartierInequalities divisor := by
  intro dimension basis adjacent cone_basis adjacent_cone removed _ _
  have bound := support dimension adjacent adjacent_cone (fan.basisRay basis cone_basis removed)
  change -divisor (fan.basisRay basis cone_basis removed) ≤
    fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis removed) at bound
  linarith

omit [FiniteDimensional ℝ Ambient] in
theorem coneBasis_hull_eq_realBasis_hull (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) =
      PointedCone.hull ℝ (Set.range (fan.lattice.isBaseChange.basis basis)) := by
  congr 1
  congr 1
  funext index
  exact (fan.lattice.isBaseChange.basis_apply basis index).symm

theorem adjacentConeBases_union_mem_nhds_of_positive_facet
    (fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice) (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (point : Ambient)
    (zero_coordinate : (fan.lattice.isBaseChange.basis basis).repr point removed = 0)
    (positive_coordinates : ∀ index, index ≠ removed →
      0 < (fan.lattice.isBaseChange.basis basis).repr point index) :
    (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) : Set Ambient) ∪
      (PointedCone.hull ℝ (Set.range (fun index => embedding (adjacent index))) : Set Ambient)
      ∈ 𝓝 point := by
  rw [fan.coneBasis_hull_eq_realBasis_hull basis, fan.coneBasis_hull_eq_realBasis_hull adjacent]
  apply BondalThomsen.adjacentBasis_union_mem_nhds_of_positive_facet
    (fan.lattice.isBaseChange.basis basis) (fan.lattice.isBaseChange.basis adjacent) removed
    _ _ point zero_coordinate positive_coordinates
  · intro index distinct
    rw [fan.lattice.isBaseChange.basis_apply, fan.lattice.isBaseChange.basis_apply,
      shared index distinct]
  · rw [fan.lattice.isBaseChange.basis_apply]
    change (fan.lattice.isBaseChange.basis basis).repr
      (embedding.toIntLinearMap (adjacent removed)) removed = -1
    rw [fan.lattice.isBaseChange.basis_repr_comp_apply, opposite]
    norm_num

theorem adjacentDivisorSupportFunction_locally_min_of_gap_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (divisor : fan.InvariantRayDivisor)
    (gap_nonnegative : 0 ≤ fan.coneDivisorCharacter adjacent adjacent_cone divisor
      (basis removed) + divisor (fan.basisRay basis cone_basis removed))
    (point : Ambient)
    (zero_coordinate : (fan.lattice.isBaseChange.basis basis).repr point removed = 0)
    (positive_coordinates : ∀ index, index ≠ removed →
      0 < (fan.lattice.isBaseChange.basis basis).repr point index) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ nearby ∈ Metric.ball point radius,
        fan.divisorSupportFunction complete regular divisor nearby =
          min (fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor) nearby)
            (fan.lattice.realCharacter
              (fan.coneDivisorCharacter adjacent adjacent_cone divisor) nearby)) ∧
      ConcaveOn ℝ (Metric.ball point radius)
        (fan.divisorSupportFunction complete regular divisor) := by
  obtain ⟨radius, positive, within⟩ := Metric.mem_nhds_iff.mp
    (fan.adjacentConeBases_union_mem_nhds_of_positive_facet basis adjacent removed shared
      opposite point zero_coordinate positive_coordinates)
  refine ⟨radius, positive, ?_, ?_⟩
  · intro nearby member
    exact fan.adjacentDivisorSupportFunction_eq_min_of_gap_nonnegative complete regular
      basis adjacent cone_basis adjacent_cone removed shared opposite divisor gap_nonnegative
      nearby (within member)
  · exact fan.adjacentDivisorSupportFunction_concaveOn_of_gap_nonnegative complete regular
      basis adjacent cone_basis adjacent_cone removed shared opposite divisor gap_nonnegative
      (Metric.ball point radius) (convex_ball point radius) within

theorem divisorSupportFunction_locally_concave_on_coneInterior
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (point : Ambient)
    (positive_coordinates : ∀ index,
      0 < (fan.lattice.isBaseChange.basis basis).repr point index) :
    ∃ radius : ℝ, 0 < radius ∧
      ConcaveOn ℝ (Metric.ball point radius)
        (fan.divisorSupportFunction complete regular divisor) := by
  have interior_member := BondalThomsen.mem_interior_basisCone_of_positive
    (fan.lattice.isBaseChange.basis basis) point positive_coordinates
  rw [← fan.coneBasis_hull_eq_realBasis_hull basis] at interior_member
  obtain ⟨radius, positive, within⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp interior_member)
  refine ⟨radius, positive, ?_⟩
  apply ((fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor)).concaveOn
    (convex_ball point radius)).congr
  intro nearby member
  exact (fan.divisorSupportFunction_on_coneBasis complete regular divisor basis cone_basis
    nearby (within member)).symm

theorem divisorSupportFunction_locally_concave_on_facet_of_wallInequalities
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (wall_inequalities : fan.HasAdjacentWallCartierInequalities divisor)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (removed : Fin dimension) (point : Ambient)
    (zero_coordinate : (fan.lattice.isBaseChange.basis basis).repr point removed = 0)
    (positive_coordinates : ∀ index, index ≠ removed →
      0 < (fan.lattice.isBaseChange.basis basis).repr point index) :
    ∃ radius : ℝ, 0 < radius ∧
      ConcaveOn ℝ (Metric.ball point radius)
        (fan.divisorSupportFunction complete regular divisor) := by
  obtain ⟨adjacent, adjacent_cone, shared, opposite, _⟩ :=
    fan.exists_coneBasis_across_facet_without_deep complete regular basis cone_basis removed
  obtain ⟨radius, positive, _, concave⟩ :=
    fan.adjacentDivisorSupportFunction_locally_min_of_gap_nonnegative complete regular
      basis adjacent cone_basis adjacent_cone removed shared opposite divisor
      (wall_inequalities dimension basis adjacent cone_basis adjacent_cone removed shared opposite)
      point zero_coordinate positive_coordinates
  exact ⟨radius, positive, concave⟩

theorem divisorSupportFunction_locally_concave_of_at_most_one_zero_coordinate
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (wall_inequalities : fan.HasAdjacentWallCartierInequalities divisor)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (point : Ambient)
    (nonnegative_coordinates : ∀ index,
      0 ≤ (fan.lattice.isBaseChange.basis basis).repr point index)
    (at_most_one_zero : ∀ first second : Fin dimension,
      (fan.lattice.isBaseChange.basis basis).repr point first = 0 →
      (fan.lattice.isBaseChange.basis basis).repr point second = 0 → first = second) :
    ∃ radius : ℝ, 0 < radius ∧
      ConcaveOn ℝ (Metric.ball point radius)
        (fan.divisorSupportFunction complete regular divisor) := by
  classical
  by_cases all_positive : ∀ index,
      0 < (fan.lattice.isBaseChange.basis basis).repr point index
  · exact fan.divisorSupportFunction_locally_concave_on_coneInterior complete regular
      basis cone_basis divisor point all_positive
  · obtain ⟨removed, not_positive⟩ := not_forall.mp all_positive
    have zero_coordinate : (fan.lattice.isBaseChange.basis basis).repr point removed = 0 :=
      le_antisymm (le_of_not_gt not_positive) (nonnegative_coordinates removed)
    apply fan.divisorSupportFunction_locally_concave_on_facet_of_wallInequalities
      complete regular divisor wall_inequalities basis cone_basis removed point zero_coordinate
    intro index distinct
    apply lt_of_le_of_ne (nonnegative_coordinates index)
    intro zero
    exact distinct (at_most_one_zero index removed zero.symm zero_coordinate)

end TauCeti.Toric.Fan
