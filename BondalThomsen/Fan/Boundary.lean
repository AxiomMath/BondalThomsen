module

public import BondalThomsen.Fan.Determination
public import BondalThomsen.Fan.Interior

@[expose] public section

namespace BondalThomsen

open Set

variable {Index Ambient : Type*} [Fintype Index] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient]

theorem sum_mem_interior_of_sum_lt_one {points : Set Ambient}
    (convex : Convex ℝ points) (zero_interior : (0 : Ambient) ∈ interior points)
    (weights : Index → ℝ) (vectors : Index → Ambient)
    (nonnegative : ∀ index, 0 ≤ weights index)
    (total_lt : ∑ index, weights index < 1)
    (members : ∀ index, vectors index ∈ points) :
    ∑ index, weights index • vectors index ∈ interior points := by
  classical
  let total := ∑ index, weights index
  have total_nonnegative : 0 ≤ total := Finset.sum_nonneg (fun index _ => nonnegative index)
  by_cases total_zero : total = 0
  · have weights_zero : ∀ index, weights index = 0 := by
      exact fun index => (Finset.sum_eq_zero_iff_of_nonneg
        (fun index _ => nonnegative index)).mp total_zero index (Finset.mem_univ index)
    simpa [weights_zero] using zero_interior
  · have total_positive : 0 < total := lt_of_le_of_ne total_nonnegative (Ne.symm total_zero)
    let normalized := ∑ index, (weights index / total) • vectors index
    have normalized_member : normalized ∈ points := by
      apply convex.sum_mem
      · intro index _
        exact div_nonneg (nonnegative index) total_nonnegative
      · rw [← Finset.sum_div]
        exact div_self total_zero
      · intro index _
        exact members index
    have interior := convex.combo_interior_self_mem_interior zero_interior normalized_member
      (show 0 < 1 - total by linarith) total_nonnegative (by ring : 1 - total + total = 1)
    have scaled : total • normalized = ∑ index, weights index • vectors index := by
      simp only [normalized, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro index _
      congr 1
      field_simp
    simpa only [smul_zero, zero_add, scaled] using interior

end BondalThomsen

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem rayPolytope_isClosed (fan : TauCeti.Toric.Fan embedding) :
    IsClosed fan.rayPolytope :=
  fan.rayGenerators_finite.isCompact_convexHull ℝ |>.isClosed

theorem frontier_mem_basisFace [Nontrivial Ambient] (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (deep : fan.IsDeep dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (point : Ambient) (boundary : point ∈ frontier fan.rayPolytope)
    (contains : point ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    point ∈ convexHull ℝ (Set.range (fun index => embedding (basis index))) := by
  classical
  let real_basis := fan.lattice.isBaseChange.basis basis
  have real_contains : point ∈ PointedCone.hull ℝ (Set.range real_basis) := by
    convert contains using 1
    congr 1
    ext vector
    simp only [Set.mem_range]
    constructor <;> rintro ⟨index, rfl⟩ <;> refine ⟨index, ?_⟩
    · exact (fan.lattice.isBaseChange.basis_apply basis index).symm
    · exact fan.lattice.isBaseChange.basis_apply basis index
  have nonnegative := (mem_basisCone_iff real_basis point).mp real_contains
  have member := fan.rayPolytope_isClosed.frontier_subset boundary
  have bound := fan.rayPolytope_supporting_le_one deep basis cone_basis member
  have equality : fan.supportingFunctional basis point = 1 := by
    apply le_antisymm bound
    by_contra not_le
    have total_lt : ∑ index, real_basis.repr point index < 1 := by
      rw [← fan.supportingFunctional_eq_sum_realCoordinates basis point]
      exact lt_of_not_ge not_le
    have interior := sum_mem_interior_of_sum_lt_one
      (convex_convexHull ℝ fan.rayGenerators)
      (fan.zero_mem_interior_rayPolytope_of_complete complete)
      (fun index => real_basis.repr point index) real_basis nonnegative total_lt
      (fun index => by
        apply subset_convexHull ℝ fan.rayGenerators
        rw [fan.lattice.isBaseChange.basis_apply basis index]
        exact fan.basisGenerators_subset_rayGenerators basis cone_basis ⟨index, rfl⟩)
    rw [real_basis.sum_repr point] at interior
    exact (mem_frontier_iff_notMem_interior member).mp boundary interior
  rw [← fan.rayPolytope_inter_supportingHyperplane deep basis cone_basis]
  exact ⟨member, equality⟩

theorem frontier_covered_by_basisFaces [Nontrivial Ambient]
    (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice)
    (point : Ambient) (boundary : point ∈ frontier fan.rayPolytope) :
    ∃ basis : Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis basis ∧
      point ∈ convexHull ℝ (Set.range (fun index => embedding (basis index))) := by
  obtain ⟨size, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular point
  have size_eq : size = dimension := by
    have ranks := (finrank_eq_card_basis basis).symm.trans (finrank_eq_card_basis reference)
    simpa only [Fintype.card_fin] using ranks
  subst size
  exact ⟨basis, cone_basis, fan.frontier_mem_basisFace complete deep basis cone_basis
    point boundary contains⟩

end TauCeti.Toric.Fan
