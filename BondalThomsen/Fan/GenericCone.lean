module

public import BondalThomsen.Fan.ConeCoordinates
public import BondalThomsen.Fan.Representations

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem genericPositiveCone_of_complete_regular (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference_basis : Basis (Fin dimension) ℤ Lattice) :
    FanGenericPositiveCone fan dimension := by
  classical
  let full_cones := {cone : fan.cones //
    Submodule.span ℝ (cone.val : Set Ambient) = ⊤}
  have cone_basis_exists : ∀ cone : full_cones,
      ∃ basis : Basis (Fin dimension) ℤ Lattice,
        cone.val.val = PointedCone.hull ℝ
          (Set.range (fun index => embedding (basis index))) := by
    intro cone
    obtain ⟨size, basis, cone_eq⟩ := fan.exists_integralBasis_of_fullSpan
      cone.val.val (regular cone.val.property) cone.property
    have size_eq : size = dimension := by
      have first := finrank_eq_card_basis basis
      have second := finrank_eq_card_basis reference_basis
      simp only [Fintype.card_fin] at first second
      omega
    subst size
    exact ⟨basis, cone_eq⟩
  choose adapted adapted_cone_eq using cone_basis_exists
  let real_adapted := fun cone => fan.lattice.isBaseChange.basis (adapted cone)
  have kernel_proper : ∀ label : full_cones × Fin dimension,
      ((real_adapted label.1).coord label.2).ker ≠ ⊤ := by
    intro label equality
    have vanishes : (real_adapted label.1).coord label.2
        ((real_adapted label.1) label.2) = 0 := by
      have member : (real_adapted label.1) label.2 ∈
          ((real_adapted label.1).coord label.2).ker := by rw [equality]; trivial
      exact member
    simp at vanishes
  have generic := dense_avoiding_proper_subspaces
    (fun label : full_cones × Fin dimension => ((real_adapted label.1).coord label.2).ker)
    kernel_proper
  intro rays independent
  have real_independent := fan.linearIndependent_real_of_integer reference_basis
    (fun index => (rays index).val) independent
  have card_eq : Fintype.card (Fin dimension) = finrank ℝ Ambient := by
    rw [← fan.lattice.finrank_eq, finrank_eq_card_basis reference_basis]
  let ray_basis := Basis.mk real_independent
    (by rw [real_independent.span_eq_top_of_card_eq_finrank' card_eq])
  have positive_nonempty :
      {point : Ambient | ∀ index, 0 < ray_basis.repr point index}.Nonempty := by
    refine ⟨ray_basis.equivFun.symm (fun _ => 1), ?_⟩
    intro index
    change 0 < ray_basis.equivFun (ray_basis.equivFun.symm (fun _ => 1)) index
    simp
  obtain ⟨point, positive, avoids⟩ := generic.inter_open_nonempty _
    (isOpen_positive_basisCoordinates ray_basis) positive_nonempty
  obtain ⟨cone, member, contains, full_span⟩ := fan.exists_fullSpan_cone complete point
  let chosen : full_cones := ⟨⟨cone, member⟩, full_span⟩
  have positive_coordinates : ∀ row, 0 < (real_adapted chosen).repr point row := by
    intro row
    have nonnegative : 0 ≤ (real_adapted chosen).repr point row := by
      apply (mem_basisCone_iff (real_adapted chosen) point).mp
      have contains_adapted : point ∈ PointedCone.hull ℝ
          (Set.range (fun index => embedding (adapted chosen index))) := by
        rw [← adapted_cone_eq chosen]
        exact contains
      convert contains_adapted using 1
      congr 1
      ext vector
      simp only [Set.mem_range]
      constructor <;> rintro ⟨index, rfl⟩ <;> refine ⟨index, ?_⟩
      · exact (fan.lattice.isBaseChange.basis_apply (adapted chosen) index).symm
      · exact fan.lattice.isBaseChange.basis_apply (adapted chosen) index
    have nonzero : (real_adapted chosen).repr point row ≠ 0 :=
      avoids (chosen, row)
    exact lt_of_le_of_ne nonnegative (Ne.symm nonzero)
  have selected_cone : fan.IsConeBasis (adapted chosen) := by
    change PointedCone.hull ℝ (Set.range (fun index => embedding (adapted chosen index)))
      ∈ fan.cones
    rw [← adapted_cone_eq chosen]
    exact member
  refine ⟨adapted chosen, selected_cone, (fun index => ray_basis.repr point index),
    positive, ?_⟩
  intro row
  have decomposition : point = ∑ index, ray_basis.repr point index •
      embedding (rays index).val := by
    simpa only [ray_basis, Basis.mk_apply] using (ray_basis.sum_repr point).symm
  have coordinate_formula : (real_adapted chosen).repr point row =
      ∑ index, (adapted chosen).repr (rays index).val row * ray_basis.repr point index := by
    conv_lhs => rw [decomposition]
    rw [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro index _
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [show (real_adapted chosen).repr (embedding (rays index).val) row =
      ((adapted chosen).repr (rays index).val row : ℝ) from
      fan.lattice.isBaseChange.basis_repr_comp_apply (adapted chosen) (rays index).val row]
    exact mul_comm _ _
  simpa only [Basis.toMatrix_apply] using
    (coordinate_formula ▸ positive_coordinates row)

theorem rayMatrix_totallyUnimodular_of_complete_regular (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (adjacency : FanWallAdjacency fan dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    (fan.rayMatrix basis).IsTotallyUnimodular :=
  fan.rayMatrix_totallyUnimodular deep adjacency
    (fan.genericPositiveCone_of_complete_regular complete regular basis) basis cone_basis

theorem rayMatroid_representable_of_complete_regular (fan : TauCeti.Toric.Fan embedding)
    {Field : Type*} [_root_.Field Field] {dimension : ℕ} (complete : fan.IsComplete)
    (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (adjacency : FanWallAdjacency fan dimension) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) : fan.rayMatroid.Representable Field :=
  fan.rayMatroid_representable deep adjacency
    (fan.genericPositiveCone_of_complete_regular complete regular basis) basis cone_basis

end TauCeti.Toric.Fan
