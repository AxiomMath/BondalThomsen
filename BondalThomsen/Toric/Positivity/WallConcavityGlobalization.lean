module

public import BondalThomsen.Toric.Positivity.HigherWallLocalConcavity

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Module Filter
open scoped Topology

noncomputable section

namespace BondalThomsen

theorem basis_pair_ker_sup_span_singleton_ne_top
    {Space Index : Type} [AddCommGroup Space] [Module ℝ Space]
    (basis : Basis Index ℝ Space) (first second : Index) (distinct : first ≠ second)
    (point : Space) :
    (basis.coord first).ker ⊓ (basis.coord second).ker ⊔
      Submodule.span ℝ {point} ≠ ⊤ := by
  classical
  intro equality
  have decomposes : ∀ vector : Space, ∃ remainder : Space,
      remainder ∈ (basis.coord first).ker ⊓ (basis.coord second).ker ∧
        ∃ scalar : ℝ, remainder + scalar • point = vector := by
    intro vector
    have member : vector ∈ (basis.coord first).ker ⊓ (basis.coord second).ker ⊔
        Submodule.span ℝ {point} := by rw [equality]; trivial
    obtain ⟨remainder, remainder_member, multiple, multiple_member, sum_eq⟩ :=
      Submodule.mem_sup.mp member
    obtain ⟨scalar, scalar_eq⟩ := Submodule.mem_span_singleton.mp multiple_member
    exact ⟨remainder, remainder_member, scalar, scalar_eq ▸ sum_eq⟩
  by_cases zero_coordinate : basis.coord first point = 0
  · obtain ⟨remainder, remainder_member, scalar, sum_eq⟩ := decomposes (basis first)
    have coordinate_eq := congrArg (basis.coord first) sum_eq
    have remainder_zero : basis.coord first remainder = 0 := remainder_member.1
    simp only [map_add, map_smul, smul_eq_mul, remainder_zero, zero_coordinate,
      mul_zero, add_zero, Basis.coord_apply, Basis.repr_self_apply, ite_true] at coordinate_eq
    exact zero_ne_one coordinate_eq
  · obtain ⟨remainder, remainder_member, scalar, sum_eq⟩ := decomposes (basis second)
    have first_eq := congrArg (basis.coord first) sum_eq
    have second_eq := congrArg (basis.coord second) sum_eq
    have first_zero : basis.coord first remainder = 0 := remainder_member.1
    have second_zero : basis.coord second remainder = 0 := remainder_member.2
    have scalar_zero : scalar = 0 := by
      have product_zero : scalar * basis.coord first point = 0 := by
        simpa only [map_add, map_smul, smul_eq_mul, first_zero, zero_add,
          Basis.coord_apply, Basis.repr_self_apply, ite_eq_right distinct.symm] using first_eq
      exact (mul_eq_zero.mp product_zero).resolve_right zero_coordinate
    simp only [map_add, map_smul, smul_eq_mul, second_zero, scalar_zero,
      zero_mul, add_zero, Basis.coord_apply, Basis.repr_self_apply, ite_true] at second_eq
    exact zero_ne_one second_eq

theorem chord_le_of_continuous_locally_concave_off_finite_subspaces
    {Space Index : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] [Finite Index]
    (subspaces : Index → Submodule ℝ Space)
    (proper_extensions : ∀ index point,
      subspaces index ⊔ Submodule.span ℝ {point} ≠ ⊤)
    (function : Space → ℝ) (continuous : Continuous function)
    (locally_concave : ∀ point : Space, (∀ index, point ∉ subspaces index) →
      ∃ radius : ℝ, 0 < radius ∧ ConcaveOn ℝ (Metric.ball point radius) function)
    (first second : Space) (parameter : ℝ) (member : parameter ∈ Icc (0 : ℝ) 1) :
    (1 - parameter) * function first + parameter * function second ≤
      function (AffineMap.lineMap first second parameter) := by
  let extensions := fun index => subspaces index ⊔ Submodule.span ℝ {first}
  have generic := dense_avoiding_proper_subspaces extensions
    (fun index => proper_extensions index first)
  let chord_domain := {other : Space |
    (1 - parameter) * function first + parameter * function other ≤
      function (AffineMap.lineMap first other parameter)}
  have closed_domain : IsClosed chord_domain := by
    have path_continuous : Continuous
        (fun other : Space => AffineMap.lineMap first other parameter) := by
      simp only [AffineMap.lineMap_apply_module]
      exact continuous_const.add (continuous_const.smul continuous_id)
    exact isClosed_le
      (continuous_const.add (continuous_const.mul continuous))
      (continuous.comp path_continuous)
  have generic_chord : {other : Space | ∀ index, other ∉ extensions index} ⊆
      chord_domain := by
    intro other avoids
    let path : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap first other
    have path_continuous : Continuous path := path.continuous_of_finiteDimensional
    have path_avoids : ∀ scalar ∈ Ioo (0 : ℝ) 1,
        ∀ index, path scalar ∉ subspaces index := by
      intro scalar scalar_member index path_member
      have scalar_nonzero : scalar ≠ 0 := ne_of_gt scalar_member.1
      have path_in_extension : path scalar ∈ extensions index :=
        Submodule.mem_sup_left path_member
      have first_in_extension : first ∈ extensions index :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self first)
      have multiple_in_extension : scalar • other ∈ extensions index := by
        have difference := (extensions index).sub_mem path_in_extension
          ((extensions index).smul_mem (1 - scalar) first_in_extension)
        simpa only [path, AffineMap.lineMap_apply_module, add_sub_cancel_left] using difference
      have other_in_extension := (extensions index).smul_mem scalar⁻¹ multiple_in_extension
      rw [smul_smul, inv_mul_cancel₀ scalar_nonzero, one_smul] at other_in_extension
      exact avoids index other_in_extension
    have local_path_concavity : ∀ scalar ∈ Ioo (0 : ℝ) 1,
        ∃ radius : ℝ, 0 < radius ∧
          ConcaveOn ℝ (Metric.ball scalar radius) (function ∘ path) := by
      intro scalar scalar_member
      obtain ⟨radius, radius_positive, concave⟩ := locally_concave (path scalar)
        (path_avoids scalar scalar_member)
      have neighborhood : path ⁻¹' Metric.ball (path scalar) radius ∈ 𝓝 scalar :=
        path_continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ radius_positive)
      obtain ⟨parameter_radius, positive, within⟩ := Metric.mem_nhds_iff.mp neighborhood
      exact ⟨parameter_radius, positive,
        (concave.comp_affineMap path).subset within (convex_ball scalar parameter_radius)⟩
    have chord := unitIntervalChord_le_of_locally_concave (function ∘ path)
      (continuous.comp path_continuous).continuousOn local_path_concavity
    change (1 - parameter) * function first + parameter * function other ≤
      function (AffineMap.lineMap first other parameter)
    simpa only [Function.comp_apply, path, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] using chord parameter member
  have closure_bound := closure_minimal generic_chord closed_domain
  rw [generic.closure_eq] at closure_bound
  exact closure_bound (Set.mem_univ second)

theorem concaveOn_univ_of_continuous_locally_concave_off_finite_subspaces
    {Space Index : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] [Finite Index]
    (subspaces : Index → Submodule ℝ Space)
    (proper_extensions : ∀ index point,
      subspaces index ⊔ Submodule.span ℝ {point} ≠ ⊤)
    (function : Space → ℝ) (continuous : Continuous function)
    (locally_concave : ∀ point : Space, (∀ index, point ∉ subspaces index) →
      ∃ radius : ℝ, 0 < radius ∧ ConcaveOn ℝ (Metric.ball point radius) function) :
    ConcaveOn ℝ Set.univ function := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ first_weight second_weight first_nonnegative second_nonnegative weight_sum
  have parameter_member : second_weight ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact second_nonnegative
    · linarith
  have bound := chord_le_of_continuous_locally_concave_off_finite_subspaces
    subspaces proper_extensions function continuous locally_concave
    first second second_weight parameter_member
  have first_weight_eq : 1 - second_weight = first_weight := by linarith
  simpa only [AffineMap.lineMap_apply_module, first_weight_eq, smul_eq_mul] using bound

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem divisorSupportFunction_concave_of_adjacentWallCartierInequalities
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (wall_inequalities : fan.HasAdjacentWallCartierInequalities divisor) :
    ConcaveOn ℝ Set.univ (fan.divisorSupportFunction complete regular divisor) := by
  classical
  let full_cones := {cone : fan.cones //
    Submodule.span ℝ (cone.val : Set Ambient) = ⊤}
  have cone_basis_exists : ∀ cone : full_cones,
      ∃ dimension : ℕ, ∃ basis : Basis (Fin dimension) ℤ Lattice,
        cone.val.val = PointedCone.hull ℝ
          (Set.range (fun index => embedding (basis index))) := by
    intro cone
    exact fan.exists_integralBasis_of_fullSpan cone.val.val
      (regular cone.val.property) cone.property
  choose dimension adapted adapted_cone_eq using cone_basis_exists
  let real_adapted := fun cone => fan.lattice.isBaseChange.basis (adapted cone)
  let labels := Σ cone : full_cones,
    {pair : Fin (dimension cone) × Fin (dimension cone) // pair.1 ≠ pair.2}
  let subspaces : labels → Submodule ℝ Ambient := fun label =>
    ((real_adapted label.1).coord label.2.val.1).ker ⊓
      ((real_adapted label.1).coord label.2.val.2).ker
  have proper_extensions : ∀ label point,
      subspaces label ⊔ Submodule.span ℝ {point} ≠ ⊤ := by
    intro label point
    exact BondalThomsen.basis_pair_ker_sup_span_singleton_ne_top
      (real_adapted label.1) label.2.val.1 label.2.val.2 label.2.property point
  apply BondalThomsen.concaveOn_univ_of_continuous_locally_concave_off_finite_subspaces
    subspaces proper_extensions _ (fan.divisorSupportFunction_continuous complete regular divisor)
  intro point avoids
  obtain ⟨cone, cone_member, contains, full_span⟩ :=
    fan.exists_fullSpan_cone complete point
  let chosen : full_cones := ⟨⟨cone, cone_member⟩, full_span⟩
  have chosen_cone : fan.IsConeBasis (adapted chosen) := by
    change PointedCone.hull ℝ
      (Set.range (fun index => embedding (adapted chosen index))) ∈ fan.cones
    rw [← adapted_cone_eq chosen]
    exact cone_member
  have nonnegative_coordinates : ∀ index, 0 ≤ (real_adapted chosen).repr point index := by
    apply (BondalThomsen.mem_basisCone_iff (real_adapted chosen) point).mp
    rw [← fan.coneBasis_hull_eq_realBasis_hull (adapted chosen),
      ← adapted_cone_eq chosen]
    exact contains
  have at_most_one_zero : ∀ first second : Fin (dimension chosen),
      (real_adapted chosen).repr point first = 0 →
      (real_adapted chosen).repr point second = 0 → first = second := by
    intro first second first_zero second_zero
    by_contra distinct
    apply avoids (⟨chosen, ⟨(first, second), distinct⟩⟩ : labels)
    exact ⟨first_zero, second_zero⟩
  exact fan.divisorSupportFunction_locally_concave_of_at_most_one_zero_coordinate
    complete regular divisor wall_inequalities (adapted chosen) chosen_cone point
    nonnegative_coordinates at_most_one_zero

theorem hasRaySupportInequalities_of_adjacentWallCartierInequalities
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (wall_inequalities : fan.HasAdjacentWallCartierInequalities divisor) :
    fan.HasRaySupportInequalities divisor :=
  fan.hasRaySupportInequalities_of_concave complete regular divisor
    (fan.divisorSupportFunction_concave_of_adjacentWallCartierInequalities
      complete regular divisor wall_inequalities)

end TauCeti.Toric.Fan
