module

public import BondalThomsen.Fan.Boundary
public import BondalThomsen.Fan.ConeBasisFaces
public import BondalThomsen.DeepFan.Coordinates
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace BondalThomsen

open Set

variable {Ambient : Type*} [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]

theorem exposedFace_eq_convexHull_inter (generators : Set Ambient) (face : Set Ambient)
    (exposed : IsExposed ℝ (convexHull ℝ generators) face) :
    face = convexHull ℝ (generators ∩ face) := by
  classical
  obtain empty | nonempty := face.eq_empty_or_nonempty
  · simp [empty]
  obtain ⟨functional, face_eq⟩ := exposed nonempty
  obtain ⟨point, point_member⟩ := nonempty
  have point_max : point ∈ convexHull ℝ generators ∧
      ∀ vector ∈ convexHull ℝ generators, functional vector ≤ functional point := by
    rwa [face_eq] at point_member
  let gap : Ambient →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ Ambient (functional point) - functional.toLinearMap.toAffineMap
  have nonnegative : ∀ vector ∈ generators, 0 ≤ gap vector := by
    intro vector member
    exact sub_nonneg.mpr (point_max.2 vector (subset_convexHull ℝ generators member))
  have zero_slice : convexHull ℝ generators ∩ {vector | gap vector = 0} = face := by
    rw [face_eq]
    ext vector
    constructor
    · rintro ⟨member, equality⟩
      change functional point - functional vector = 0 at equality
      have same := sub_eq_zero.mp equality
      exact ⟨member, fun other other_member => same ▸ point_max.2 other other_member⟩
    · rintro ⟨member, maximal⟩
      change vector ∈ convexHull ℝ generators ∧ functional point - functional vector = 0
      exact ⟨member, sub_eq_zero.mpr (le_antisymm
        (maximal point point_max.1) (point_max.2 vector member))⟩
  have generator_slice : generators ∩ {vector | gap vector = 0} = generators ∩ face := by
    ext vector
    constructor
    · rintro ⟨member, equality⟩
      exact ⟨member, zero_slice ▸ ⟨subset_convexHull ℝ generators member, equality⟩⟩
    · rintro ⟨member, face_member⟩
      exact ⟨member, (zero_slice.symm ▸ face_member).2⟩
  have slice := convexHull_inter_affine_zero_of_nonneg_set generators gap nonnegative
  rwa [zero_slice, generator_slice] at slice

theorem properExposedFace_subset_frontier (points face : Set Ambient)
    (exposed : IsExposed ℝ points face) (proper : face ≠ points) :
    face ⊆ frontier points := by
  intro point member
  obtain ⟨functional, face_eq⟩ := exposed ⟨point, member⟩
  have point_max : point ∈ points ∧ ∀ vector ∈ points, functional vector ≤ functional point := by
    rwa [face_eq] at member
  have nonzero : functional ≠ 0 := by
    intro zero
    apply proper
    rw [face_eq, zero]
    ext vector
    simp
  apply (mem_frontier_iff_notMem_interior point_max.1).mpr
  intro point_interior
  have halfspace_interior : point ∈ interior (functional ⁻¹' Set.Iic (functional point)) :=
    interior_mono (fun vector vector_member => point_max.2 vector vector_member) point_interior
  have open_map := functional.isOpenMap_of_ne_zero nonzero
  have strict := open_map.interior_preimage_subset_preimage_interior halfspace_interior
  rw [interior_Iic] at strict
  exact lt_irrefl (functional point) strict

end BondalThomsen

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] [Nontrivial Ambient]
    {embedding : Lattice →+ Ambient}

theorem properFace_generators_subset_basis (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (face : Set Ambient) (exposed : IsExposed ℝ fan.rayPolytope face)
    (proper : face ≠ fan.rayPolytope) :
    ∃ basis : Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis basis ∧
      fan.rayGenerators ∩ face ⊆ Set.range (fun index => embedding (basis index)) := by
  classical
  let selected := fan.rayGenerators ∩ face
  have face_eq : face = convexHull ℝ selected :=
    exposedFace_eq_convexHull_inter fan.rayGenerators face exposed
  obtain empty | nonempty := selected.eq_empty_or_nonempty
  · obtain ⟨size, basis, cone_basis, _⟩ := fan.exists_coneBasis_containing complete regular 0
    have size_eq : size = dimension := by
      have ranks := (finrank_eq_card_basis basis).symm.trans (finrank_eq_card_basis reference)
      simpa only [Fintype.card_fin] using ranks
    subst size
    refine ⟨basis, cone_basis, ?_⟩
    change selected ⊆ _
    rw [empty]
    exact empty_subset _
  let : Finite selected := (fan.rayGenerators_finite.subset inter_subset_left).to_subtype
  let := Fintype.ofFinite selected
  have index_nonempty : Nonempty selected := nonempty.to_subtype
  let := index_nonempty
  let weight : ℝ := (Fintype.card selected : ℝ)⁻¹
  have cardinal_positive : (0 : ℝ) < Fintype.card selected := by
    exact_mod_cast Fintype.card_pos
  have weight_positive : 0 < weight := inv_pos.mpr cardinal_positive
  have weights_sum : ∑ _ : selected, weight = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, weight]
    exact mul_inv_cancel₀ cardinal_positive.ne'
  let point := ∑ vector : selected, weight • (vector : Ambient)
  have point_member : point ∈ face := by
    exact (exposed.convex (convex_convexHull ℝ fan.rayGenerators)).sum_mem
      (fun _ _ => weight_positive.le) weights_sum (fun vector _ => vector.property.2)
  have boundary := properExposedFace_subset_frontier fan.rayPolytope face exposed proper point_member
  obtain ⟨basis, cone_basis, simplex_member⟩ :=
    fan.frontier_covered_by_basisFaces complete regular deep reference point boundary
  have point_value : fan.supportingFunctional basis point = 1 := by
    rw [← fan.rayPolytope_inter_supportingHyperplane deep basis cone_basis] at simplex_member
    exact simplex_member.2
  have bounds : ∀ vector : selected, fan.supportingFunctional basis (vector : Ambient) ≤ 1 :=
    fun vector => fan.rayPolytope_supporting_le_one deep basis cone_basis
      (subset_convexHull ℝ fan.rayGenerators vector.property.1)
  have sums_equal : ∑ vector : selected,
      weight * fan.supportingFunctional basis (vector : Ambient) =
      ∑ _ : selected, weight := by
    rw [weights_sum]
    simpa only [point, map_sum, map_smul, smul_eq_mul] using point_value
  have terms_equal := (Finset.sum_eq_sum_iff_of_le (fun vector _ =>
    mul_le_of_le_one_right weight_positive.le (bounds vector))).mp sums_equal
  refine ⟨basis, cone_basis, ?_⟩
  intro vector member
  have equality : fan.supportingFunctional basis vector = 1 := by
    have term := terms_equal ⟨vector, member⟩ (Finset.mem_univ _)
    exact (mul_left_cancel₀ weight_positive.ne' (term.trans (mul_one weight).symm))
  rw [← fan.supportingGenerators_eq deep basis cone_basis]
  exact ⟨member.1, equality⟩

end TauCeti.Toric.Fan
