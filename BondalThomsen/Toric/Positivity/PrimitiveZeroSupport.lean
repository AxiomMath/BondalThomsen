module

public import BondalThomsen.Toric.Positivity.RealPrimitivePairings

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open Finset Module

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance zeroSupportRayDecidableEq (fan : Fan embedding) : DecidableEq fan.Ray :=
  Classical.decEq _

omit [FiniteDimensional ℝ Ambient] in
theorem realRaySupportGap_eq_zero_of_mem_coneBasis
    (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (values : fan.RealRayCoefficients) (ray : fan.Ray)
    (contains : embedding ray.val ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    fan.realRaySupportGap basis cone_basis values ray = 0 := by
  obtain ⟨index, same⟩ := fan.ray_eq_basis_of_mem_coneBasis basis cone_basis ray contains
  have ray_eq : fan.basisRay basis cone_basis index = ray := Subtype.ext same
  rw [← ray_eq, fan.realRaySupportGap_basisRay]

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.realRayPairing_eq_supportGaps
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (values : fan.RealRayCoefficients) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    relation.realRayPairing values =
      (∑ ray : left, fan.realRaySupportGap basis cone_basis values ray.val) -
        ∑ ray : right, (relation.coefficients ray : ℝ) *
          fan.realRaySupportGap basis cone_basis values ray.val := by
  let datum := fan.realConeDivisorCharacter basis cone_basis values
  have evaluated := congrArg datum relation.lattice_eq
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_natCast] at evaluated
  change (∑ ray : left, values ray.val) -
      (∑ ray : right, (relation.coefficients ray : ℝ) * values ray.val) =
    (∑ ray : left, (values ray.val + datum ray.val.val)) -
      ∑ ray : right, (relation.coefficients ray : ℝ) *
        (values ray.val + datum ray.val.val)
  rw [Finset.sum_add_distrib]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [evaluated]
  ring

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.realRaySupportGap_eq_zero_left_of_pairing_eq_zero
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values)
    (zero_pairing : relation.realRayPairing values = 0) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray : left, ray.val.val) ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    ∀ ray ∈ left, fan.realRaySupportGap basis cone_basis values ray = 0 := by
  have sum_zero : (∑ ray : left, fan.realRaySupportGap basis cone_basis values ray.val) = 0 :=
    (relation.realRayPairing_eq_coneGaps values basis cone_basis contains).symm.trans zero_pairing
  have gaps_zero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (ray : left) (_ : ray ∈ Finset.univ) =>
      support dimension basis cone_basis ray.val)).mp sum_zero
  intro ray member
  exact gaps_zero ⟨ray, member⟩ (Finset.mem_univ _)

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.realRaySupportGap_eq_zero_right_of_sum_mem_coneBasis
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (values : fan.RealRayCoefficients) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray : left, ray.val.val) ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    ∀ ray ∈ right, fan.realRaySupportGap basis cone_basis values ray = 0 := by
  intro ray member
  obtain ⟨index, same⟩ := relation.right_generators_of_sum_mem_coneBasis
    basis cone_basis contains ⟨ray, member⟩
  have ray_eq : fan.basisRay basis cone_basis index = ray := Subtype.ext same
  rw [← ray_eq, fan.realRaySupportGap_basisRay]

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.realRaySupportGap_eq_zero_of_pairing_eq_zero_of_sum_mem
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values)
    (zero_pairing : relation.realRayPairing values = 0) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray : left, ray.val.val) ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    ∀ ray ∈ left ∪ right, fan.realRaySupportGap basis cone_basis values ray = 0 := by
  intro ray member
  rcases Finset.mem_union.mp member with left_member | right_member
  · exact relation.realRaySupportGap_eq_zero_left_of_pairing_eq_zero
      values support zero_pairing basis cone_basis contains ray left_member
  · exact relation.realRaySupportGap_eq_zero_right_of_sum_mem_coneBasis
      values basis cone_basis contains ray right_member

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.realRaySupportGap_eq_zero_of_pairing_eq_zero_of_rightCone_le
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values)
    (zero_pairing : relation.realRayPairing values = 0) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (contains : fan.finiteRayHull right ≤ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    ∀ ray ∈ left ∪ right, fan.realRaySupportGap basis cone_basis values ray = 0 :=
  relation.realRaySupportGap_eq_zero_of_pairing_eq_zero_of_sum_mem
    values support zero_pairing basis cone_basis (contains relation.sum_mem_rightCone)

theorem PrimitiveLatticeRelation.exists_coneBasis_zeroSupport_of_right_union_cone
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values)
    (zero_pairing : relation.realRayPairing values = 0) (extra : Finset fan.Ray)
    (cone : fan.finiteRayHull (right ∪ extra) ∈ fan.cones) :
    ∃ dimension : ℕ, ∃ basis : Basis (Fin dimension) ℤ Lattice,
      ∃ cone_basis : fan.IsConeBasis basis,
        (fan.finiteRayHull (right ∪ extra)).IsFaceOf
          (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ∧
        ∀ ray ∈ left ∪ right ∪ extra,
          fan.realRaySupportGap basis cone_basis values ray = 0 := by
  classical
  obtain ⟨dimension, basis, cone_basis, above⟩ :=
    fan.exists_coneBasis_above complete regular (fan.finiteRayHull (right ∪ extra)) cone
  have right_le : fan.finiteRayHull right ≤ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index))) := by
    apply Submodule.span_le.mpr
    rintro point ⟨ray, member, rfl⟩
    exact above.le (PointedCone.subset_hull
      ⟨ray, Finset.mem_union_left extra member, rfl⟩)
  refine ⟨dimension, basis, cone_basis, above, ?_⟩
  intro ray member
  rcases Finset.mem_union.mp member with relation_member | extra_member
  · exact relation.realRaySupportGap_eq_zero_of_pairing_eq_zero_of_rightCone_le
      values support zero_pairing basis cone_basis right_le ray relation_member
  · exact fan.realRaySupportGap_eq_zero_of_mem_coneBasis basis cone_basis values ray
      (above.le (PointedCone.subset_hull
        ⟨ray, Finset.mem_union_right right extra_member, rfl⟩))

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.realRayPairing_nonpos_of_left_zeroSupport
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (left_zero : ∀ ray ∈ left, fan.realRaySupportGap basis cone_basis values ray = 0) :
    relation.realRayPairing values ≤ 0 := by
  rw [relation.realRayPairing_eq_supportGaps values basis cone_basis]
  have left_sum : (∑ ray : left, fan.realRaySupportGap basis cone_basis values ray.val) = 0 :=
    Finset.sum_eq_zero fun ray _ => left_zero ray.val ray.property
  rw [left_sum]
  have right_sum : 0 ≤ ∑ ray : right, (relation.coefficients ray : ℝ) *
      fan.realRaySupportGap basis cone_basis values ray.val :=
    Finset.sum_nonneg fun ray _ =>
      mul_nonneg (Nat.cast_nonneg _) (support dimension basis cone_basis ray.val)
  linarith

theorem PrimitiveLatticeRelation.realRayPairing_eq_zero_of_left_zeroSupport
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (left_zero : ∀ ray ∈ left, fan.realRaySupportGap basis cone_basis values ray = 0) :
    relation.realRayPairing values = 0 := by
  apply le_antisymm
  · exact relation.realRayPairing_nonpos_of_left_zeroSupport values support basis cone_basis left_zero
  · exact fan.hasNonnegativeRealPrimitivePairings_of_raySupport
      complete regular values support left right relation

theorem PrimitiveLatticeRelation.realRayPairing_eq_zero_of_left_subset_zeroSupport
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (rays : Finset fan.Ray)
    (zero_gaps : ∀ ray ∈ rays, fan.realRaySupportGap basis cone_basis values ray = 0)
    (subset : left ⊆ rays) : relation.realRayPairing values = 0 :=
  relation.realRayPairing_eq_zero_of_left_zeroSupport complete regular values support
    basis cone_basis (fun ray member => zero_gaps ray (subset member))

theorem PrimitiveLatticeRelation.exists_coneBasis_zeroSupport_and_pairings_of_right_union_cone
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values)
    (zero_pairing : relation.realRayPairing values = 0) (extra : Finset fan.Ray)
    (cone : fan.finiteRayHull (right ∪ extra) ∈ fan.cones) :
    ∃ dimension : ℕ, ∃ basis : Basis (Fin dimension) ℤ Lattice,
      ∃ cone_basis : fan.IsConeBasis basis,
        (fan.finiteRayHull (right ∪ extra)).IsFaceOf
          (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ∧
        (∀ ray ∈ left ∪ right ∪ extra,
          fan.realRaySupportGap basis cone_basis values ray = 0) ∧
        ∀ other_left other_right (other : fan.PrimitiveLatticeRelation other_left other_right),
          other_left ⊆ left ∪ right ∪ extra → other.realRayPairing values = 0 := by
  obtain ⟨dimension, basis, cone_basis, above, zero_gaps⟩ :=
    relation.exists_coneBasis_zeroSupport_of_right_union_cone
      complete regular values support zero_pairing extra cone
  refine ⟨dimension, basis, cone_basis, above, zero_gaps, ?_⟩
  intro other_left other_right other subset
  exact other.realRayPairing_eq_zero_of_left_subset_zeroSupport complete regular values support
    basis cone_basis (left ∪ right ∪ extra) zero_gaps subset

end TauCeti.Toric.Fan
