module

public import BondalThomsen.Fan.PrimitiveDivisorPairing
public import BondalThomsen.Fan.PrimitiveRelationDegree
public import BondalThomsen.Toric.Positivity.ActualAmpleStrictSupportCriterion
public import BondalThomsen.Fan.PrimitiveNonfaces
public import BondalThomsen.Toric.Positivity.GeometricNefSupportProof

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open Finset Module

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance primitiveReplacementRayFintype (fan : Fan embedding) : Fintype fan.Ray :=
  Fintype.ofFinite fan.Ray

def PrimitiveLatticeRelation.primitiveSupportReplacementCoefficients
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (coefficients : fan.Ray → ℤ)
    (ray : fan.Ray) : ℤ := by
  classical
  exact coefficients ray - (if ray ∈ left then 1 else 0) +
    (if member : ray ∈ right then (relation.coefficients ⟨ray, member⟩ : ℤ) else 0)

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.primitiveSupportReplacementCoefficients_nonnegative
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (coefficients : fan.Ray → ℤ)
    (nonnegative : ∀ ray, 0 ≤ coefficients ray)
    (positive_left : ∀ ray ∈ left, 0 < coefficients ray) :
    ∀ ray, 0 ≤ relation.primitiveSupportReplacementCoefficients coefficients ray := by
  classical
  intro ray
  unfold primitiveSupportReplacementCoefficients
  have lower := nonnegative ray
  split_ifs with in_left in_right in_right
  · have positive := positive_left ray in_left
    have right_nonnegative : (0 : ℤ) ≤ relation.coefficients ⟨ray, in_right⟩ := Int.natCast_nonneg _
    omega
  · have positive := positive_left ray in_left
    omega
  · have right_nonnegative : (0 : ℤ) ≤ relation.coefficients ⟨ray, in_right⟩ := Int.natCast_nonneg _
    omega
  · omega

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.primitiveSupportReplacementCoefficients_weightedSum
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (coefficients : fan.Ray → ℤ)
    (values : fan.Ray → ℤ) :
    (∑ ray, relation.primitiveSupportReplacementCoefficients coefficients ray * values ray) =
      (∑ ray, coefficients ray * values ray) -
        ((∑ ray : left, values ray.val) -
          ∑ ray : right, (relation.coefficients ray : ℤ) * values ray.val) := by
  classical
  simp only [primitiveSupportReplacementCoefficients, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have left_sum : (∑ ray : fan.Ray, (if ray ∈ left then (1 : ℤ) else 0) * values ray) =
      ∑ ray : left, values ray.val := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_univ_mem]
    exact (Finset.sum_coe_sort left values).symm
  have right_sum : (∑ ray : fan.Ray,
      (if member : ray ∈ right then (relation.coefficients ⟨ray, member⟩ : ℤ) else 0) *
        values ray) = ∑ ray : right, (relation.coefficients ray : ℤ) * values ray.val := by
    simp only [dite_mul, zero_mul]
    exact (Finset.sum_attach_eq_sum_dite right
      (fun ray : right => (relation.coefficients ray : ℤ) * values ray.val)).symm.trans
      (Finset.sum_coe_sort_eq_attach right _).symm
  rw [left_sum, right_sum]
  ring

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.primitiveSupportReplacementCoefficients_latticeSum
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (coefficients : fan.Ray → ℤ) :
    (∑ ray, relation.primitiveSupportReplacementCoefficients coefficients ray • ray.val) =
      ∑ ray, coefficients ray • ray.val := by
  classical
  simp only [primitiveSupportReplacementCoefficients, add_smul, sub_smul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have left_sum : (∑ ray : fan.Ray, (if ray ∈ left then (1 : ℤ) else 0) • ray.val) =
      ∑ ray : left, ray.val.val := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [← Finset.sum_filter, Finset.filter_univ_mem]
    exact (Finset.sum_coe_sort left Subtype.val).symm
  have right_sum : (∑ ray : fan.Ray,
      (if member : ray ∈ right then (relation.coefficients ⟨ray, member⟩ : ℤ) else 0) •
        ray.val) = ∑ ray : right, (relation.coefficients ray : ℤ) • ray.val.val := by
    simp only [dite_smul, zero_smul]
    exact (Finset.sum_attach_eq_sum_dite right
      (fun ray : right => (relation.coefficients ray : ℤ) • ray.val.val)).symm.trans
      (Finset.sum_coe_sort_eq_attach right _).symm
  rw [left_sum, right_sum, ← relation.lattice_eq]
  abel

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.primitiveSupportIntersection_eq_coneGaps
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (divisor : fan.InvariantRayDivisor) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray : left, ray.val.val) ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    relation.divisorIntersection divisor = ∑ ray : left,
      (divisor ray.val + fan.coneDivisorCharacter basis cone_basis divisor ray.val.val) := by
  let datum := fan.coneDivisorCharacter basis cone_basis divisor
  have right_values : ∀ ray : right, datum ray.val.val = -divisor ray.val := by
    intro ray
    obtain ⟨index, same⟩ := relation.right_generators_of_sum_mem_coneBasis
      basis cone_basis contains ray
    dsimp [datum]
    rw [← same, fan.coneDivisorCharacter_basis]
    rw [show fan.basisRay basis cone_basis index = ray.val from Subtype.ext same]
  have evaluated := congrArg datum relation.lattice_eq
  simp only [map_sum, map_zsmul, zsmul_eq_mul, right_values,
    mul_neg, Finset.sum_neg_distrib] at evaluated
  rw [Finset.sum_add_distrib]
  change relation.divisorIntersection divisor = (∑ ray : left, divisor ray.val) +
    ∑ ray : left, datum ray.val.val
  rw [evaluated]
  rfl

theorem PrimitiveLatticeRelation.primitiveSupportIntersection_positive_of_strictSupport
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (strict : fan.HasStrictRaySupportInequalities divisor) :
    0 < relation.divisorIntersection divisor := by
  classical
  obtain ⟨dimension, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (embedding (∑ ray : left, ray.val.val))
  rw [relation.primitiveSupportIntersection_eq_coneGaps divisor basis cone_basis contains]
  obtain ⟨chosen, outside⟩ := relation.primitive_collection.exists_nongenerator_of_coneBasis
    regular basis cone_basis
  have support := fan.hasRaySupportInequalities_of_strict divisor strict
  have nonnegative : ∀ ray : left,
      0 ≤ divisor ray.val + fan.coneDivisorCharacter basis cone_basis divisor ray.val.val := by
    intro ray
    have bound := support dimension basis cone_basis ray.val
    omega
  have bound := Finset.single_le_sum (fun ray _ => nonnegative ray) (Finset.mem_univ chosen)
  have positive := strict dimension basis cone_basis chosen.val outside
  omega

def HasNonnegativePrimitivePairings (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) : Prop :=
  ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
    0 ≤ relation.divisorIntersection divisor

def positiveCoefficientRays (fan : Fan embedding) (coefficients : fan.Ray → ℤ) :
    Finset fan.Ray := by
  classical
  exact Finset.univ.filter fun ray => 0 < coefficients ray

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.primitiveSupportReplacementCoefficients_divisorCost
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (coefficients : fan.Ray → ℤ) (divisor : fan.InvariantRayDivisor) :
    (∑ ray, relation.primitiveSupportReplacementCoefficients coefficients ray * divisor ray) =
      (∑ ray, coefficients ray * divisor ray) - relation.divisorIntersection divisor :=
  relation.primitiveSupportReplacementCoefficients_weightedSum coefficients divisor

theorem exists_primitiveReplacement_of_noncone
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (coefficients : fan.Ray → ℤ) (nonnegative : ∀ ray, 0 ≤ coefficients ray)
    (noncone : fan.finiteRayHull (fan.positiveCoefficientRays coefficients) ∉ fan.cones) :
    ∃ (left right : Finset fan.Ray), ∃ relation : fan.PrimitiveLatticeRelation left right,
      left ⊆ fan.positiveCoefficientRays coefficients ∧
      (∀ ray, 0 ≤ relation.primitiveSupportReplacementCoefficients coefficients ray) ∧
      (∑ ray, relation.primitiveSupportReplacementCoefficients coefficients ray • ray.val) =
        (∑ ray, coefficients ray • ray.val) ∧
      ∀ divisor : fan.InvariantRayDivisor,
        (∑ ray, relation.primitiveSupportReplacementCoefficients coefficients ray * divisor ray) =
          (∑ ray, coefficients ray * divisor ray) - relation.divisorIntersection divisor := by
  classical
  have nonempty : (fan.positiveCoefficientRays coefficients).Nonempty := by
    by_contra empty
    have same := Finset.not_nonempty_iff_eq_empty.mp empty
    obtain ⟨dimension, basis, cone_basis, contains⟩ :=
      fan.exists_coneBasis_containing complete regular (0 : Ambient)
    apply noncone
    rw [same, fan.finiteRayHull_empty]
    exact fan.bot_mem cone_basis
  obtain ⟨left, subset, primitive⟩ := fan.exists_primitiveCollection_subset_of_noncone
    regular (fan.positiveCoefficientRays coefficients) nonempty noncone
  obtain ⟨right, ⟨relation⟩⟩ := primitive.exists_primitiveLatticeRelation complete regular
  refine ⟨left, right, relation, subset,
    relation.primitiveSupportReplacementCoefficients_nonnegative coefficients nonnegative ?_,
    relation.primitiveSupportReplacementCoefficients_latticeSum coefficients,
    relation.primitiveSupportReplacementCoefficients_divisorCost coefficients⟩
  intro ray member
  exact (Finset.mem_filter.mp (subset member)).2

theorem hasNonnegativePrimitivePairings_of_raySupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor) :
    fan.HasNonnegativePrimitivePairings divisor := by
  intro left right relation
  obtain ⟨dimension, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (embedding (∑ ray : left, ray.val.val))
  rw [relation.primitiveSupportIntersection_eq_coneGaps divisor basis cone_basis contains]
  apply Finset.sum_nonneg
  intro ray _
  have bound := support dimension basis cone_basis ray.val
  omega

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.primitiveSupportReplacementCoefficients_supportCost
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (coefficients : fan.Ray → ℤ) (divisor : fan.InvariantRayDivisor)
    (datum : Lattice →+ ℤ) :
    (∑ ray, relation.primitiveSupportReplacementCoefficients coefficients ray *
        (divisor ray + datum ray.val)) =
      (∑ ray, coefficients ray * (divisor ray + datum ray.val)) -
        relation.divisorIntersection divisor := by
  have evaluated := congrArg datum relation.lattice_eq
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_id] at evaluated
  rw [relation.primitiveSupportReplacementCoefficients_weightedSum]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [evaluated]
  simp only [PrimitiveLatticeRelation.divisorIntersection]
  ring

theorem exists_coneSupported_primitiveNormalization
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ampleDivisor : fan.InvariantRayDivisor)
    (strict : fan.HasStrictRaySupportInequalities ampleDivisor)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (divisor : fan.InvariantRayDivisor)
    (pairings : fan.HasNonnegativePrimitivePairings divisor)
    (coefficients : fan.Ray → ℤ) (nonnegative : ∀ ray, 0 ≤ coefficients ray) :
    ∃ normalized : fan.Ray → ℤ,
      (∀ ray, 0 ≤ normalized ray) ∧
      (∑ ray, normalized ray • ray.val) = (∑ ray, coefficients ray • ray.val) ∧
      fan.finiteRayHull (fan.positiveCoefficientRays normalized) ∈ fan.cones ∧
      (∑ ray, normalized ray * divisor ray) ≤ (∑ ray, coefficients ray * divisor ray) := by
  classical
  let datum := fan.coneDivisorCharacter basis cone_basis ampleDivisor
  let cost := fun representation : fan.Ray → ℤ =>
    ∑ ray, representation ray * (ampleDivisor ray + datum ray.val)
  have gaps : ∀ ray, 0 ≤ ampleDivisor ray + datum ray.val := by
    intro ray
    have support := fan.hasRaySupportInequalities_of_strict ampleDivisor strict
    have bound := support dimension basis cone_basis ray
    change 0 ≤ ampleDivisor ray + fan.coneDivisorCharacter basis cone_basis ampleDivisor ray.val
    omega
  have cost_nonnegative : ∀ representation : fan.Ray → ℤ,
      (∀ ray, 0 ≤ representation ray) → 0 ≤ cost representation := by
    intro representation positive
    exact Finset.sum_nonneg fun ray _ => mul_nonneg (positive ray) (gaps ray)
  have normalization : ∀ bound : ℕ, ∀ representation : fan.Ray → ℤ,
      (∀ ray, 0 ≤ representation ray) → (cost representation).toNat = bound →
      ∃ normalized : fan.Ray → ℤ,
        (∀ ray, 0 ≤ normalized ray) ∧
        (∑ ray, normalized ray • ray.val) = (∑ ray, representation ray • ray.val) ∧
        fan.finiteRayHull (fan.positiveCoefficientRays normalized) ∈ fan.cones ∧
        (∑ ray, normalized ray * divisor ray) ≤ (∑ ray, representation ray * divisor ray) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound induction_hypothesis =>
      intro representation positive measure
      by_cases cone : fan.finiteRayHull (fan.positiveCoefficientRays representation) ∈ fan.cones
      · exact ⟨representation, positive, rfl, cone, le_rfl⟩
      · obtain ⟨left, right, relation, subset, replaced_positive, same, cost_identity⟩ :=
          fan.exists_primitiveReplacement_of_noncone complete regular representation positive cone
        let replaced := relation.primitiveSupportReplacementCoefficients representation
        have cost_decreases : cost replaced < cost representation := by
          dsimp [cost, replaced]
          rw [relation.primitiveSupportReplacementCoefficients_supportCost]
          have pairing := relation.primitiveSupportIntersection_positive_of_strictSupport
            complete regular ampleDivisor strict
          omega
        have smaller : (cost replaced).toNat < bound := by
          have first := cost_nonnegative replaced replaced_positive
          have second := cost_nonnegative representation positive
          omega
        obtain ⟨normalized, normalized_positive, normalized_sum, normalized_cone, normalized_cost⟩ :=
          induction_hypothesis (cost replaced).toNat smaller replaced replaced_positive rfl
        refine ⟨normalized, normalized_positive, normalized_sum.trans same, normalized_cone, ?_⟩
        have replaced_cost := cost_identity divisor
        have pairing := pairings left right relation
        change (∑ ray, replaced ray * divisor ray) = _ at replaced_cost
        omega
  exact normalization (cost coefficients).toNat coefficients nonnegative rfl

omit [FiniteDimensional ℝ Ambient] in
theorem coneSupported_coefficients_generators_of_sum_mem
    (fan : Fan embedding) (coefficients : fan.Ray → ℤ)
    (nonnegative : ∀ ray, 0 ≤ coefficients ray)
    (cone : fan.finiteRayHull (fan.positiveCoefficientRays coefficients) ∈ fan.cones)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray, coefficients ray • ray.val) ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :
    ∀ ray, 0 < coefficients ray → ∃ index, basis index = ray.val := by
  classical
  let source := fan.finiteRayHull (fan.positiveCoefficientRays coefficients)
  let target := PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))
  let vectors := fun ray : fan.Ray => if 0 < coefficients ray then embedding ray.val else 0
  have vector_member : ∀ ray, vectors ray ∈ source := by
    intro ray
    dsimp [vectors]
    split_ifs with positive
    · exact PointedCone.subset_hull
        ⟨ray, Finset.mem_filter.mpr ⟨Finset.mem_univ _, positive⟩, rfl⟩
    · exact zero_mem source
  have sum_eq : (∑ ray, (coefficients ray : ℝ) • vectors ray) =
      embedding (∑ ray, coefficients ray • ray.val) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ray _
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    dsimp [vectors]
    split_ifs with positive
    · rfl
    · have zero : coefficients ray = 0 := by have lower := nonnegative ray; omega
      simp [zero]
  have sum_in_source : (∑ ray, (coefficients ray : ℝ) • vectors ray) ∈ source := by
    exact Submodule.sum_mem _ fun ray _ =>
      source.smul_mem (by exact_mod_cast nonnegative ray) (vector_member ray)
  have sum_in_intersection : (∑ ray, (coefficients ray : ℝ) • vectors ray) ∈
      source ⊓ target := ⟨sum_in_source, sum_eq.symm ▸ contains⟩
  have face := fan.inf_isFaceOf_left cone cone_basis
  intro ray positive
  have member := face.mem_of_sum_smul_mem vector_member
    (fun selected => by exact_mod_cast nonnegative selected) sum_in_intersection ray
    (by exact_mod_cast positive)
  have target_member : embedding ray.val ∈ target := by
    have target_contains := member.2
    change vectors ray ∈ target at target_contains
    simpa only [vectors, ite_eq_left positive] using target_contains
  exact fan.ray_eq_basis_of_mem_coneBasis basis cone_basis ray target_member

omit [FiniteDimensional ℝ Ambient] in
theorem coneSupported_coefficients_divisorCost
    (fan : Fan embedding) (coefficients : fan.Ray → ℤ)
    (nonnegative : ∀ ray, 0 ≤ coefficients ray)
    (cone : fan.finiteRayHull (fan.positiveCoefficientRays coefficients) ∈ fan.cones)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray, coefficients ray • ray.val) ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))
    (divisor : fan.InvariantRayDivisor) :
    (∑ ray, coefficients ray * divisor ray) =
      -fan.coneDivisorCharacter basis cone_basis divisor (∑ ray, coefficients ray • ray.val) := by
  classical
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ray _
  rw [map_zsmul, zsmul_eq_mul]
  by_cases positive : 0 < coefficients ray
  · obtain ⟨index, same⟩ := fan.coneSupported_coefficients_generators_of_sum_mem
      coefficients nonnegative cone basis cone_basis contains ray positive
    have equation : fan.coneDivisorCharacter basis cone_basis divisor ray.val = -divisor ray := by
      rw [← same, fan.coneDivisorCharacter_basis]
      rw [show fan.basisRay basis cone_basis index = ray from Subtype.ext same]
    rw [equation]
    simp only [Int.cast_id]
    ring
  · have zero : coefficients ray = 0 := by have lower := nonnegative ray; omega
    simp [zero]

def basisRayCoefficients (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (vector : Lattice) (ray : fan.Ray) : ℤ := by
  classical
  exact ∑ index, if fan.basisRay basis cone_basis index = ray then basis.repr vector index else 0

omit [FiniteDimensional ℝ Ambient] in
theorem basisRayCoefficients_nonnegative (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (vector : Lattice) (nonnegative : ∀ index, 0 ≤ basis.repr vector index) :
    ∀ ray, 0 ≤ fan.basisRayCoefficients basis cone_basis vector ray := by
  classical
  intro ray
  exact Finset.sum_nonneg fun index _ => by
    change 0 ≤ if fan.basisRay basis cone_basis index = ray then basis.repr vector index else 0
    split_ifs
    · exact nonnegative index
    · exact le_rfl

omit [FiniteDimensional ℝ Ambient] in
theorem basisRayCoefficients_latticeSum (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (vector : Lattice) :
    (∑ ray, fan.basisRayCoefficients basis cone_basis vector ray • ray.val) = vector := by
  classical
  simp only [basisRayCoefficients, Finset.sum_smul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ index, basis.repr vector index • basis index := by
      apply Finset.sum_congr rfl
      intro index _
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
      rfl
    _ = vector := basis.sum_repr vector

omit [FiniteDimensional ℝ Ambient] in
theorem basisRayCoefficients_divisorCost (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (vector : Lattice) (divisor : fan.InvariantRayDivisor) :
    (∑ ray, fan.basisRayCoefficients basis cone_basis vector ray * divisor ray) =
      -fan.coneDivisorCharacter basis cone_basis divisor vector := by
  classical
  simp only [basisRayCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ index, basis.repr vector index * divisor (fan.basisRay basis cone_basis index) := by
      apply Finset.sum_congr rfl
      intro index _
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    _ = -fan.coneDivisorCharacter basis cone_basis divisor vector := by
      conv_rhs => rw [← basis.sum_repr vector, map_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro index _
      rw [map_zsmul, zsmul_eq_mul, fan.coneDivisorCharacter_basis]
      simp only [Int.cast_id]
      ring

theorem hasRaySupportInequalities_of_nonnegativePrimitivePairings_of_strictSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ampleDivisor : fan.InvariantRayDivisor)
    (strict : fan.HasStrictRaySupportInequalities ampleDivisor)
    (divisor : fan.InvariantRayDivisor)
    (pairings : fan.HasNonnegativePrimitivePairings divisor) :
    fan.HasRaySupportInequalities divisor := by
  classical
  intro dimension basis cone_basis selected
  let upper : Lattice := basis.equivFun.symm (fun index => max (basis.repr selected.val index) 0)
  have upper_coordinates : ∀ index, basis.repr upper index = max (basis.repr selected.val index) 0 := by
    intro index
    change basis.equivFun upper index = _
    simp only [upper, LinearEquiv.apply_symm_apply]
  have upper_nonnegative : ∀ index, 0 ≤ basis.repr upper index := by
    intro index
    rw [upper_coordinates]
    exact le_max_right _ _
  have lower_nonnegative : ∀ index, 0 ≤ basis.repr (upper - selected.val) index := by
    intro index
    rw [map_sub, Finsupp.sub_apply, upper_coordinates]
    exact sub_nonneg.mpr (le_max_left _ _)
  let lower := fan.basisRayCoefficients basis cone_basis (upper - selected.val)
  let coefficients := fun ray : fan.Ray => lower ray + if selected = ray then 1 else 0
  have positive : ∀ ray, 0 ≤ coefficients ray := by
    intro ray
    have lower_positive := fan.basisRayCoefficients_nonnegative basis cone_basis
      (upper - selected.val) lower_nonnegative ray
    change 0 ≤ lower ray at lower_positive
    dsimp [coefficients]
    split_ifs <;> omega
  have sum_eq : (∑ ray, coefficients ray • ray.val) = upper := by
    simp only [coefficients, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul]
    rw [fan.basisRayCoefficients_latticeSum, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_univ _), sub_add_cancel]
  have cost_eq : (∑ ray, coefficients ray * divisor ray) =
      -fan.coneDivisorCharacter basis cone_basis divisor (upper - selected.val) + divisor selected := by
    simp only [coefficients, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
    rw [fan.basisRayCoefficients_divisorCost, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_univ _)]
  obtain ⟨normalized, normalized_positive, normalized_sum, normalized_cone, normalized_cost⟩ :=
    fan.exists_coneSupported_primitiveNormalization complete regular ampleDivisor strict
      basis cone_basis divisor pairings coefficients positive
  have normalized_contains : embedding (∑ ray, normalized ray • ray.val) ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
    rw [normalized_sum, sum_eq]
    exact fan.mem_coneBasis_of_repr_nonnegative basis upper upper_nonnegative
  rw [fan.coneSupported_coefficients_divisorCost normalized normalized_positive normalized_cone
    basis cone_basis normalized_contains divisor, normalized_sum, sum_eq, cost_eq, map_sub]
    at normalized_cost
  omega

theorem exists_strictSupportDivisor_of_projective
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    ∃ ampleDivisor : fan.InvariantRayDivisor,
      fan.HasStrictRaySupportInequalities ampleDivisor := by
  obtain ⟨Index, finite, closedMap, closed, overBase⟩ := projective
  let := finite
  let := closed
  let bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular) :=
    ⟨BondalThomsen.polynomialProjDegreeOnePullbackSheaf 𝕜 Index closedMap,
      BondalThomsen.polynomialProjDegreeOnePullbackSheaf_isInvertible 𝕜 Index closedMap⟩
  let : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (fan.algebraicRealization 𝕜 regular) bundle.obj := bundle.property
  have ample : AlgebraicGeometry.IsAmple bundle.obj :=
    BondalThomsen.polynomialProjDegreeOnePullbackSheaf_isAmple_of_closedImmersion 𝕜 Index closedMap
  obtain ⟨ampleDivisor, ⟨comparison⟩⟩ :=
    fan.invertibleSheaf_exists_invariantDivisorRepresentative 𝕜 complete regular bundle
  exact ⟨ampleDivisor,
    (fan.invertibleSheaf_isAmple_iff_representative_strictSupport 𝕜
      complete regular bundle ampleDivisor comparison).mp ample⟩

theorem invariantDivisor_nonnegativePrimitivePairings_iff_raySupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (divisor : fan.InvariantRayDivisor) :
    fan.HasNonnegativePrimitivePairings divisor ↔ fan.HasRaySupportInequalities divisor := by
  obtain ⟨ampleDivisor, strict⟩ := fan.exists_strictSupportDivisor_of_projective 𝕜 complete regular projective
  exact ⟨fan.hasRaySupportInequalities_of_nonnegativePrimitivePairings_of_strictSupport
      complete regular ampleDivisor strict divisor,
    fan.hasNonnegativePrimitivePairings_of_raySupport complete regular divisor⟩

variable {𝕜} in
local instance primitiveSupportBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

theorem invariantDivisor_isNef_iff_allPrimitivePairings
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (divisor : fan.InvariantRayDivisor) :
    AlgebraicGeometry.IsNef (baseField := 𝕜)
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ↔
      fan.HasNonnegativePrimitivePairings divisor :=
  (fan.invariantDivisor_isNef_iff_raySupport 𝕜 complete regular divisor).trans
    (fan.invariantDivisor_nonnegativePrimitivePairings_iff_raySupport 𝕜
      complete regular projective divisor).symm

theorem invariantClass_isNef_iff_allPrimitivePairings
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (divisorClass : fan.InvariantRayDivisorClass) :
    BondalThomsen.SchemeLineBundleClassIsNef (baseField := 𝕜)
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass)) ↔
      ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
        0 ≤ relation.classPairing divisorClass := by
  obtain ⟨divisor, rfl⟩ := QuotientAddGroup.mk_surjective divisorClass
  change BondalThomsen.SchemeLineBundleClassIsNef (baseField := 𝕜)
    (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular
      (fan.invariantRayDivisorClass divisor))) ↔
      ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
        0 ≤ relation.classPairing (fan.invariantRayDivisorClass divisor)
  rw [fan.invariantDivisorPicardRealization_apply 𝕜]
  change BondalThomsen.SchemeLineBundleClassIsNef (baseField := 𝕜)
    (AlgebraicGeometry.LineBundleClass.mk (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)) ↔ _
  rw [BondalThomsen.schemeLineBundleClassIsNef_mk_iff]
  simpa only [HasNonnegativePrimitivePairings, PrimitiveLatticeRelation.classPairing_mk] using
    fan.invariantDivisor_isNef_iff_allPrimitivePairings 𝕜 complete regular projective divisor

end TauCeti.Toric.Fan
