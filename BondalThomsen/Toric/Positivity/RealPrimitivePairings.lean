module

public import BondalThomsen.Toric.Positivity.PrimitivePairingSupportCriterion
public import BondalThomsen.Toric.Positivity.PrimitiveNumericalClass
public import BondalThomsen.Fan.PrimitiveRelationFiniteness
public import Mathlib.Topology.Instances.Rat

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

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance realPrimitiveRayFintype (fan : Fan embedding) : Fintype fan.Ray :=
  Fintype.ofFinite fan.Ray

abbrev RealRayCoefficients (fan : Fan embedding) := fan.Ray → ℝ

def PrimitiveLatticeRelation.realRayPairing
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) : fan.RealRayCoefficients →ₗ[ℝ] ℝ where
  toFun values := (∑ ray : left, values ray.val) -
    ∑ ray : right, (relation.coefficients ray : ℝ) * values ray.val
  map_add' first second := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' scalar values := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm, mul_sub]

omit [FiniteDimensional ℝ Ambient] in
@[simp] theorem PrimitiveLatticeRelation.realRayPairing_integral
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (divisor : fan.InvariantRayDivisor) :
    relation.realRayPairing (fun ray => (divisor ray : ℝ)) =
      (relation.divisorIntersection divisor : ℝ) := by
  simp [realRayPairing, divisorIntersection]

def realConeDivisorCharacter (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (values : fan.RealRayCoefficients) : Lattice →+ ℝ :=
  (basis.constr ℝ (fun index => -values (fan.basisRay basis cone_basis index))).toAddMonoidHom

omit [FiniteDimensional ℝ Ambient] in
@[simp] theorem realConeDivisorCharacter_basis (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (values : fan.RealRayCoefficients) (index : Fin dimension) :
    fan.realConeDivisorCharacter basis cone_basis values (basis index) =
      -values (fan.basisRay basis cone_basis index) :=
  basis.constr_basis ℝ _ index

def realRaySupportGap (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (values : fan.RealRayCoefficients) (ray : fan.Ray) : ℝ :=
  values ray + fan.realConeDivisorCharacter basis cone_basis values ray.val

def HasRealRaySupportInequalities (fan : Fan embedding)
    (values : fan.RealRayCoefficients) : Prop :=
  ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (ray : fan.Ray),
      0 ≤ fan.realRaySupportGap basis cone_basis values ray

def HasNonnegativeRealPrimitivePairings (fan : Fan embedding)
    (values : fan.RealRayCoefficients) : Prop :=
  ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
    0 ≤ relation.realRayPairing values

omit [FiniteDimensional ℝ Ambient] in
@[simp] theorem realRaySupportGap_basisRay (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (values : fan.RealRayCoefficients) (index : Fin dimension) :
    fan.realRaySupportGap basis cone_basis values (fan.basisRay basis cone_basis index) = 0 := by
  simp [realRaySupportGap, basisRay]

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.primitiveSupportReplacementCoefficients_realCost
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (coefficients : fan.Ray → ℤ) (values : fan.RealRayCoefficients) :
    (∑ ray, (relation.primitiveSupportReplacementCoefficients coefficients ray : ℝ) * values ray) =
      (∑ ray, (coefficients ray : ℝ) * values ray) - relation.realRayPairing values := by
  classical
  simp only [primitiveSupportReplacementCoefficients, Int.cast_add, Int.cast_sub,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have left_sum : (∑ ray : fan.Ray, ((if ray ∈ left then 1 else 0 : ℤ) : ℝ) * values ray) =
      ∑ ray : left, values ray.val := by
    simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_univ_mem]
    exact (Finset.sum_coe_sort left values).symm
  have right_sum : (∑ ray : fan.Ray,
      ((if member : ray ∈ right then (relation.coefficients ⟨ray, member⟩ : ℤ) else 0 : ℤ) : ℝ) *
        values ray) = ∑ ray : right, (relation.coefficients ray : ℝ) * values ray.val := by
    simp only [apply_dite (fun integer : ℤ => (integer : ℝ)),
      Int.cast_natCast, Int.cast_zero, dite_mul, zero_mul]
    exact (Finset.sum_attach_eq_sum_dite right
      (fun ray : right => (relation.coefficients ray : ℝ) * values ray.val)).symm.trans
      (Finset.sum_coe_sort_eq_attach right _).symm
  rw [left_sum, right_sum]
  change _ = _ - ((∑ ray : left, values ray.val) -
    ∑ ray : right, (relation.coefficients ray : ℝ) * values ray.val)
  ring

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.realRayPairing_eq_coneGaps
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (values : fan.RealRayCoefficients) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray : left, ray.val.val) ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    relation.realRayPairing values = ∑ ray : left,
      fan.realRaySupportGap basis cone_basis values ray.val := by
  let datum := fan.realConeDivisorCharacter basis cone_basis values
  have right_values : ∀ ray : right, datum ray.val.val = -values ray.val := by
    intro ray
    obtain ⟨index, same⟩ := relation.right_generators_of_sum_mem_coneBasis
      basis cone_basis contains ray
    dsimp [datum]
    rw [← same, fan.realConeDivisorCharacter_basis]
    rw [show fan.basisRay basis cone_basis index = ray.val from Subtype.ext same]
  have evaluated := congrArg datum relation.lattice_eq
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_natCast, right_values,
    mul_neg, Finset.sum_neg_distrib] at evaluated
  change (∑ ray : left, values ray.val) -
      (∑ ray : right, (relation.coefficients ray : ℝ) * values ray.val) =
    ∑ ray : left, (values ray.val + datum ray.val.val)
  rw [Finset.sum_add_distrib, evaluated]
  ring

theorem hasNonnegativeRealPrimitivePairings_of_raySupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (values : fan.RealRayCoefficients) (support : fan.HasRealRaySupportInequalities values) :
    fan.HasNonnegativeRealPrimitivePairings values := by
  intro left right relation
  obtain ⟨dimension, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (embedding (∑ ray : left, ray.val.val))
  rw [relation.realRayPairing_eq_coneGaps values basis cone_basis contains]
  exact Finset.sum_nonneg fun ray _ => support dimension basis cone_basis ray.val

theorem exists_coneSupported_realPrimitiveNormalization
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ampleDivisor : fan.InvariantRayDivisor)
    (strict : fan.HasStrictRaySupportInequalities ampleDivisor)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (values : fan.RealRayCoefficients)
    (pairings : fan.HasNonnegativeRealPrimitivePairings values)
    (coefficients : fan.Ray → ℤ) (nonnegative : ∀ ray, 0 ≤ coefficients ray) :
    ∃ normalized : fan.Ray → ℤ,
      (∀ ray, 0 ≤ normalized ray) ∧
      (∑ ray, normalized ray • ray.val) = (∑ ray, coefficients ray • ray.val) ∧
      fan.finiteRayHull (fan.positiveCoefficientRays normalized) ∈ fan.cones ∧
      (∑ ray, (normalized ray : ℝ) * values ray) ≤
        (∑ ray, (coefficients ray : ℝ) * values ray) := by
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
        (∑ ray, (normalized ray : ℝ) * values ray) ≤
          (∑ ray, (representation ray : ℝ) * values ray) := by
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
        have replaced_cost := relation.primitiveSupportReplacementCoefficients_realCost
          representation values
        have pairing := pairings left right relation
        change (∑ ray, (replaced ray : ℝ) * values ray) = _ at replaced_cost
        linarith
  exact normalization (cost coefficients).toNat coefficients nonnegative rfl

omit [FiniteDimensional ℝ Ambient] in
theorem coneSupported_coefficients_realCost
    (fan : Fan embedding) (coefficients : fan.Ray → ℤ)
    (nonnegative : ∀ ray, 0 ≤ coefficients ray)
    (cone : fan.finiteRayHull (fan.positiveCoefficientRays coefficients) ∈ fan.cones)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray, coefficients ray • ray.val) ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))
    (values : fan.RealRayCoefficients) :
    (∑ ray, (coefficients ray : ℝ) * values ray) =
      -fan.realConeDivisorCharacter basis cone_basis values
        (∑ ray, coefficients ray • ray.val) := by
  classical
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ray _
  rw [map_zsmul, zsmul_eq_mul]
  by_cases positive : 0 < coefficients ray
  · obtain ⟨index, same⟩ := fan.coneSupported_coefficients_generators_of_sum_mem
      coefficients nonnegative cone basis cone_basis contains ray positive
    have equation : fan.realConeDivisorCharacter basis cone_basis values ray.val = -values ray := by
      rw [← same, fan.realConeDivisorCharacter_basis]
      rw [show fan.basisRay basis cone_basis index = ray from Subtype.ext same]
    rw [equation]
    ring
  · have zero : coefficients ray = 0 := by have lower := nonnegative ray; omega
    simp [zero]

omit [FiniteDimensional ℝ Ambient] in
theorem basisRayCoefficients_realCost (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (vector : Lattice) (values : fan.RealRayCoefficients) :
    (∑ ray, (fan.basisRayCoefficients basis cone_basis vector ray : ℝ) * values ray) =
      -fan.realConeDivisorCharacter basis cone_basis values vector := by
  classical
  simp only [basisRayCoefficients, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ index, (basis.repr vector index : ℝ) * values (fan.basisRay basis cone_basis index) := by
      apply Finset.sum_congr rfl
      intro index _
      simp only [Int.cast_ite, Int.cast_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    _ = -fan.realConeDivisorCharacter basis cone_basis values vector := by
      conv_rhs => rw [← basis.sum_repr vector, map_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro index _
      rw [map_zsmul, zsmul_eq_mul, fan.realConeDivisorCharacter_basis]
      ring

theorem hasRealRaySupportInequalities_of_nonnegativePrimitivePairings_of_strictSupport
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ampleDivisor : fan.InvariantRayDivisor)
    (strict : fan.HasStrictRaySupportInequalities ampleDivisor)
    (values : fan.RealRayCoefficients)
    (pairings : fan.HasNonnegativeRealPrimitivePairings values) :
    fan.HasRealRaySupportInequalities values := by
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
  have cost_eq : (∑ ray, (coefficients ray : ℝ) * values ray) =
      -fan.realConeDivisorCharacter basis cone_basis values (upper - selected.val) + values selected := by
    simp only [coefficients, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
      add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
    rw [fan.basisRayCoefficients_realCost, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_univ _)]
  obtain ⟨normalized, normalized_positive, normalized_sum, normalized_cone, normalized_cost⟩ :=
    fan.exists_coneSupported_realPrimitiveNormalization complete regular ampleDivisor strict
      basis cone_basis values pairings coefficients positive
  have normalized_contains : embedding (∑ ray, normalized ray • ray.val) ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
    rw [normalized_sum, sum_eq]
    exact fan.mem_coneBasis_of_repr_nonnegative basis upper upper_nonnegative
  rw [fan.coneSupported_coefficients_realCost normalized normalized_positive normalized_cone
    basis cone_basis normalized_contains values, normalized_sum, sum_eq, cost_eq, map_sub]
    at normalized_cost
  change 0 ≤ values selected + fan.realConeDivisorCharacter basis cone_basis values selected.val
  linarith

theorem hasRealRaySupportInequalities_of_nonnegativePrimitivePairings
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (values : fan.RealRayCoefficients)
    (pairings : fan.HasNonnegativeRealPrimitivePairings values) :
    fan.HasRealRaySupportInequalities values := by
  obtain ⟨ampleDivisor, strict⟩ :=
    fan.exists_strictSupportDivisor_of_projective 𝕜 complete regular projective
  exact fan.hasRealRaySupportInequalities_of_nonnegativePrimitivePairings_of_strictSupport
    complete regular ampleDivisor strict values pairings

variable {𝕜} in
local instance realPrimitiveBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def realRayNumericalEvaluation (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    fan.RealRayCoefficients →ₗ[ℝ] ℝ where
  toFun values := fan.numericalRealPicardFunctional 𝕜 complete regular values numericalClass
  map_add' first second := by
    simp only [numericalRealPicardFunctional, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar values := by
    simp only [numericalRealPicardFunctional, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem realRayNumericalEvaluation_continuous (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    Continuous (fan.realRayNumericalEvaluation 𝕜 complete regular numericalClass) :=
  LinearMap.continuous_of_finiteDimensional _

omit [FiniteDimensional ℝ Ambient] in
theorem exists_positive_real_integer_multiple_rayCoefficients (fan : Fan embedding)
    (coefficients : fan.Ray → ℚ) :
    ∃ scalar : ℝ, 0 < scalar ∧ ∃ divisor : fan.InvariantRayDivisor,
      (fun ray => (divisor ray : ℝ)) = scalar • (fun ray => (coefficients ray : ℝ)) := by
  classical
  obtain ⟨scalar, scalar_ne, divisor, equality⟩ :=
    fan.exists_integer_multiple_rayCoefficients coefficients
  have coordinates : ∀ ray, (scalar : ℝ) * (coefficients ray : ℝ) = (divisor ray : ℝ) := by
    intro ray
    have rationalEquality := congrFun equality ray
    simp only [Pi.smul_apply, smul_eq_mul] at rationalEquality
    exact_mod_cast rationalEquality
  rcases lt_or_gt_of_ne scalar_ne with negative | positive
  · refine ⟨-(scalar : ℝ), by exact_mod_cast neg_pos.mpr negative, -divisor, ?_⟩
    funext ray
    simp only [Finsupp.neg_apply, Int.cast_neg, Pi.smul_apply, smul_eq_mul,
      neg_mul, coordinates]
  · refine ⟨(scalar : ℝ), by exact_mod_cast positive, divisor, ?_⟩
    funext ray
    exact (coordinates ray).symm

theorem numericalRealPicardFunctional_integralCurve_integerDivisor
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    fan.numericalRealPicardFunctional 𝕜 complete regular (fun ray => (divisor ray : ℝ))
        (BondalThomsen.integralCurveNumericalClass curve) =
      (BondalThomsen.integralCurvePicardDegree curve
        (fan.invariantDivisorPicardRealization 𝕜 complete regular
          (fan.invariantRayDivisorClass divisor)) : ℝ) := by
  have rationalEquality := fan.rationalPicardRayFunctional_integerDivisor 𝕜 complete regular
    (BondalThomsen.integralCurvePicardDegree curve) divisor
  have realEquality := congrArg (fun rational : ℚ => (rational : ℝ)) rationalEquality
  simpa only [rationalPicardRayFunctional, numericalRealPicardFunctional,
    LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
    BondalThomsen.integralCurveNumericalClass_apply] using realEquality

theorem rationalRayCoefficients_nonnegative_on_integralCurve_of_primitivePairings
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (coefficients : fan.Ray → ℚ)
    (pairings : fan.HasNonnegativeRealPrimitivePairings (fun ray => (coefficients ray : ℝ)))
    (curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular
      (fun ray => (coefficients ray : ℝ)) (BondalThomsen.integralCurveNumericalClass curve) := by
  obtain ⟨scalar, positive, divisor, equality⟩ :=
    fan.exists_positive_real_integer_multiple_rayCoefficients coefficients
  have integralPairings : fan.HasNonnegativePrimitivePairings divisor := by
    intro left right relation
    have nonnegative := mul_nonneg positive.le (pairings left right relation)
    have scaled : relation.realRayPairing (fun ray => (divisor ray : ℝ)) =
        scalar * relation.realRayPairing (fun ray => (coefficients ray : ℝ)) := by
      rw [equality, map_smul, smul_eq_mul]
    rw [← scaled, relation.realRayPairing_integral] at nonnegative
    exact_mod_cast nonnegative
  have nef := (fan.invariantClass_isNef_iff_allPrimitivePairings 𝕜 complete regular projective
    (fan.invariantRayDivisorClass divisor)).mpr integralPairings
  have degree := (BondalThomsen.schemeLineBundleClassIsNef_iff_curveDegree_nonnegative _).mp nef curve
  change 0 ≤ (BondalThomsen.integralCurvePicardDegree curve
    (fan.invariantDivisorPicardRealization 𝕜 complete regular
      (fan.invariantRayDivisorClass divisor)) : ℝ) at degree
  rw [← fan.numericalRealPicardFunctional_integralCurve_integerDivisor 𝕜
    complete regular divisor curve] at degree
  change 0 ≤ fan.realRayNumericalEvaluation 𝕜 complete regular
    (BondalThomsen.integralCurveNumericalClass curve) (fun ray => (divisor ray : ℝ)) at degree
  rw [equality, map_smul, smul_eq_mul] at degree
  exact (mul_nonneg_iff_of_pos_left positive).mp degree

theorem realRayCoefficients_nonnegative_on_integralCurve_of_primitivePairings
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (values : fan.RealRayCoefficients)
    (pairings : fan.HasNonnegativeRealPrimitivePairings values)
    (curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular values
      (BondalThomsen.integralCurveNumericalClass curve) := by
  classical
  let := fan.primitiveRelationIndex_finite regular
  let evaluation := fan.realRayNumericalEvaluation 𝕜 complete regular
    (BondalThomsen.integralCurveNumericalClass curve)
  change 0 ≤ evaluation values
  by_contra not_nonnegative
  have negative : evaluation values < 0 := lt_of_not_ge not_nonnegative
  obtain ⟨ampleDivisor, strict⟩ :=
    fan.exists_strictSupportDivisor_of_projective 𝕜 complete regular projective
  let ampleValues : fan.RealRayCoefficients := fun ray => (ampleDivisor ray : ℝ)
  obtain ⟨epsilon, epsilon_positive, epsilon_bound⟩ :=
    exists_pos_mul_lt (neg_pos.mpr negative) (evaluation ampleValues)
  let perturbed := values + epsilon • ampleValues
  have perturbed_negative : evaluation perturbed < 0 := by
    dsimp [perturbed]
    rw [map_add, map_smul, smul_eq_mul]
    linarith [mul_comm epsilon (evaluation ampleValues)]
  have perturbed_positive : ∀ index : fan.PrimitiveRelationIndex,
      0 < index.2.2.realRayPairing perturbed := by
    rintro ⟨left, right, relation⟩
    have positive : 0 < relation.realRayPairing ampleValues := by
      change 0 < relation.realRayPairing (fun ray => (ampleDivisor ray : ℝ))
      rw [relation.realRayPairing_integral]
      exact_mod_cast relation.primitiveSupportIntersection_positive_of_strictSupport
        complete regular ampleDivisor strict
    have nonnegative := pairings left right relation
    dsimp [perturbed]
    rw [map_add, map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos nonnegative (mul_pos epsilon_positive positive)
  let feasible : Set fan.RealRayCoefficients :=
    ⋂ index : fan.PrimitiveRelationIndex, {candidate | 0 < index.2.2.realRayPairing candidate}
  have feasible_open : IsOpen feasible := by
    apply isOpen_iInter_of_finite
    intro index
    exact (LinearMap.continuous_of_finiteDimensional index.2.2.realRayPairing).isOpen_preimage
      (Set.Ioi 0) isOpen_Ioi
  let negativeSet : Set fan.RealRayCoefficients := {candidate | evaluation candidate < 0}
  have negative_open : IsOpen negativeSet :=
    (fan.realRayNumericalEvaluation_continuous 𝕜 complete regular
      (BondalThomsen.integralCurveNumericalClass curve)).isOpen_preimage (Set.Iio 0) isOpen_Iio
  have rational_dense : DenseRange (fun rational : fan.Ray → ℚ =>
      fun ray => (rational ray : ℝ)) :=
    DenseRange.piMap fun _ => Rat.isDenseEmbedding_coe_real.dense
  obtain ⟨rational, feasible_rational, negative_rational⟩ := rational_dense.exists_mem_open
    (feasible_open.inter negative_open) ⟨perturbed, Set.mem_iInter.mpr perturbed_positive,
      perturbed_negative⟩
  have rationalPairings : fan.HasNonnegativeRealPrimitivePairings
      (fun ray => (rational ray : ℝ)) := by
    intro left right relation
    exact (Set.mem_iInter.mp feasible_rational ⟨left, right, relation⟩).le
  have nonnegative := fan.rationalRayCoefficients_nonnegative_on_integralCurve_of_primitivePairings 𝕜
    complete regular projective rational rationalPairings curve
  exact (not_lt_of_ge nonnegative) negative_rational

end TauCeti.Toric.Fan
