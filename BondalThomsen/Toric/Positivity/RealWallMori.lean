module

public import BondalThomsen.Toric.Positivity.WallNumericalDegrees
public import BondalThomsen.Toric.Positivity.RealPrimitivePairings
public import BondalThomsen.Toric.Positivity.WallConcavityGlobalization
public import BondalThomsen.Toric.Positivity.PrimitiveMoriInclusion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Set BondalThomsen
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance realWallRayFintype (fan : Fan embedding) : Fintype fan.Ray :=
  Fintype.ofFinite fan.Ray

variable {𝕜} in
local instance realWallBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

omit [FiniteDimensional ℝ Ambient] in
theorem realConeDivisorCharacter_eq_sum (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (values : fan.RealRayCoefficients) (vector : Lattice) :
    fan.realConeDivisorCharacter basis coneBasis values vector =
      ∑ index, (basis.repr vector index : ℝ) *
        -values (fan.basisRay basis coneBasis index) := by
  conv_lhs => rw [← basis.sum_repr vector]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, realConeDivisorCharacter_basis]

omit [FiniteDimensional ℝ Ambient] in
theorem realConeDivisorCharacter_integral (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (divisor : fan.InvariantRayDivisor) (vector : Lattice) :
    fan.realConeDivisorCharacter basis coneBasis (fun ray => (divisor ray : ℝ)) vector =
      (fan.coneDivisorCharacter basis coneBasis divisor vector : ℝ) := by
  rw [fan.realConeDivisorCharacter_eq_sum]
  conv_rhs => rw [← basis.sum_repr vector]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, coneDivisorCharacter_basis,
    Int.cast_sum, Int.cast_mul, Int.cast_neg]
  norm_cast

def realConeCharacterEvaluation (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (vector : Lattice) : fan.RealRayCoefficients →ₗ[ℝ] ℝ where
  toFun values := fan.realConeDivisorCharacter basis coneBasis values vector
  map_add' first second := by
    simp only [fan.realConeDivisorCharacter_eq_sum, Pi.add_apply, neg_add,
      mul_add, Finset.sum_add_distrib]
  map_smul' scalar values := by
    simp only [fan.realConeDivisorCharacter_eq_sum, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring

def realAdjacentCartierGap (fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension) : fan.RealRayCoefficients →ₗ[ℝ] ℝ :=
  fan.realConeCharacterEvaluation adjacent adjacentCone (basis removed) +
    LinearMap.proj (fan.basisRay basis coneBasis removed)

omit [FiniteDimensional ℝ Ambient] in
@[simp] theorem realAdjacentCartierGap_apply (fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension) (values : fan.RealRayCoefficients) :
    fan.realAdjacentCartierGap basis adjacent coneBasis adjacentCone removed values =
      fan.realConeDivisorCharacter adjacent adjacentCone values (basis removed) +
        values (fan.basisRay basis coneBasis removed) := rfl

omit [FiniteDimensional ℝ Ambient] in
@[simp] theorem realAdjacentCartierGap_integral (fan : Fan embedding) {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension) (divisor : fan.InvariantRayDivisor) :
    fan.realAdjacentCartierGap basis adjacent coneBasis adjacentCone removed
        (fun ray => (divisor ray : ℝ)) =
      (fan.coneDivisorCharacter adjacent adjacentCone divisor (basis removed) +
        divisor (fan.basisRay basis coneBasis removed) : ℤ) := by
  rw [fan.realAdjacentCartierGap_apply, fan.realConeDivisorCharacter_integral, Int.cast_add]

theorem prescribedWallRealNumericalEvaluation_eq_adjacentCartierGap
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (wall : fan.cones)
    (wallEquality : wall.val = adjacentBasisWallCone (embedding := embedding) basis removed)
    (codimensionOne : Module.finrank ℝ (Submodule.span ℝ (wall.val : Set Ambient)) + 1 =
      Module.finrank ℤ Lattice) :
    fan.realRayNumericalEvaluation 𝕜 complete regular
        (BondalThomsen.integralCurveNumericalClass
          (fan.prescribedWallIntegralCurve 𝕜 complete regular wall codimensionOne)) =
      fan.realAdjacentCartierGap basis adjacent coneBasis adjacentCone removed := by
  classical
  apply (Pi.basisFun ℝ fan.Ray).ext
  intro ray
  rw [Pi.basisFun_apply]
  have castSingle : (fun selected : fan.Ray =>
      ((Finsupp.single ray (1 : ℤ) : fan.InvariantRayDivisor) selected : ℝ)) =
      Pi.single ray 1 := by
    funext selected
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [← castSingle, fan.realAdjacentCartierGap_integral]
  change fan.numericalRealPicardFunctional 𝕜 complete regular _ _ = _
  rw [fan.numericalRealPicardFunctional_integralCurve_integerDivisor 𝕜,
    fan.invariantDivisorPicardRealization_apply 𝕜,
    fan.prescribedWallIntegralCurvePicardDegree_eq_adjacentCartierGap 𝕜 complete regular
      basis adjacent coneBasis adjacentCone removed shared opposite wall wallEquality codimensionOne]

theorem adjacentCartierGap_nonnegative_of_actualCurveEvaluations
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (values : fan.RealRayCoefficients)
    (nonnegative : ∀ curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular),
      0 ≤ fan.realRayNumericalEvaluation 𝕜 complete regular
        (BondalThomsen.integralCurveNumericalClass curve) values)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1) :
    0 ≤ fan.realAdjacentCartierGap basis adjacent coneBasis adjacentCone removed values := by
  classical
  let wall : fan.cones := ⟨adjacentBasisWallCone (embedding := embedding) basis removed,
    fan.prescribedBasisCone_mem basis coneBasis (Finset.univ.erase removed)⟩
  have codimensionOne : Module.finrank ℝ (Submodule.span ℝ (wall.val : Set Ambient)) + 1 =
      Module.finrank ℤ Lattice := by
    change Module.finrank ℝ (Submodule.span ℝ
      (prescribedBasisCone (embedding := embedding) basis (Finset.univ.erase removed) : Set Ambient)) +
        1 = Module.finrank ℤ Lattice
    rw [fan.prescribedBasisCone_span_finrank basis (Finset.univ.erase removed),
      Module.finrank_eq_card_basis basis, Fintype.card_fin,
      Finset.card_erase_of_mem (Finset.mem_univ removed), Finset.card_univ, Fintype.card_fin]
    have dimensionPositive : 0 < dimension := Nat.zero_lt_of_lt removed.isLt
    omega
  have degree := nonnegative (fan.prescribedWallIntegralCurve 𝕜 complete regular wall codimensionOne)
  rw [fan.prescribedWallRealNumericalEvaluation_eq_adjacentCartierGap 𝕜 complete regular
    basis adjacent coneBasis adjacentCone removed shared opposite wall rfl codimensionOne] at degree
  exact degree

def numericalWallConeBases (fan : Fan embedding) :=
  {basis : Basis (Fin (Module.finrank ℤ Lattice)) ℤ Lattice // fan.IsConeBasis basis}

instance numericalWallConeBases_finite (fan : Fan embedding) : Finite fan.numericalWallConeBases := by
  let encoding : fan.numericalWallConeBases → (Fin (Module.finrank ℤ Lattice) → fan.Ray) :=
    fun datum index => fan.basisRay datum.val datum.property index
  apply Finite.of_injective encoding
  intro first second same
  apply Subtype.ext
  apply Basis.eq_of_apply_eq
  intro index
  exact congrArg Subtype.val (congrFun same index)

def numericalWallIndex (fan : Fan embedding) :=
  {datum : fan.numericalWallConeBases × fan.numericalWallConeBases ×
      Fin (Module.finrank ℤ Lattice) //
    (∀ index, index ≠ datum.2.2 → datum.2.1.val index = datum.1.val index) ∧
      datum.1.val.repr (datum.2.1.val datum.2.2) datum.2.2 = -1}

instance numericalWallIndex_finite (fan : Fan embedding) : Finite fan.numericalWallIndex :=
  inferInstanceAs (Finite {datum : fan.numericalWallConeBases × fan.numericalWallConeBases ×
    Fin (Module.finrank ℤ Lattice) //
      (∀ index, index ≠ datum.2.2 → datum.2.1.val index = datum.1.val index) ∧
        datum.1.val.repr (datum.2.1.val datum.2.2) datum.2.2 = -1})

def numericalWallEvaluation (fan : Fan embedding) (wall : fan.numericalWallIndex) :
    fan.RealRayCoefficients →ₗ[ℝ] ℝ :=
  fan.realAdjacentCartierGap wall.val.1.val wall.val.2.1.val
    wall.val.1.property wall.val.2.1.property wall.val.2.2

omit [FiniteDimensional ℝ Ambient] in
theorem realAdjacentCartierGap_nonnegative_of_numericalWalls (fan : Fan embedding)
    (values : fan.RealRayCoefficients)
    (nonnegative : ∀ wall : fan.numericalWallIndex, 0 ≤ fan.numericalWallEvaluation wall values)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1) :
    0 ≤ fan.realAdjacentCartierGap basis adjacent coneBasis adjacentCone removed values := by
  have dimensionEquality : dimension = Module.finrank ℤ Lattice := by
    simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis basis).symm
  subst dimension
  exact nonnegative ⟨(⟨basis, coneBasis⟩, ⟨adjacent, adjacentCone⟩, removed), shared, opposite⟩

omit [FiniteDimensional ℝ Ambient] in
theorem numericalWallEvaluation_positive_of_strictSupport (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) (strict : fan.HasStrictRaySupportInequalities divisor)
    (wall : fan.numericalWallIndex) :
    0 < fan.numericalWallEvaluation wall (fun ray => (divisor ray : ℝ)) := by
  classical
  let basis := wall.val.1.val
  let adjacent := wall.val.2.1.val
  let removed := wall.val.2.2
  have outside : (fan.basisRay basis wall.val.1.property removed).val ∉ Set.range adjacent := by
    rintro ⟨index, same⟩
    change adjacent index = basis removed at same
    by_cases equal : index = removed
    · subst index
      have opposite := wall.property.2
      change basis.repr (adjacent removed) removed = -1 at opposite
      rw [same] at opposite
      simp only [Basis.repr_self_apply, ite_true] at opposite
      omega
    · have shared := wall.property.1 index equal
      change adjacent index = basis index at shared
      exact equal (basis.injective (shared.symm.trans same))
  have positive := strict _ adjacent wall.val.2.1.property
    (fan.basisRay basis wall.val.1.property removed) outside
  change -divisor (fan.basisRay basis wall.val.1.property removed) <
    fan.coneDivisorCharacter adjacent wall.val.2.1.property divisor (basis removed) at positive
  change 0 < fan.realAdjacentCartierGap basis adjacent wall.val.1.property
    wall.val.2.1.property removed (fun ray => (divisor ray : ℝ))
  rw [fan.realAdjacentCartierGap_integral]
  exact_mod_cast (show 0 < fan.coneDivisorCharacter adjacent wall.val.2.1.property divisor
    (basis removed) + divisor (fan.basisRay basis wall.val.1.property removed) by omega)

def realRaySupportEvaluation (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (ray : fan.Ray) : fan.RealRayCoefficients →ₗ[ℝ] ℝ :=
  LinearMap.proj ray + fan.realConeCharacterEvaluation basis coneBasis ray.val

omit [FiniteDimensional ℝ Ambient] in
@[simp] theorem realRaySupportEvaluation_apply (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (ray : fan.Ray) (values : fan.RealRayCoefficients) :
    fan.realRaySupportEvaluation basis coneBasis ray values =
      fan.realRaySupportGap basis coneBasis values ray := rfl

omit [FiniteDimensional ℝ Ambient] in
theorem realRaySupportEvaluation_integral (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (ray : fan.Ray) (divisor : fan.InvariantRayDivisor) :
    fan.realRaySupportEvaluation basis coneBasis ray (fun selected => (divisor selected : ℝ)) =
      (divisor ray + fan.coneDivisorCharacter basis coneBasis divisor ray.val : ℤ) := by
  change (divisor ray : ℝ) + fan.realConeDivisorCharacter basis coneBasis
    (fun selected => (divisor selected : ℝ)) ray.val = _
  rw [fan.realConeDivisorCharacter_integral, Int.cast_add]

theorem rationalRaySupport_of_numericalWall_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (coefficients : fan.Ray → ℚ)
    (nonnegative : ∀ wall : fan.numericalWallIndex,
      0 ≤ fan.numericalWallEvaluation wall (fun ray => (coefficients ray : ℝ))) :
    fan.HasRealRaySupportInequalities (fun ray => (coefficients ray : ℝ)) := by
  obtain ⟨scalar, positive, divisor, equality⟩ :=
    fan.exists_positive_real_integer_multiple_rayCoefficients coefficients
  have integralWalls : fan.HasAdjacentWallCartierInequalities divisor := by
    intro dimension basis adjacent coneBasis adjacentCone removed shared opposite
    have bound := fan.realAdjacentCartierGap_nonnegative_of_numericalWalls
      (fun ray => (coefficients ray : ℝ)) nonnegative
      basis adjacent coneBasis adjacentCone removed shared opposite
    have scaled := mul_nonneg positive.le bound
    have scaledEquality : fan.realAdjacentCartierGap basis adjacent coneBasis adjacentCone removed
        (fun ray => (divisor ray : ℝ)) =
      scalar * fan.realAdjacentCartierGap basis adjacent coneBasis adjacentCone removed
        (fun ray => (coefficients ray : ℝ)) := by
      rw [equality, map_smul, smul_eq_mul]
    rw [← scaledEquality, fan.realAdjacentCartierGap_integral] at scaled
    exact_mod_cast scaled
  have integralSupport := fan.hasRaySupportInequalities_of_adjacentWallCartierInequalities
    complete regular divisor integralWalls
  intro dimension basis coneBasis ray
  have bound := integralSupport dimension basis coneBasis ray
  have integralNonnegative :
      0 ≤ (divisor ray + fan.coneDivisorCharacter basis coneBasis divisor ray.val : ℝ) := by
    exact_mod_cast (show 0 ≤ divisor ray +
      fan.coneDivisorCharacter basis coneBasis divisor ray.val by omega)
  have scaled : 0 ≤ scalar * fan.realRaySupportEvaluation basis coneBasis ray
      (fun selected => (coefficients selected : ℝ)) := by
    rw [← smul_eq_mul, ← map_smul, ← equality, fan.realRaySupportEvaluation_integral]
    simpa only [Int.cast_add] using integralNonnegative
  exact (mul_nonneg_iff_of_pos_left positive).mp scaled

theorem hasRealRaySupportInequalities_of_numericalWall_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (values : fan.RealRayCoefficients)
    (nonnegative : ∀ wall : fan.numericalWallIndex, 0 ≤ fan.numericalWallEvaluation wall values) :
    fan.HasRealRaySupportInequalities values := by
  classical
  intro dimension basis coneBasis ray
  let evaluation := fan.realRaySupportEvaluation basis coneBasis ray
  change 0 ≤ evaluation values
  by_contra notNonnegative
  have negative : evaluation values < 0 := lt_of_not_ge notNonnegative
  obtain ⟨ampleDivisor, strict⟩ :=
    fan.exists_strictSupportDivisor_of_projective 𝕜 complete regular projective
  let ampleValues : fan.RealRayCoefficients := fun selected => (ampleDivisor selected : ℝ)
  obtain ⟨epsilon, epsilonPositive, epsilonBound⟩ :=
    exists_pos_mul_lt (neg_pos.mpr negative) (evaluation ampleValues)
  let perturbed := values + epsilon • ampleValues
  have perturbedNegative : evaluation perturbed < 0 := by
    dsimp only [perturbed]
    rw [map_add, map_smul, smul_eq_mul]
    linarith [mul_comm epsilon (evaluation ampleValues)]
  have perturbedPositive : ∀ wall : fan.numericalWallIndex,
      0 < fan.numericalWallEvaluation wall perturbed := by
    intro wall
    have positive := fan.numericalWallEvaluation_positive_of_strictSupport ampleDivisor strict wall
    change 0 < fan.numericalWallEvaluation wall ampleValues at positive
    dsimp only [perturbed]
    rw [map_add, map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos (nonnegative wall) (mul_pos epsilonPositive positive)
  let feasible : Set fan.RealRayCoefficients :=
    ⋂ wall : fan.numericalWallIndex, {candidate | 0 < fan.numericalWallEvaluation wall candidate}
  have feasibleOpen : IsOpen feasible := by
    apply isOpen_iInter_of_finite
    intro wall
    exact (LinearMap.continuous_of_finiteDimensional (fan.numericalWallEvaluation wall)).isOpen_preimage
      (Set.Ioi 0) isOpen_Ioi
  let negativeSet : Set fan.RealRayCoefficients := {candidate | evaluation candidate < 0}
  have negativeOpen : IsOpen negativeSet :=
    (LinearMap.continuous_of_finiteDimensional evaluation).isOpen_preimage (Set.Iio 0) isOpen_Iio
  have rationalDense : DenseRange (fun rational : fan.Ray → ℚ =>
      fun selected => (rational selected : ℝ)) :=
    DenseRange.piMap fun _ => Rat.isDenseEmbedding_coe_real.dense
  obtain ⟨rational, feasibleRational, negativeRational⟩ := rationalDense.exists_mem_open
    (feasibleOpen.inter negativeOpen)
    ⟨perturbed, Set.mem_iInter.mpr perturbedPositive, perturbedNegative⟩
  have rationalNonnegative : ∀ wall : fan.numericalWallIndex,
      0 ≤ fan.numericalWallEvaluation wall (fun selected => (rational selected : ℝ)) := by
    intro wall
    exact (Set.mem_iInter.mp feasibleRational wall).le
  have support := fan.rationalRaySupport_of_numericalWall_nonnegative complete regular
    rational rationalNonnegative dimension basis coneBasis ray
  exact (not_lt_of_ge support) negativeRational

theorem hasRealRaySupportInequalities_of_actualCurveEvaluations
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (values : fan.RealRayCoefficients)
    (nonnegative : ∀ curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular),
      0 ≤ fan.realRayNumericalEvaluation 𝕜 complete regular
        (BondalThomsen.integralCurveNumericalClass curve) values) :
    fan.HasRealRaySupportInequalities values := by
  apply fan.hasRealRaySupportInequalities_of_numericalWall_nonnegative 𝕜 complete regular projective values
  intro wall
  exact fan.adjacentCartierGap_nonnegative_of_actualCurveEvaluations 𝕜 complete regular values nonnegative
    wall.val.1.val wall.val.2.1.val wall.val.1.property wall.val.2.1.property wall.val.2.2
    wall.property.1 wall.property.2

theorem hasNonnegativeRealPrimitivePairings_of_actualCurveEvaluations
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (values : fan.RealRayCoefficients)
    (nonnegative : ∀ curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular),
      0 ≤ fan.realRayNumericalEvaluation 𝕜 complete regular
        (BondalThomsen.integralCurveNumericalClass curve) values) :
    fan.HasNonnegativeRealPrimitivePairings values :=
  fan.hasNonnegativeRealPrimitivePairings_of_raySupport complete regular values
    (fan.hasRealRaySupportInequalities_of_actualCurveEvaluations 𝕜
      complete regular projective values nonnegative)

theorem PrimitiveLatticeRelation.numericalClass_mem_moriCone
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    relation.numericalClass 𝕜 complete regular projective ∈
      BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) := by
  apply (fan.numericalMoriCone_bipolar 𝕜 complete regular _).mpr
  intro values nonnegative
  have pairings := fan.hasNonnegativeRealPrimitivePairings_of_actualCurveEvaluations 𝕜
    complete regular projective values (fun curve => nonnegative
      (BondalThomsen.integralCurveNumericalClass curve)
      (BondalThomsen.integralCurveNumericalClass_mem_moriCone curve))
  change 0 ≤ fan.realRayNumericalEvaluation 𝕜 complete regular
    (relation.numericalClass 𝕜 complete regular projective) values
  rw [relation.realRayNumericalEvaluation_eq 𝕜 complete regular projective]
  exact pairings left right relation

theorem primitiveNumericalCone_le_moriCone
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    fan.primitiveNumericalCone 𝕜 complete regular projective ≤
      BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) :=
  fan.primitiveNumericalCone_le_moriCone_of_primitiveClasses 𝕜 complete regular projective
    (fun _ _ relation => relation.numericalClass_mem_moriCone 𝕜 complete regular projective)

end TauCeti.Toric.Fan
