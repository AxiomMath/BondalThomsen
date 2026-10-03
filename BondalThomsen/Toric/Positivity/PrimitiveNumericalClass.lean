module

public import BondalThomsen.Toric.Positivity.NumericalConeDuality
public import BondalThomsen.Toric.Positivity.PrimitivePairingSupportCriterion
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

noncomputable section

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable {𝕜} in
local instance primitiveNumericalBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

local instance primitiveNumericalRayFintype (fan : Fan embedding) : Fintype fan.Ray :=
  Fintype.ofFinite fan.Ray

local instance primitiveNumericalRayDecidableEq (fan : Fan embedding) : DecidableEq fan.Ray :=
  Classical.decEq fan.Ray

def rationalPicardRayFunctional (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (pairing : Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular)) →+ ℤ) :
    (fan.Ray → ℚ) →ₗ[ℚ] ℚ where
  toFun coefficients := ∑ ray, coefficients ray *
    (pairing (fan.numericalRayPicardClass 𝕜 complete regular ray) : ℚ)
  map_add' first second := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem rationalPicardRayFunctional_integerDivisor (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (pairing : Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular)) →+ ℤ)
    (divisor : fan.InvariantRayDivisor) :
    fan.rationalPicardRayFunctional 𝕜 complete regular pairing (fun ray => (divisor ray : ℚ)) =
      (pairing (fan.invariantDivisorPicardRealization 𝕜 complete regular
        (fan.invariantRayDivisorClass divisor)) : ℚ) := by
  classical
  let coefficientPairing := pairing.comp
    ((fan.invariantDivisorPicardRealization 𝕜 complete regular).comp fan.invariantRayDivisorClass)
  have integerEquality :
      coefficientPairing divisor =
        ∑ ray, divisor ray * coefficientPairing (Finsupp.single ray 1) := by
    conv_lhs => rw [← Finsupp.univ_sum_single divisor]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ray _
    have singleEquality :
        Finsupp.single ray (divisor ray) = divisor ray • Finsupp.single ray (1 : ℤ) := by
      simp
    rw [singleEquality, map_zsmul, zsmul_eq_mul, Int.cast_id]
  have rationalEquality := congrArg (fun integer : ℤ => (integer : ℚ)) integerEquality
  simpa only [rationalPicardRayFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Int.cast_sum, Int.cast_mul, coefficientPairing, AddMonoidHom.comp_apply,
    numericalRayPicardClass, invariantDivisorPicardEquiv_apply] using rationalEquality.symm

omit [FiniteDimensional ℝ Ambient] in
theorem exists_integer_multiple_rayCoefficients (fan : Fan embedding)
    (coefficients : fan.Ray → ℚ) :
    ∃ scalar : ℚ, scalar ≠ 0 ∧ ∃ divisor : fan.InvariantRayDivisor,
      scalar • coefficients = fun ray => (divisor ray : ℚ) := by
  classical
  obtain ⟨denominator, integers⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) coefficients
  choose numerator equality using integers
  refine ⟨(denominator.val : ℚ), ?_, Finsupp.equivFunOnFinite.symm numerator, ?_⟩
  · exact_mod_cast (mem_nonZeroDivisors_iff_ne_zero.mp denominator.property)
  · funext ray
    simpa only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def,
      Finsupp.equivFunOnFinite_symm_apply_apply, algebraMap_int_eq,
      Int.coe_castRingHom] using (equality ray).symm

theorem PrimitiveLatticeRelation.schemePicardPairing_eq_zero_of_curveDegrees_eq_zero
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (bundleClass : Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular)))
    (zeroDegrees : ∀ curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular),
      BondalThomsen.integralCurvePicardDegree curve bundleClass = 0) :
    relation.schemePicardPairing 𝕜 complete regular bundleClass = 0 := by
  let divisorClass := (fan.invariantDivisorPicardEquiv 𝕜 complete regular).symm bundleClass
  have realization : fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass =
      bundleClass := (fan.invariantDivisorPicardEquiv 𝕜 complete regular).apply_symm_apply bundleClass
  have nef : BondalThomsen.SchemeLineBundleClassIsNef (baseField := 𝕜) bundleClass.toMul := by
    apply (BondalThomsen.schemeLineBundleClassIsNef_iff_curveDegree_nonnegative _).mpr
    intro curve
    change 0 ≤ (BondalThomsen.integralCurvePicardDegree curve bundleClass : ℝ)
    rw [zeroDegrees curve]
    simp only [Int.cast_zero, le_refl]
  have inverseNef : BondalThomsen.SchemeLineBundleClassIsNef (baseField := 𝕜)
      (fan.invariantDivisorPicardRealization 𝕜 complete regular (-divisorClass)).toMul := by
    apply (BondalThomsen.schemeLineBundleClassIsNef_iff_curveDegree_nonnegative _).mpr
    intro curve
    change 0 ≤ (BondalThomsen.integralCurvePicardDegree curve
      (fan.invariantDivisorPicardRealization 𝕜 complete regular (-divisorClass)) : ℝ)
    have inverseDegree := map_neg ((BondalThomsen.integralCurvePicardDegree curve).comp
      (fan.invariantDivisorPicardRealization 𝕜 complete regular)) divisorClass
    change BondalThomsen.integralCurvePicardDegree curve
      (fan.invariantDivisorPicardRealization 𝕜 complete regular (-divisorClass)) =
        -BondalThomsen.integralCurvePicardDegree curve
          (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass) at inverseDegree
    rw [inverseDegree, realization, zeroDegrees curve]
    simp only [neg_zero, Int.cast_zero, le_refl]
  have positive := ((fan.invariantClass_isNef_iff_allPrimitivePairings 𝕜
    complete regular projective divisorClass).mp (realization.symm ▸ nef)) left right relation
  have negative := ((fan.invariantClass_isNef_iff_allPrimitivePairings 𝕜
    complete regular projective (-divisorClass)).mp inverseNef) left right relation
  rw [map_neg] at negative
  rw [← realization, relation.schemePicardPairing_realization 𝕜]
  omega

theorem PrimitiveLatticeRelation.rationalPicardRayFunctional_mem_curveSpan
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    fan.rationalPicardRayFunctional 𝕜 complete regular
        (relation.schemePicardPairing 𝕜 complete regular) ∈
      Submodule.span ℚ (Set.range (fun curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular) =>
        fan.rationalPicardRayFunctional 𝕜 complete regular
          (BondalThomsen.integralCurvePicardDegree curve))) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro coefficients annihilated
  have curveZero := (Submodule.mem_iInf _).mp annihilated
  obtain ⟨scalar, nonzero, divisor, scaled⟩ :=
    fan.exists_integer_multiple_rayCoefficients coefficients
  have degreeZero : ∀ curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular),
      BondalThomsen.integralCurvePicardDegree curve
        (fan.invariantDivisorPicardRealization 𝕜 complete regular
          (fan.invariantRayDivisorClass divisor)) = 0 := by
    intro curve
    have evaluated := congrArg
      (fan.rationalPicardRayFunctional 𝕜 complete regular (BondalThomsen.integralCurvePicardDegree curve))
      scaled
    rw [map_smul, LinearMap.mem_ker.mp (curveZero curve), smul_zero,
      fan.rationalPicardRayFunctional_integerDivisor 𝕜] at evaluated
    exact_mod_cast evaluated.symm
  have pairingZero := relation.schemePicardPairing_eq_zero_of_curveDegrees_eq_zero 𝕜
    complete regular projective _ degreeZero
  have evaluated := congrArg
    (fan.rationalPicardRayFunctional 𝕜 complete regular (relation.schemePicardPairing 𝕜 complete regular))
    scaled
  rw [map_smul, fan.rationalPicardRayFunctional_integerDivisor 𝕜, pairingZero, Int.cast_zero]
    at evaluated
  exact (mul_eq_zero.mp evaluated).resolve_left nonzero

theorem rationalPicardRayFunctional_single (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (pairing : Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular)) →+ ℤ)
    (ray : fan.Ray) :
    fan.rationalPicardRayFunctional 𝕜 complete regular pairing (Pi.single ray 1) =
      (pairing (fan.numericalRayPicardClass 𝕜 complete regular ray) : ℚ) := by
  classical
  simp [rationalPicardRayFunctional, Pi.single_apply]

theorem rationalCurveSpan_exists_numericalClass (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (functional : (fan.Ray → ℚ) →ₗ[ℚ] ℚ)
    (membership : functional ∈ Submodule.span ℚ
      (Set.range (fun curve : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular) =>
        fan.rationalPicardRayFunctional 𝕜 complete regular
          (BondalThomsen.integralCurvePicardDegree curve)))) :
    ∃ numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular),
      ∀ ray, numericalClass.val (fan.numericalRayPicardClass 𝕜 complete regular ray) =
        (functional (Pi.single ray 1) : ℝ) := by
  induction membership using Submodule.span_induction with
  | mem functional inGenerators =>
      obtain ⟨curve, rfl⟩ := inGenerators
      refine ⟨BondalThomsen.integralCurveNumericalClass curve, ?_⟩
      intro ray
      rw [fan.rationalPicardRayFunctional_single 𝕜, Rat.cast_intCast]
      rfl
  | zero =>
      refine ⟨0, ?_⟩
      intro ray
      simp only [Submodule.coe_zero, Pi.zero_apply, LinearMap.zero_apply, Rat.cast_zero]
  | add first second firstMembership secondMembership firstLift secondLift =>
      obtain ⟨firstClass, firstEquality⟩ := firstLift
      obtain ⟨secondClass, secondEquality⟩ := secondLift
      refine ⟨firstClass + secondClass, ?_⟩
      intro ray
      change firstClass.val (fan.numericalRayPicardClass 𝕜 complete regular ray) +
        secondClass.val (fan.numericalRayPicardClass 𝕜 complete regular ray) = _
      rw [LinearMap.add_apply, Rat.cast_add, firstEquality, secondEquality]
  | smul scalar functional functionalMembership lift =>
      obtain ⟨numericalClass, equality⟩ := lift
      refine ⟨(scalar : ℝ) • numericalClass, ?_⟩
      intro ray
      change (scalar : ℝ) * numericalClass.val
        (fan.numericalRayPicardClass 𝕜 complete regular ray) = _
      rw [LinearMap.smul_apply, smul_eq_mul, Rat.cast_mul, equality]

theorem PrimitiveLatticeRelation.exists_numericalClass
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    ∃ numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular),
      numericalClass.val = relation.numericalFunctional 𝕜 complete regular := by
  obtain ⟨numericalClass, rayEquality⟩ := fan.rationalCurveSpan_exists_numericalClass 𝕜
    complete regular _
      (relation.rationalPicardRayFunctional_mem_curveSpan 𝕜 complete regular projective)
  let coefficientPicard :=
    (fan.invariantDivisorPicardEquiv 𝕜 complete regular).toAddMonoidHom.comp
      fan.invariantRayDivisorClass
  let primitivePicardHom := (Int.castAddHom ℝ).comp
    (relation.schemePicardPairing 𝕜 complete regular)
  have coefficientEqual :
      (BondalThomsen.numericalPicardHom numericalClass).comp coefficientPicard =
        primitivePicardHom.comp coefficientPicard := by
    apply Finsupp.addHom_ext'
    intro ray
    apply AddMonoidHom.ext_int
    change numericalClass.val (fan.numericalRayPicardClass 𝕜 complete regular ray) =
      (relation.schemePicardPairing 𝕜 complete regular
        (fan.numericalRayPicardClass 𝕜 complete regular ray) : ℝ)
    simpa only [fan.rationalPicardRayFunctional_single 𝕜, Rat.cast_intCast] using rayEquality ray
  refine ⟨numericalClass, ?_⟩
  funext bundleClass
  obtain ⟨divisor, divisorEquality⟩ :=
    fan.invariantDivisorPicard_coefficients_surjective 𝕜 complete regular bundleClass
  have evaluated := DFunLike.congr_fun coefficientEqual divisor
  change numericalClass.val (coefficientPicard divisor) =
    relation.numericalFunctional 𝕜 complete regular (coefficientPicard divisor) at evaluated
  change coefficientPicard divisor = bundleClass at divisorEquality
  simpa only [divisorEquality] using evaluated

theorem PrimitiveLatticeRelation.numericalFunctional_mem_numericalCurveSpace
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    relation.numericalFunctional 𝕜 complete regular ∈
      BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular) := by
  obtain ⟨numericalClass, equality⟩ := relation.exists_numericalClass 𝕜 complete regular projective
  exact equality ▸ numericalClass.property

def PrimitiveLatticeRelation.numericalClass
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular) :=
  ⟨relation.numericalFunctional 𝕜 complete regular,
    relation.numericalFunctional_mem_numericalCurveSpace 𝕜 complete regular projective⟩

@[simp] theorem PrimitiveLatticeRelation.numericalClass_val
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    (relation.numericalClass 𝕜 complete regular projective).val =
      relation.numericalFunctional 𝕜 complete regular := rfl

@[simp] theorem PrimitiveLatticeRelation.numericalClass_apply
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (bundleClass : Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular))) :
    (relation.numericalClass 𝕜 complete regular projective).val bundleClass =
      (relation.schemePicardPairing 𝕜 complete regular bundleClass : ℝ) := rfl

@[simp] theorem PrimitiveLatticeRelation.numericalClass_realization
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (divisorClass : fan.InvariantRayDivisorClass) :
    (relation.numericalClass 𝕜 complete regular projective).val
        (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass) =
      (relation.classPairing divisorClass : ℝ) :=
  relation.numericalFunctional_realization 𝕜 complete regular divisorClass

theorem PrimitiveLatticeRelation.numericalClass_ne_zero
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    relation.numericalClass 𝕜 complete regular projective ≠ 0 := by
  intro zero
  exact relation.numericalFunctional_ne_zero 𝕜 complete regular
    (congrArg Subtype.val zero)

theorem PrimitiveLatticeRelation.isMoriExtremal_iff_numericalClass
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    relation.IsMoriExtremal 𝕜 complete regular ↔
      BondalThomsen.IsExtremalMoriClass (relation.numericalClass 𝕜 complete regular projective) := by
  constructor
  · rintro ⟨numericalClass, equality, extremal⟩
    have classesEqual : numericalClass = relation.numericalClass 𝕜 complete regular projective :=
      Subtype.ext equality
    exact classesEqual ▸ extremal
  · intro extremal
    exact ⟨relation.numericalClass 𝕜 complete regular projective, rfl, extremal⟩

end

end TauCeti.Toric.Fan
