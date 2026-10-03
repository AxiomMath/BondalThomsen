module

public import BondalThomsen.Toric.Positivity.SupportGeneration
public import BondalThomsen.Fan.AnticanonicalPolytope
public import Mathlib.Data.Pi.Interval
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

open Set Module Multiplicative
open scoped Pointwise

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def divisorCharacterPolyhedron (fan : Fan embedding) (divisor : fan.InvariantRayDivisor) :
    Set (StrongDual ℝ Ambient) :=
  {functional | ∀ ray : fan.Ray, -(divisor ray : ℝ) ≤ functional (embedding ray.val)}

noncomputable def divisorCoefficientBound (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) : ℕ :=
  divisor.support.sup (fun ray => (divisor ray).natAbs) + 1

omit [FiniteDimensional ℝ Ambient] in
theorem divisorCoefficientBound_positive (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) : 0 < fan.divisorCoefficientBound divisor := by
  unfold divisorCoefficientBound
  omega

omit [FiniteDimensional ℝ Ambient] in
theorem divisor_coefficient_le_bound (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray) :
    divisor ray ≤ fan.divisorCoefficientBound divisor := by
  classical
  have absolute_bound : (divisor ray).natAbs ≤ fan.divisorCoefficientBound divisor := by
    by_cases contains : ray ∈ divisor.support
    · unfold divisorCoefficientBound
      exact (Finset.le_sup (f := fun ray => (divisor ray).natAbs) contains).trans (Nat.le_succ _)
    · rw [Finsupp.notMem_support_iff.mp contains]
      exact Nat.zero_le _
  exact (Int.le_natAbs).trans (by exact_mod_cast absolute_bound)

omit [FiniteDimensional ℝ Ambient] in

theorem divisorCharacterPolyhedron_subset_scaled_anticanonical (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) :
    fan.divisorCharacterPolyhedron divisor ⊆
      (fan.divisorCoefficientBound divisor : ℝ) • fan.anticanonicalPolytope := by
  intro functional inequalities
  let bound : ℝ := fan.divisorCoefficientBound divisor
  have positive : 0 < bound := by
    change (0 : ℝ) < (fan.divisorCoefficientBound divisor : ℝ)
    exact_mod_cast fan.divisorCoefficientBound_positive divisor
  refine Set.mem_smul_set.mpr ⟨bound⁻¹ • functional, ?_, ?_⟩
  · intro ray
    change -1 ≤ bound⁻¹ * functional (embedding ray.val)
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ positive).mpr
    have coefficient_bound : (divisor ray : ℝ) ≤ bound := by
      change (divisor ray : ℝ) ≤ (fan.divisorCoefficientBound divisor : ℝ)
      exact_mod_cast fan.divisor_coefficient_le_bound divisor ray
    have lower := inequalities ray
    linarith
  · rw [smul_smul, mul_inv_cancel₀ positive.ne', one_smul]

theorem divisorCharacterPolyhedron_isBounded (fan : Fan embedding)
    (complete : fan.IsComplete) (divisor : fan.InvariantRayDivisor) :
    Bornology.IsBounded (fan.divisorCharacterPolyhedron divisor) :=
  ((fan.anticanonicalPolytope_isBounded complete).smul₀
    (fan.divisorCoefficientBound divisor : ℝ)).subset
      (fan.divisorCharacterPolyhedron_subset_scaled_anticanonical divisor)

omit [FiniteDimensional ℝ Ambient] in

theorem integral_exponents_finite_of_coordinate_bounds (_fan : Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (exponents : Set (Multiplicative (Lattice →+ ℤ)))
    (lower upper : Fin dimension → ℤ)
    (bounds : ∀ exponent ∈ exponents, ∀ coordinate,
      lower coordinate ≤ toAdd exponent (basis coordinate) ∧
        toAdd exponent (basis coordinate) ≤ upper coordinate) : exponents.Finite := by
  classical
  let coordinates : Multiplicative (Lattice →+ ℤ) → Fin dimension → ℤ :=
    fun exponent coordinate => toAdd exponent (basis coordinate)
  have injective : Function.Injective coordinates := by
    intro first second same
    have linear_same : (toAdd first).toIntLinearMap = (toAdd second).toIntLinearMap := by
      apply basis.ext
      intro coordinate
      exact congrFun same coordinate
    apply congrArg ofAdd
    ext vector
    exact DFunLike.congr_fun linear_same vector
  have finite_image : (coordinates '' exponents).Finite := by
    apply (Set.finite_Icc lower upper).subset
    rintro values ⟨exponent, member, rfl⟩
    exact ⟨fun coordinate => (bounds exponent member coordinate).1,
      fun coordinate => (bounds exponent member coordinate).2⟩
  exact finite_image.of_finite_image injective.injOn

theorem integral_exponents_finite_of_bounded_realCharacters (fan : Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (exponents : Set (Multiplicative (Lattice →+ ℤ)))
    (bounded : Bornology.IsBounded
      ((fun exponent => LinearMap.toContinuousLinearMap
        (fan.lattice.realCharacter (toAdd exponent))) '' exponents)) : exponents.Finite := by
  obtain ⟨bound, bound_norm⟩ := bounded.exists_norm_le
  let upper : Fin dimension → ℤ := fun coordinate => ⌈bound * ‖embedding (basis coordinate)‖⌉
  apply fan.integral_exponents_finite_of_coordinate_bounds basis exponents (-upper) upper
  intro exponent member coordinate
  let functional := LinearMap.toContinuousLinearMap (fan.lattice.realCharacter (toAdd exponent))
  have functional_bound : ‖functional‖ ≤ bound := bound_norm functional ⟨exponent, member, rfl⟩
  have evaluation_bound : ‖functional (embedding (basis coordinate))‖ ≤
      bound * ‖embedding (basis coordinate)‖ :=
    (functional.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right functional_bound (norm_nonneg _))
  have integer_bound : |(toAdd exponent (basis coordinate) : ℝ)| ≤ (upper coordinate : ℝ) := by
    change |(toAdd exponent (basis coordinate) : ℝ)| ≤ (⌈bound * ‖embedding (basis coordinate)‖⌉ : ℝ)
    have evaluation : functional (embedding (basis coordinate)) =
        (toAdd exponent (basis coordinate) : ℝ) := fan.lattice.realCharacter_apply _ _
    rw [evaluation, Real.norm_eq_abs] at evaluation_bound
    exact evaluation_bound.trans (Int.le_ceil _)
  have integer_bounds := abs_le.mp integer_bound
  constructor
  · change -upper coordinate ≤ toAdd exponent (basis coordinate)
    exact_mod_cast integer_bounds.1
  · exact_mod_cast integer_bounds.2

theorem globalDivisorSectionExponents_finite (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) : (fan.globalDivisorSectionExponents divisor).Finite := by
  obtain ⟨dimension, basis, _, _⟩ := fan.exists_coneBasis_containing complete regular (0 : Ambient)
  apply fan.integral_exponents_finite_of_bounded_realCharacters basis
    (fan.globalDivisorSectionExponents divisor)
  apply (fan.divisorCharacterPolyhedron_isBounded complete divisor).subset
  rintro functional ⟨exponent, inequalities, rfl⟩ ray
  change -(divisor ray : ℝ) ≤ fan.lattice.realCharacter (toAdd exponent) (embedding ray.val)
  rw [fan.lattice.realCharacter_apply]
  exact_mod_cast inequalities ray

noncomputable def globalDivisorLaurentSectionCoeffEquiv (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) :
    fan.globalDivisorLaurentSectionSpace 𝕜 divisor ≃ₗ[𝕜]
      (fan.globalDivisorSectionExponents divisor →₀ 𝕜) :=
  MonoidAlgebra.supportedEquivFinsupp (fan.globalDivisorSectionExponents divisor)

noncomputable def globalDivisorLaurentSectionBasis (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) :
    Basis (fan.globalDivisorSectionExponents divisor) 𝕜
      (fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :=
  Finsupp.basisSingleOne.map (fan.globalDivisorLaurentSectionCoeffEquiv 𝕜 divisor).symm

omit [FiniteDimensional ℝ Ambient] in

theorem globalDivisorLaurentSectionBasis_val (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) (exponent : fan.globalDivisorSectionExponents divisor) :
    (fan.globalDivisorLaurentSectionBasis 𝕜 divisor exponent : fan.LaurentCharacterAlgebra 𝕜) =
      MonoidAlgebra.single exponent.val 1 := by
  change ((MonoidAlgebra.supportedEquivFinsupp (R := 𝕜) (S := 𝕜)
    (fan.globalDivisorSectionExponents divisor)).symm (Finsupp.single exponent (1 : 𝕜)) :
      fan.LaurentCharacterAlgebra 𝕜) = _
  apply MonoidAlgebra.coeff_injective
  exact Finsupp.supportedEquivFinsupp_symm_single (R := 𝕜) (M := 𝕜)
    (fan.globalDivisorSectionExponents divisor) exponent 1

end TauCeti.Toric.Fan
