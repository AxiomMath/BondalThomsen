module

public import BondalThomsen.Toric.RankOne.BondalThomsenClassification
public import BondalThomsen.Toric.Positivity.GlobalGenerationCriterion
public import BondalThomsen.Toric.Positivity.VeryAmpleLineBundle
public import BondalThomsen.Toric.Projective.AllSectionPullbackSheafIso
public import BondalThomsen.Toric.Scheme.DeepProperness

@[expose] public section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module
open TauCeti.Toric
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

def HasGloballyGeneratedPower {scheme : Scheme}
    (lineBundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) : Prop :=
  ∃ exponent : ℕ, 0 < exponent ∧
    ∃ powerBundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme,
      TauCeti.AlgebraicGeometry.LineBundleClass.mk powerBundle =
        TauCeti.AlgebraicGeometry.LineBundleClass.mk lineBundle ^ exponent ∧
      Nonempty powerBundle.obj.GeneratingSections

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem rankOneDivisorCoefficientDegree_eq_sum (fan : Fan embedding) [Fintype fan.Ray]
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (divisor : fan.InvariantRayDivisor) :
    fan.rankOneDivisorCoefficientDegree complete regular basis divisor = ∑ ray : fan.Ray, divisor ray := by
  have all_rays : (Finset.univ : Finset fan.Ray) =
      {fan.rankOnePositiveRay complete regular basis, fan.rankOneNegativeRay complete regular basis} := by
    ext ray
    simpa only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff] using
      fan.rankOne_ray_eq_positive_or_negative complete regular basis ray
  rw [all_rays]
  simp [rankOneDivisorCoefficientDegree,
    fan.rankOnePositiveRay_ne_negativeRay complete regular basis]

theorem rankOneDivisorCoefficientDegree_basis_independent (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : Basis (Fin 1) ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    fan.rankOneDivisorCoefficientDegree complete regular first divisor =
        fan.rankOneDivisorCoefficientDegree complete regular second divisor := by
  let : Fintype fan.Ray := Fintype.ofFinite _
  rw [fan.rankOneDivisorCoefficientDegree_eq_sum, fan.rankOneDivisorCoefficientDegree_eq_sum]

theorem rankOne_hasRaySupportInequalities_iff_coefficientDegree_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin 1) ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    fan.HasRaySupportInequalities divisor ↔
      0 ≤ fan.rankOneDivisorCoefficientDegree complete regular reference divisor := by
  constructor
  · exact fan.rankOne_coefficientDegree_nonnegative_of_raySupportInequalities
      complete regular reference divisor
  · intro nonnegative dimension basis cone_basis ray
    have dimension_one : dimension = 1 := by
      have same_rank := (Module.finrank_eq_card_basis basis).symm.trans
        (Module.finrank_eq_card_basis reference)
      simpa only [Fintype.card_fin] using same_rank
    subst dimension
    have local_degree : 0 ≤ fan.rankOneDivisorCoefficientDegree complete regular basis divisor := by
      rwa [fan.rankOneDivisorCoefficientDegree_basis_independent complete regular basis reference]
    have positive_same : fan.basisRay basis cone_basis 0 =
        fan.rankOnePositiveRay complete regular basis := Subtype.ext rfl
    rcases fan.rankOne_ray_eq_positive_or_negative complete regular basis ray with positive | negative
    · rw [positive, fan.rankOnePositiveRay_val, fan.coneDivisorCharacter_basis, positive_same]
    · rw [negative, fan.rankOneNegativeRay_val, map_neg,
        fan.coneDivisorCharacter_basis, positive_same]
      change 0 ≤ divisor (fan.rankOnePositiveRay complete regular basis) +
        divisor (fan.rankOneNegativeRay complete regular basis) at local_degree
      omega

theorem rankOne_invariantDivisorGloballyGenerated_iff_coefficientDegree_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    fan.InvariantDivisorGloballyGenerated 𝕜 complete regular divisor ↔
      0 ≤ fan.rankOneDivisorCoefficientDegree complete regular basis divisor :=
  (fan.invariantDivisorGloballyGenerated_iff_support 𝕜 complete regular divisor).trans
    (fan.rankOne_hasRaySupportInequalities_iff_coefficientDegree_nonnegative
      complete regular basis divisor)

theorem rankOneDivisorCoefficientDegree_nsmul (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (divisor : fan.InvariantRayDivisor) (multiple : ℕ) :
    fan.rankOneDivisorCoefficientDegree complete regular basis (multiple • divisor) =
      (multiple : ℤ) * fan.rankOneDivisorCoefficientDegree complete regular basis divisor := by
  simp only [rankOneDivisorCoefficientDegree, Finsupp.nsmul_apply, nsmul_eq_mul]
  ring

theorem rankOne_invariantDivisor_hasGloballyGeneratedPower_iff_coefficientDegree_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    BondalThomsen.HasGloballyGeneratedPower (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) ↔
      0 ≤ fan.rankOneDivisorCoefficientDegree complete regular basis divisor := by
  constructor
  · rintro ⟨exponent, positive, powerBundle, same_class, generators⟩
    have actual_class : TauCeti.AlgebraicGeometry.LineBundleClass.mk powerBundle =
        TauCeti.AlgebraicGeometry.LineBundleClass.mk
          (fan.invariantDivisorLineBundle 𝕜 complete regular (exponent • divisor)) :=
      same_class.trans (fan.invariantDivisorLineBundleClass_nsmul 𝕜
        complete regular divisor exponent).symm
    obtain ⟨comparison⟩ := TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mp actual_class
    have actual_generators : fan.InvariantDivisorGloballyGenerated 𝕜 complete regular (exponent • divisor) :=
      (SheafOfModules.GeneratingSections.equivOfIso comparison).nonempty_congr.mp generators
    have product_nonnegative :=
      (fan.rankOne_invariantDivisorGloballyGenerated_iff_coefficientDegree_nonnegative 𝕜
        complete regular basis (exponent • divisor)).mp actual_generators
    rw [fan.rankOneDivisorCoefficientDegree_nsmul] at product_nonnegative
    have exponent_positive : (0 : ℤ) < exponent := by exact_mod_cast positive
    exact nonneg_of_mul_nonneg_right product_nonnegative exponent_positive
  · intro nonnegative
    exact ⟨1, by decide, fan.invariantDivisorLineBundle 𝕜 complete regular divisor, by simp,
      (fan.rankOne_invariantDivisorGloballyGenerated_iff_coefficientDegree_nonnegative 𝕜
        complete regular basis divisor).mpr nonnegative⟩

end TauCeti.Toric.Fan
