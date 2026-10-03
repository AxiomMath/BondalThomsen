module

public import BondalThomsen.Toric.RankOne.NefVanishing
public import BondalThomsen.Toric.Divisor.DivisorExtCohomology
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Toric.Divisor.DivisorTensorEquivalence
public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Derived.InvertibleSheafExtCohomology
public import Mathlib.Data.Set.Card

@[expose] public section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Module
open TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped Classical

namespace TauCeti.Toric.Fan

universe derivedUniverse

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def rankOneDegreeDivisor (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (degree : ℤ) : fan.InvariantRayDivisor :=
  Finsupp.single (fan.rankOnePositiveRay complete regular basis) degree

@[simp] theorem rankOneDegreeDivisor_coefficientDegree (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (degree : ℤ) :
    fan.rankOneDivisorCoefficientDegree complete regular basis
      (fan.rankOneDegreeDivisor complete regular basis degree) = degree := by
  simp [rankOneDegreeDivisor, rankOneDivisorCoefficientDegree,
    (fan.rankOnePositiveRay_ne_negativeRay complete regular basis).symm]

noncomputable def rankOneCoefficientDegreeHom (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    fan.InvariantRayDivisor →+ ℤ where
  toFun := fan.rankOneDivisorCoefficientDegree complete regular basis
  map_zero' := by simp [rankOneDivisorCoefficientDegree]
  map_add' first second := by
    simp only [rankOneDivisorCoefficientDegree, Finsupp.add_apply]
    omega

theorem rankOne_invariantRayDivisorClass_eq_iff_coefficientDegree_eq
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) (first second : fan.InvariantRayDivisor) :
    fan.invariantRayDivisorClass first = fan.invariantRayDivisorClass second ↔
      fan.rankOneDivisorCoefficientDegree complete regular basis first =
        fan.rankOneDivisorCoefficientDegree complete regular basis second := by
  constructor
  · intro same
    obtain ⟨character, equation⟩ := QuotientAddGroup.eq_iff_sub_mem.mp same
    have sum_equation := congrArg
      (fan.rankOneDivisorCoefficientDegree complete regular basis) equation
    simp only [principalRayDivisor_apply, rankOneDivisorCoefficientDegree, Finsupp.sub_apply,
      fan.rankOnePositiveRay_val, fan.rankOneNegativeRay_val, map_neg] at sum_equation ⊢
    omega
  · intro same
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    let character : Lattice →+ ℤ :=
      (first (fan.rankOnePositiveRay complete regular basis) -
        second (fan.rankOnePositiveRay complete regular basis)) •
          (basis.coord 0).toAddMonoidHom
    refine ⟨character, ?_⟩
    ext ray
    change character ray.val = first ray - second ray
    rcases fan.rankOne_ray_eq_positive_or_negative complete regular basis ray with same_ray | same_ray
    · subst ray
      simp [character, fan.rankOnePositiveRay_val, Basis.coord_apply]
    · subst ray
      simp only [rankOneDivisorCoefficientDegree] at same
      simp [character, fan.rankOneNegativeRay_val, Basis.coord_apply]
      omega

noncomputable def rankOneClassDegree (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    fan.InvariantRayDivisorClass →+ ℤ :=
  QuotientAddGroup.lift fan.principalRayDivisor.range
    (fan.rankOneCoefficientDegreeHom complete regular basis) (by
      rintro divisor ⟨character, rfl⟩
      apply AddMonoidHom.mem_ker.mpr
      change fan.rankOneDivisorCoefficientDegree complete regular basis
        (fan.principalRayDivisor character) = 0
      simp [rankOneDivisorCoefficientDegree, fan.rankOnePositiveRay_val,
        fan.rankOneNegativeRay_val])

@[simp] theorem rankOneClassDegree_apply (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (divisor : fan.InvariantRayDivisor) :
    fan.rankOneClassDegree complete regular basis (fan.invariantRayDivisorClass divisor) =
      fan.rankOneDivisorCoefficientDegree complete regular basis divisor := rfl

theorem rankOneClassDegree_bijective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    Function.Bijective (fan.rankOneClassDegree complete regular basis) := by
  constructor
  · intro first second
    induction first using QuotientAddGroup.induction_on with
    | H first =>
      induction second using QuotientAddGroup.induction_on with
      | H second =>
        exact (fan.rankOne_invariantRayDivisorClass_eq_iff_coefficientDegree_eq
          complete regular basis first second).mpr
  · intro degree
    refine ⟨fan.invariantRayDivisorClass (fan.rankOneDegreeDivisor complete regular basis degree), ?_⟩
    simp

noncomputable def rankOneInvariantDivisorClassEquivInt (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    fan.InvariantRayDivisorClass ≃+ ℤ :=
  AddEquiv.ofBijective (fan.rankOneClassDegree complete regular basis)
    (fan.rankOneClassDegree_bijective complete regular basis)

end TauCeti.Toric.Fan
