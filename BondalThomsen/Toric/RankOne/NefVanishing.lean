module

public import BondalThomsen.Toric.Cohomology.NefCechAcyclicity
public import BondalThomsen.Toric.Cohomology.CechWeightDecomposition
public import BondalThomsen.Fan.PrimitiveRelationExistence

@[expose] public section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped Classical

namespace BondalThomsen.ToricRankOneNefVanishing

variable {Lattice : Type*} [AddCommGroup Lattice]

theorem primitive_eq_signed_rankOne_basis (basis : Basis (Fin 1) ℤ Lattice)
    (vector : Lattice) (primitive : TauCeti.IsPrimitive vector) :
    vector = basis 0 ∨ vector = -basis 0 := by
  have reconstruction : basis.repr vector 0 • basis 0 = vector := by
    simpa only [Fin.sum_univ_one] using basis.sum_repr vector
  obtain ⟨projection, primitive_value⟩ := TauCeti.isPrimitive_def.mp primitive
  rw [← reconstruction, map_smul, smul_eq_mul] at primitive_value
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp primitive_value with positive | negative
  · left
    simpa only [positive.1, one_smul] using reconstruction.symm
  · right
    simpa only [negative.1, neg_one_smul] using reconstruction.symm

noncomputable def rankOneNegativeBasis (basis : Basis (Fin 1) ℤ Lattice) : Basis (Fin 1) ℤ Lattice :=
  basis.map (LinearEquiv.neg ℤ)

theorem rankOneNegativeBasis_apply (basis : Basis (Fin 1) ℤ Lattice) (index : Fin 1) :
    rankOneNegativeBasis basis index = -basis index := by
  simp [rankOneNegativeBasis]

end BondalThomsen.ToricRankOneNefVanishing

namespace TauCeti.Toric.Fan

open BondalThomsen.ToricRankOneNefVanishing

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable section

theorem rankOne_isConeBasis (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    fan.IsConeBasis basis := by
  obtain ⟨size, otherBasis, otherCone, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (embedding (basis 0))
  have size_one : size = 1 := by
    have other_rank := Module.finrank_eq_card_basis otherBasis
    have rank_one := Module.finrank_eq_card_basis basis
    simpa only [Fintype.card_fin] using other_rank.symm.trans rank_one
  subst size
  rcases primitive_eq_signed_rankOne_basis basis (otherBasis 0) (otherBasis.isPrimitive 0) with
    positive | negative
  · have same_basis : (fun index => embedding (otherBasis index)) =
        (fun index => embedding (basis index)) := by
      funext index
      have index_zero : index = 0 := Subsingleton.elim _ _
      simpa only [index_zero] using congrArg embedding positive
    unfold IsConeBasis at otherCone ⊢
    rwa [same_basis] at otherCone
  · have basis_eq : basis 0 = -otherBasis 0 := by rw [negative, neg_neg]
    have nonnegative := fan.coneBasis_repr_nonnegative otherBasis (basis 0) contains 0
    rw [basis_eq] at nonnegative
    simp at nonnegative

def rankOnePositiveRay (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    fan.Ray :=
  fan.basisRay basis (fan.rankOne_isConeBasis complete regular basis) 0

def rankOneNegativeRay (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    fan.Ray :=
  fan.basisRay (rankOneNegativeBasis basis)
    (fan.rankOne_isConeBasis complete regular (rankOneNegativeBasis basis)) 0

theorem rankOnePositiveRay_val (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    (fan.rankOnePositiveRay complete regular basis).val = basis 0 := rfl

theorem rankOneNegativeRay_val (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    (fan.rankOneNegativeRay complete regular basis).val = -basis 0 := by
  exact rankOneNegativeBasis_apply basis 0

theorem rankOne_ray_eq_positive_or_negative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (ray : fan.Ray) :
    ray = fan.rankOnePositiveRay complete regular basis ∨
      ray = fan.rankOneNegativeRay complete regular basis := by
  rcases primitive_eq_signed_rankOne_basis basis ray.val ray.property.1 with positive | negative
  · left
    apply Subtype.ext
    exact positive
  · right
    apply Subtype.ext
    exact negative.trans (fan.rankOneNegativeRay_val complete regular basis).symm

theorem rankOnePositiveRay_ne_negativeRay (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice) :
    fan.rankOnePositiveRay complete regular basis ≠ fan.rankOneNegativeRay complete regular basis := by
  intro same
  have vector_same := congrArg Subtype.val same
  rw [fan.rankOnePositiveRay_val, fan.rankOneNegativeRay_val] at vector_same
  have coordinate_same := congrArg (fun vector => basis.repr vector 0) vector_same
  simp at coordinate_same

theorem rankOnePositiveRay_mem_cone_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (ray : fan.Ray) :
    embedding ray.val ∈ PointedCone.hull ℝ
        (Set.range (fun index => embedding (basis index))) ↔
      ray = fan.rankOnePositiveRay complete regular basis := by
  constructor
  · intro contains
    obtain ⟨index, same⟩ := fan.ray_eq_basis_of_mem_coneBasis basis
      (fan.rankOne_isConeBasis complete regular basis) ray contains
    apply Subtype.ext
    have index_zero : index = 0 := Subsingleton.elim _ _
    simpa only [index_zero, fan.rankOnePositiveRay_val] using same.symm
  · rintro rfl
    exact PointedCone.subset_hull ⟨0, rfl⟩

def rankOneDivisorCoefficientDegree (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (divisor : fan.InvariantRayDivisor) : ℤ :=
  divisor (fan.rankOnePositiveRay complete regular basis) +
    divisor (fan.rankOneNegativeRay complete regular basis)

theorem rankOne_coefficientDegree_nonnegative_of_raySupportInequalities (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (basis : Basis (Fin 1) ℤ Lattice)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor) :
    0 ≤ fan.rankOneDivisorCoefficientDegree complete regular basis divisor := by
  have bound := support 1 basis (fan.rankOne_isConeBasis complete regular basis)
    (fan.rankOneNegativeRay complete regular basis)
  rw [fan.rankOneNegativeRay_val, map_neg, fan.coneDivisorCharacter_basis] at bound
  change -divisor (fan.rankOneNegativeRay complete regular basis) ≤
    - -divisor (fan.rankOnePositiveRay complete regular basis) at bound
  unfold rankOneDivisorCoefficientDegree
  omega

end

end TauCeti.Toric.Fan
