module

public import BondalThomsen.Toric.Positivity.PrimitiveMoriInclusion

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

noncomputable section

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in
theorem PrimitiveLatticeRelation.divisorIntersection_single_nonpositive_of_not_mem_left
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (ray : fan.Ray)
    (omitted : ray ∉ left) :
    relation.divisorIntersection (Finsupp.single ray 1) ≤ 0 := by
  classical
  have leftZero : ∀ selected : left,
      (Finsupp.single ray (1 : ℤ) : fan.InvariantRayDivisor) selected.val = 0 := by
    intro selected
    have different : ray ≠ selected.val := by
      intro same
      exact omitted (same.symm ▸ selected.property)
    simp [different]
  unfold PrimitiveLatticeRelation.divisorIntersection
  simp only [leftZero, Finset.sum_const_zero, zero_sub]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro selected _
  apply mul_nonneg (Int.natCast_nonneg _)
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num

theorem PrimitiveLatticeRelation.numericalClass_single_nonpositive_of_not_mem_left
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (ray : fan.Ray) (omitted : ray ∉ left) :
    (relation.numericalClass 𝕜 complete regular projective).val
      (fan.invariantDivisorPicardRealization 𝕜 complete regular
        (fan.invariantRayDivisorClass (Finsupp.single ray 1))) ≤ 0 := by
  rw [relation.numericalClass_realization 𝕜, relation.classPairing_mk]
  exact_mod_cast relation.divisorIntersection_single_nonpositive_of_not_mem_left ray omitted

theorem PrimitiveLatticeRelation.left_subset_of_numericalClass_mem_ray
    {fan : Fan embedding} {left right otherLeft otherRight : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (other : fan.PrimitiveLatticeRelation otherLeft otherRight)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (onRay : other.numericalClass 𝕜 complete regular projective ∈
      PointedCone.hull ℝ {relation.numericalClass 𝕜 complete regular projective}) :
    left ⊆ otherLeft := by
  classical
  obtain ⟨scalar, nonnegative, equality⟩ := PointedCone.mem_hull_singleton.mp onRay
  intro ray member
  by_contra omitted
  have originalOne : (relation.numericalClass 𝕜 complete regular projective).val
      (fan.invariantDivisorPicardRealization 𝕜 complete regular
        (fan.invariantRayDivisorClass (Finsupp.single ray 1))) = 1 := by
    rw [relation.numericalClass_apply 𝕜,
      relation.schemePicardPairing_leftRay 𝕜 complete regular ⟨ray, member⟩]
    norm_num
  have tested := congrArg (fun numericalClass => numericalClass.val
    (fan.invariantDivisorPicardRealization 𝕜 complete regular
      (fan.invariantRayDivisorClass (Finsupp.single ray 1)))) equality
  change scalar * _ = _ at tested
  rw [originalOne, mul_one] at tested
  have nonpositive := other.numericalClass_single_nonpositive_of_not_mem_left 𝕜
    complete regular projective ray omitted
  have scalarZero : scalar = 0 := le_antisymm (tested ▸ nonpositive) nonnegative
  have otherZero : other.numericalClass 𝕜 complete regular projective = 0 := by
    rw [scalarZero, zero_smul] at equality
    exact equality.symm
  exact other.numericalClass_ne_zero 𝕜 complete regular projective otherZero

theorem PrimitiveLatticeRelation.numericalClass_not_mem_ray_of_omitted_leftRay
    {fan : Fan embedding} {left right otherLeft otherRight : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (other : fan.PrimitiveLatticeRelation otherLeft otherRight)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (distinguished : left) (omitted : distinguished.val ∉ otherLeft) :
    other.numericalClass 𝕜 complete regular projective ∉
      PointedCone.hull ℝ {relation.numericalClass 𝕜 complete regular projective} := by
  intro onRay
  exact omitted (relation.left_subset_of_numericalClass_mem_ray 𝕜 other complete regular
    projective onRay distinguished.property)

end

end TauCeti.Toric.Fan
