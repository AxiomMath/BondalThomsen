module

public import BondalThomsen.DeepFan.CriterionConverse
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module TauCeti.Toric

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem coneDivisorCharacter_ray (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (ray : fan.Ray) (contains : embedding ray.val ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    fan.coneDivisorCharacter basis cone_basis divisor ray.val = -divisor ray := by
  obtain ⟨index, same⟩ := fan.ray_eq_basis_of_mem_coneBasis basis cone_basis ray contains
  have same_ray : fan.basisRay basis cone_basis index = ray := Subtype.ext same
  rw [← same, fan.coneDivisorCharacter_basis, same_ray]

theorem coneDivisorCharacter_eqOn_commonCone (fan : TauCeti.Toric.Fan embedding)
    {firstDimension secondDimension : ℕ}
    (first : Basis (Fin firstDimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin secondDimension) ℤ Lattice) (second_cone : fan.IsConeBasis second)
    (divisor : fan.InvariantRayDivisor) (common : PointedCone ℝ Ambient)
    (common_member : common ∈ fan.cones)
    (common_first : common ≤ PointedCone.hull ℝ
      (Set.range (fun index => embedding (first index))))
    (common_second : common ≤ PointedCone.hull ℝ
      (Set.range (fun index => embedding (second index)))) :
    Set.EqOn (fan.lattice.realCharacter (fan.coneDivisorCharacter first first_cone divisor))
      (fan.lattice.realCharacter (fan.coneDivisorCharacter second second_cone divisor)) common := by
  let toric := fan.isToricCone common_member
  have generators_agree : Set.EqOn
      (fan.lattice.realCharacter (fan.coneDivisorCharacter first first_cone divisor))
      (fan.lattice.realCharacter (fan.coneDivisorCharacter second second_cone divisor))
      (embedding '' Set.range (primitiveGenerator fan.lattice toric)) := by
    rintro vector ⟨generator, ⟨ray, rfl⟩, rfl⟩
    let actual : fan.Ray := ⟨primitiveGenerator fan.lattice toric ray,
      primitiveGenerator_isPrimitive fan.lattice toric ray, by
        have singleton := ray.eq_hull_singleton (toric.salient.anti ray.1.isFaceOf.le)
          (primitiveGenerator_mem fan.lattice toric ray)
          (by simpa only [map_zero] using
            (fan.lattice.injective.ne (primitiveGenerator_ne_zero fan.lattice toric ray)))
        rw [← singleton]
        exact fan.mem_of_isFaceOf common_member ray.1.isFaceOf⟩
    have in_common : embedding actual.val ∈ common :=
      ray.1.isFaceOf.le (primitiveGenerator_mem fan.lattice toric ray)
    change fan.lattice.realCharacter (fan.coneDivisorCharacter first first_cone divisor)
        (embedding actual.val) =
      fan.lattice.realCharacter (fan.coneDivisorCharacter second second_cone divisor)
        (embedding actual.val)
    rw [fan.lattice.realCharacter_apply, fan.lattice.realCharacter_apply,
      fan.coneDivisorCharacter_ray first first_cone divisor actual (common_first in_common),
      fan.coneDivisorCharacter_ray second second_cone divisor actual (common_second in_common)]
  intro point contains
  have hull_member : point ∈ PointedCone.hull ℝ
      (embedding '' Set.range (primitiveGenerator fan.lattice toric)) := by
    rwa [toric.hull_primitiveGenerator fan.lattice]
  exact LinearMap.eqOn_span generators_agree
    (PointedCone.hull_le_span ℝ _ hull_member)

theorem coneDivisorCharacter_eqOn_intersection (fan : TauCeti.Toric.Fan embedding)
    {firstDimension secondDimension : ℕ}
    (first : Basis (Fin firstDimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin secondDimension) ℤ Lattice) (second_cone : fan.IsConeBasis second)
    (divisor : fan.InvariantRayDivisor) :
    Set.EqOn (fan.lattice.realCharacter (fan.coneDivisorCharacter first first_cone divisor))
      (fan.lattice.realCharacter (fan.coneDivisorCharacter second second_cone divisor))
      (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
        PointedCone.hull ℝ (Set.range (fun index => embedding (second index))) :
        PointedCone ℝ Ambient) :=
  fan.coneDivisorCharacter_eqOn_commonCone first first_cone second second_cone divisor _
    (fan.inf_mem first_cone second_cone) inf_le_left inf_le_right

theorem coneDivisorCharacter_transition_dualSemigroup (fan : TauCeti.Toric.Fan embedding)
    {firstDimension secondDimension : ℕ}
    (first : Basis (Fin firstDimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin secondDimension) ℤ Lattice) (second_cone : fan.IsConeBasis second)
    (divisor : fan.InvariantRayDivisor) :
    let common := PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
      PointedCone.hull ℝ (Set.range (fun index => embedding (second index)))
    let transition := fan.coneDivisorCharacter first first_cone divisor -
      fan.coneDivisorCharacter second second_cone divisor
    transition ∈ dualSemigroup fan.lattice common ∧
      -transition ∈ dualSemigroup fan.lattice common := by
  dsimp only
  have agree := fan.coneDivisorCharacter_eqOn_intersection first first_cone second second_cone divisor
  constructor
  · rw [mem_dualSemigroup]
    intro point contains
    simp only [map_sub, LinearMap.sub_apply, agree contains, sub_self, le_refl]
  · rw [mem_dualSemigroup]
    intro point contains
    simp only [map_neg, map_sub, LinearMap.neg_apply, LinearMap.sub_apply,
      agree contains, sub_self, neg_zero, le_refl]

section Complete

variable [FiniteDimensional ℝ Ambient]

noncomputable def divisorSupportFunction (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (point : Ambient) : ℝ :=
  let covering := fan.exists_coneBasis_containing complete regular point
  let basis := covering.choose_spec.choose
  fan.lattice.realCharacter
    (fan.coneDivisorCharacter basis covering.choose_spec.choose_spec.1 divisor) point

theorem divisorSupportFunction_on_coneBasis (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (point : Ambient) (contains : point ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    fan.divisorSupportFunction complete regular divisor point =
      fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor) point := by
  let covering := fan.exists_coneBasis_containing complete regular point
  exact fan.coneDivisorCharacter_eqOn_intersection covering.choose_spec.choose
    covering.choose_spec.choose_spec.1 basis cone_basis divisor
    ⟨covering.choose_spec.choose_spec.2, contains⟩

theorem divisorSupportFunction_ray (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray) :
    fan.divisorSupportFunction complete regular divisor (embedding ray.val) =
      (-divisor ray : ℤ) := by
  obtain ⟨dimension, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (embedding ray.val)
  rw [fan.divisorSupportFunction_on_coneBasis complete regular divisor basis cone_basis
    (embedding ray.val) contains, fan.lattice.realCharacter_apply,
    fan.coneDivisorCharacter_ray basis cone_basis divisor ray contains]

theorem divisorSupportFunction_smul (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (scalar : ℝ) (nonnegative : 0 ≤ scalar)
    (point : Ambient) :
    fan.divisorSupportFunction complete regular divisor (scalar • point) =
      scalar * fan.divisorSupportFunction complete regular divisor point := by
  obtain ⟨dimension, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular point
  rw [fan.divisorSupportFunction_on_coneBasis complete regular divisor basis cone_basis
      (scalar • point) (PointedCone.smul_mem _ nonnegative contains),
    fan.divisorSupportFunction_on_coneBasis complete regular divisor basis cone_basis point contains,
    map_smul, smul_eq_mul]

theorem divisorSupportFunction_eqOn_cone (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (cone : PointedCone ℝ Ambient)
    (member : cone ∈ fan.cones) :
    ∃ character : Lattice →+ ℤ,
      Set.EqOn (fan.divisorSupportFunction complete regular divisor)
        (fan.lattice.realCharacter character) cone := by
  obtain ⟨dimension, basis, cone_basis, face⟩ :=
    fan.exists_coneBasis_above complete regular cone member
  exact ⟨fan.coneDivisorCharacter basis cone_basis divisor,
    fun point contains => fan.divisorSupportFunction_on_coneBasis complete regular
      divisor basis cone_basis point (face.le contains)⟩

theorem divisorSupportFunction_continuous (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) :
    Continuous (fan.divisorSupportFunction complete regular divisor) := by
  let cones : fan.cones → Set Ambient := fun cone => cone.val
  apply (locallyFinite_of_finite cones).continuous
  · ext point
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨cone, member, contains⟩ := (fan.isComplete_iff.mp complete) point
    exact ⟨⟨cone, member⟩, contains⟩
  · intro cone
    exact fan.cone_isClosed cone.val cone.property
  · intro cone
    obtain ⟨character, agrees⟩ :=
      fan.divisorSupportFunction_eqOn_cone complete regular divisor cone.val cone.property
    exact (fan.lattice.realCharacter character).continuous_of_finiteDimensional.continuousOn.congr agrees

end Complete

end TauCeti.Toric.Fan
