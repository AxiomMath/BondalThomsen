module

public import BondalThomsen.Toric.Cohomology.CechNegativeSupportComparison
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryCechNonvanishing
public import BondalThomsen.Toric.Cohomology.NefCechAcyclicity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open TauCeti.Toric Multiplicative
open BondalThomsen.ToricCechNegativeSupportComparison
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem divisorWeightForbiddenRegion_inter_cone_nonempty_iff_negativeRay (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) (cone : fan.cones) :
    ((cone.val : Set Ambient) ∩
      fan.divisorWeightForbiddenRegion complete regular divisor character).Nonempty ↔
        ∃ ray : fan.Ray, fan.cechCharacterNegativeRay divisor character ray ∧
          embedding ray.val ∈ cone.val := by
  rw [← Set.not_disjoint_iff_nonempty_inter,
    ← fan.divisorSectionExponents_iff_forbiddenRegion_disjoint complete regular divisor character cone]
  change (¬ ∀ ray : fan.Ray, embedding ray.val ∈ cone.val → -divisor ray ≤ character ray.val) ↔ _
  push Not
  constructor
  · rintro ⟨ray, contains, negative⟩
    exact ⟨ray, by change divisor ray + character ray.val < 0; omega, contains⟩
  · rintro ⟨ray, negative, contains⟩
    exact ⟨ray, contains, by change divisor ray + character ray.val < 0 at negative; omega⟩

theorem divisorWeightForbiddenRegion_nonempty_iff_negativeRay (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) :
    (fan.divisorWeightForbiddenRegion complete regular divisor character).Nonempty ↔
      ∃ ray : fan.Ray, fan.cechCharacterNegativeRay divisor character ray := by
  constructor
  · rintro ⟨point, forbidden⟩
    obtain ⟨cone, member, contains⟩ := fan.isComplete_iff.mp complete point
    obtain ⟨ray, negative, _⟩ :=
      (fan.divisorWeightForbiddenRegion_inter_cone_nonempty_iff_negativeRay
        complete regular divisor character ⟨cone, member⟩).mp ⟨point, contains, forbidden⟩
    exact ⟨ray, negative⟩
  · rintro ⟨ray, negative⟩
    exact ⟨embedding ray.val,
      (fan.divisorWeightForbiddenRegion_ray_iff complete regular divisor character ray).mpr negative⟩

noncomputable def divisorForbiddenChartPatch (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ)
    (chart : Fin (Nat.card fan.cones)) : Set Ambient :=
  ((fan.divisorLocalCone 𝕜 complete regular chart).val : Set Ambient) ∩
    fan.divisorWeightForbiddenRegion complete regular divisor character

theorem divisorForbiddenChartPatch_cover (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) :
    (⋃ chart, fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character chart) =
      fan.divisorWeightForbiddenRegion complete regular divisor character := by
  ext point
  constructor
  · intro member
    obtain ⟨chart, member⟩ := Set.mem_iUnion.mp member
    exact member.2
  · intro forbidden
    obtain ⟨cone, member, contains⟩ := fan.isComplete_iff.mp complete point
    let actual_cone : fan.cones := ⟨cone, member⟩
    exact Set.mem_iUnion.mpr ⟨(Finite.equivFin fan.cones) actual_cone,
      fan.divisorLocalCone_contains_cone 𝕜 complete regular actual_cone contains, forbidden⟩

theorem divisorForbiddenChartPatch_isClosed_in_region (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ)
    (chart : Fin (Nat.card fan.cones)) :
    IsClosed {point : fan.divisorWeightForbiddenRegion complete regular divisor character |
      point.val ∈ fan.divisorForbiddenChartPatch 𝕜 complete regular divisor character chart} := by
  have cone_closed := fan.cone_isClosed (fan.divisorLocalCone 𝕜 complete regular chart).val
    (fan.divisorLocalCone 𝕜 complete regular chart).property
  convert cone_closed.preimage continuous_subtype_val using 1
  ext point
  exact and_iff_left point.property

noncomputable def cechFiniteChartCone (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (charts : Finset (Fin (Nat.card fan.cones))) (nonempty : charts.Nonempty) : fan.cones :=
  charts.inf' nonempty (fan.divisorLocalCone 𝕜 complete regular)

theorem mem_cechFiniteChartCone_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (charts : Finset (Fin (Nat.card fan.cones))) (nonempty : charts.Nonempty) (point : Ambient) :
    point ∈ (fan.cechFiniteChartCone 𝕜 complete regular charts nonempty).val ↔
      ∀ chart ∈ charts, point ∈ (fan.divisorLocalCone 𝕜 complete regular chart).val := by
  unfold cechFiniteChartCone
  induction charts using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty nonempty).elim
  | @insert chart rest absent induction =>
    by_cases rest_nonempty : rest.Nonempty
    · rw [Finset.inf'_insert rest_nonempty]
      change (point ∈ (fan.divisorLocalCone 𝕜 complete regular chart).val ∧
        point ∈ (rest.inf' rest_nonempty (fan.divisorLocalCone 𝕜 complete regular)).val) ↔ _
      rw [induction rest_nonempty]
      simp only [Finset.mem_insert, forall_eq_or_imp]
    · have rest_empty : rest = ∅ := Finset.not_nonempty_iff_eq_empty.mp rest_nonempty
      subst rest
      simp

noncomputable def divisorForbiddenChartIntersection (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ)
    (charts : Finset (Fin (Nat.card fan.cones))) : Set Ambient :=
  fan.divisorWeightForbiddenRegion complete regular divisor character ∩
    ⋂ chart ∈ charts, ((fan.divisorLocalCone 𝕜 complete regular chart).val : Set Ambient)

theorem mem_divisorForbiddenChartIntersection_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ)
    (charts : Finset (Fin (Nat.card fan.cones))) (point : Ambient) :
    point ∈ fan.divisorForbiddenChartIntersection 𝕜 complete regular divisor character charts ↔
      point ∈ fan.divisorWeightForbiddenRegion complete regular divisor character ∧
        ∀ chart ∈ charts, point ∈ (fan.divisorLocalCone 𝕜 complete regular chart).val := by
  simp only [divisorForbiddenChartIntersection, Set.mem_inter_iff, Set.mem_iInter]
  rfl

theorem divisorForbiddenChartIntersection_nonempty_iff_negativeRay (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ)
    (charts : Finset (Fin (Nat.card fan.cones))) (nonempty : charts.Nonempty) :
    (fan.divisorForbiddenChartIntersection 𝕜 complete regular divisor character charts).Nonempty ↔
      ∃ ray : fan.Ray, fan.cechCharacterNegativeRay divisor character ray ∧
        ∀ chart ∈ charts, fan.cechRayChartIncidence 𝕜 complete regular ray chart := by
  have intersection_eq : fan.divisorForbiddenChartIntersection 𝕜 complete regular divisor character charts =
      ((fan.cechFiniteChartCone 𝕜 complete regular charts nonempty).val : Set Ambient) ∩
        fan.divisorWeightForbiddenRegion complete regular divisor character := by
    ext point
    rw [mem_divisorForbiddenChartIntersection_iff, Set.mem_inter_iff]
    change (point ∈ fan.divisorWeightForbiddenRegion complete regular divisor character ∧
      ∀ chart ∈ charts, point ∈ (fan.divisorLocalCone 𝕜 complete regular chart).val) ↔
        point ∈ (fan.cechFiniteChartCone 𝕜 complete regular charts nonempty).val ∧
          point ∈ fan.divisorWeightForbiddenRegion complete regular divisor character
    rw [mem_cechFiniteChartCone_iff]
    exact and_comm
  rw [intersection_eq, fan.divisorWeightForbiddenRegion_inter_cone_nonempty_iff_negativeRay
    complete regular divisor character]
  constructor
  · rintro ⟨ray, negative, contains⟩
    exact ⟨ray, negative,
      (fan.mem_cechFiniteChartCone_iff 𝕜 complete regular charts nonempty (embedding ray.val)).mp contains⟩
  · rintro ⟨ray, negative, contains⟩
    exact ⟨ray, negative,
      (fan.mem_cechFiniteChartCone_iff 𝕜 complete regular charts nonempty (embedding ray.val)).mpr contains⟩

noncomputable def divisorForbiddenChartNerve (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) :
    PreAbstractSimplicialComplex (Fin (Nat.card fan.cones)) :=
  negativeChartComplex (fun point chart =>
    point ∈ (fan.divisorLocalCone 𝕜 complete regular chart).val)
    (fun point => point ∈ fan.divisorWeightForbiddenRegion complete regular divisor character)

theorem mem_divisorForbiddenChartNerve_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ)
    (charts : Finset (Fin (Nat.card fan.cones))) :
    charts ∈ fan.divisorForbiddenChartNerve 𝕜 complete regular divisor character ↔
      charts.Nonempty ∧
        (fan.divisorForbiddenChartIntersection 𝕜 complete regular divisor character charts).Nonempty := by
  change (charts.Nonempty ∧ ∃ point,
    point ∈ fan.divisorWeightForbiddenRegion complete regular divisor character ∧
      ∀ chart ∈ charts, point ∈ (fan.divisorLocalCone 𝕜 complete regular chart).val) ↔ _
  simp only [Set.Nonempty, mem_divisorForbiddenChartIntersection_iff]

theorem divisorForbiddenChartNerve_eq_negativeChartComplex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) :
    fan.divisorForbiddenChartNerve 𝕜 complete regular divisor character =
      negativeChartComplex (fan.cechRayChartIncidence 𝕜 complete regular)
        (fan.cechCharacterNegativeRay divisor character) := by
  apply PreAbstractSimplicialComplex.ext
  ext charts
  change charts ∈ fan.divisorForbiddenChartNerve 𝕜 complete regular divisor character ↔
    charts ∈ negativeChartComplex (fan.cechRayChartIncidence 𝕜 complete regular)
      (fan.cechCharacterNegativeRay divisor character)
  rw [mem_divisorForbiddenChartNerve_iff]
  constructor
  · rintro ⟨nonempty, intersects⟩
    exact ⟨nonempty, (fan.divisorForbiddenChartIntersection_nonempty_iff_negativeRay 𝕜
      complete regular divisor character charts nonempty).mp intersects⟩
  · rintro ⟨nonempty, ray, negative, contains⟩
    exact ⟨nonempty, (fan.divisorForbiddenChartIntersection_nonempty_iff_negativeRay 𝕜
      complete regular divisor character charts nonempty).mpr ⟨ray, negative, contains⟩⟩

end TauCeti.Toric.Fan
