module

public import BondalThomsen.Toric.Divisor.CartierData
public import Mathlib.Analysis.Convex.Function

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module TauCeti.Toric

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def HasRaySupportInequalities (fan : TauCeti.Toric.Fan embedding)
    (divisor : fan.InvariantRayDivisor) : Prop :=
  ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (ray : fan.Ray),
      -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val

theorem divisorSupportFunction_le_coneCharacter (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (point : Ambient) :
    fan.divisorSupportFunction complete regular divisor point ≤
      fan.lattice.realCharacter (fan.coneDivisorCharacter basis cone_basis divisor) point := by
  obtain ⟨other_dimension, other, other_cone, contains⟩ :=
    fan.exists_coneBasis_containing complete regular point
  let difference := fan.coneDivisorCharacter basis cone_basis divisor -
    fan.coneDivisorCharacter other other_cone divisor
  have dual_member : difference ∈ dualSemigroup fan.lattice
      (PointedCone.hull ℝ (embedding '' Set.range other)) := by
    rw [mem_dualSemigroup_hull_image]
    rintro vector ⟨index, rfl⟩
    have bound := support dimension basis cone_basis (fan.basisRay other other_cone index)
    change 0 ≤ fan.coneDivisorCharacter basis cone_basis divisor (other index) -
      fan.coneDivisorCharacter other other_cone divisor (other index)
    rw [fan.coneDivisorCharacter_basis]
    change -divisor (fan.basisRay other other_cone index) ≤
      fan.coneDivisorCharacter basis cone_basis divisor (other index) at bound
    omega
  have in_hull : point ∈ PointedCone.hull ℝ (embedding '' Set.range other) := by
    have same_range : embedding '' Set.range other =
        Set.range (fun index => embedding (other index)) := by
      ext vector
      simp
    rwa [same_range]
  have nonnegative := (mem_dualSemigroup fan.lattice difference).mp dual_member in_hull
  change 0 ≤ fan.lattice.realCharacter difference point at nonnegative
  simp only [difference, map_sub, LinearMap.sub_apply] at nonnegative
  rw [fan.divisorSupportFunction_on_coneBasis complete regular divisor other other_cone point contains]
  exact sub_nonneg.mp nonnegative

theorem divisorSupportFunction_concave (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor) :
    ConcaveOn ℝ Set.univ (fan.divisorSupportFunction complete regular divisor) := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ first_weight second_weight first_nonnegative second_nonnegative _
  obtain ⟨dimension, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (first_weight • first + second_weight • second)
  have first_bound := fan.divisorSupportFunction_le_coneCharacter complete regular divisor
    support basis cone_basis first
  have second_bound := fan.divisorSupportFunction_le_coneCharacter complete regular divisor
    support basis cone_basis second
  rw [fan.divisorSupportFunction_on_coneBasis complete regular divisor basis cone_basis _ contains,
    map_add, map_smul, map_smul]
  exact add_le_add (smul_le_smul_of_nonneg_left first_bound first_nonnegative)
    (smul_le_smul_of_nonneg_left second_bound second_nonnegative)

theorem divisorSupportFunction_superadditive_of_concave
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (concave : ConcaveOn ℝ Set.univ (fan.divisorSupportFunction complete regular divisor))
    (first second : Ambient) :
    fan.divisorSupportFunction complete regular divisor first +
        fan.divisorSupportFunction complete regular divisor second ≤
      fan.divisorSupportFunction complete regular divisor (first + second) := by
  have midpoint := concave.2 (Set.mem_univ first) (Set.mem_univ second)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  rw [← smul_add, ← smul_add, fan.divisorSupportFunction_smul complete regular divisor (1 / 2)
    (by norm_num)] at midpoint
  simp only [smul_eq_mul] at midpoint
  linarith

theorem hasRaySupportInequalities_of_concave (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (concave : ConcaveOn ℝ Set.univ (fan.divisorSupportFunction complete regular divisor)) :
    fan.HasRaySupportInequalities divisor := by
  classical
  intro dimension basis cone_basis ray
  let upper : Lattice := basis.equivFun.symm (fun index => max (basis.repr ray.val index) 0)
  have upper_coordinates : ∀ index, basis.repr upper index = max (basis.repr ray.val index) 0 := by
    intro index
    change basis.equivFun upper index = _
    simp only [upper, LinearEquiv.apply_symm_apply]
  have upper_member := fan.mem_coneBasis_of_repr_nonnegative basis upper
    (fun index => by rw [upper_coordinates]; exact le_max_right _ _)
  have lower_member := fan.mem_coneBasis_of_repr_nonnegative basis (upper - ray.val)
    (fun index => by
      rw [map_sub, Finsupp.sub_apply, upper_coordinates]
      exact sub_nonneg.mpr (le_max_left _ _))
  have bound := fan.divisorSupportFunction_superadditive_of_concave complete regular divisor
    concave (embedding (upper - ray.val)) (embedding ray.val)
  rw [← map_add, sub_add_cancel,
    fan.divisorSupportFunction_on_coneBasis complete regular divisor basis cone_basis _ upper_member,
    fan.divisorSupportFunction_on_coneBasis complete regular divisor basis cone_basis _ lower_member,
    fan.divisorSupportFunction_ray complete regular divisor ray,
    fan.lattice.realCharacter_apply, fan.lattice.realCharacter_apply, map_sub] at bound
  have real_bound : ((-divisor ray : ℤ) : ℝ) ≤
      (fan.coneDivisorCharacter basis cone_basis divisor ray.val : ℝ) := by
    push_cast at bound
    push_cast
    linarith
  exact_mod_cast real_bound

end TauCeti.Toric.Fan
