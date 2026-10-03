module

public import BondalThomsen.Cohomology.FiniteAffineCechAllDegreeComparison
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryCechNonvanishing
public import BondalThomsen.Toric.Positivity.SupportConcavity
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TauCeti.Toric Multiplicative
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.ToricPrimitiveWeightZeroComplex
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ToricNefCechAcyclicity

def scalarSimplexDifferential {Index : Type*} (degree : ℕ)
    (cochain : (Fin (degree + 1) → Index) → 𝕜)
    (tuple : Fin (degree + 2) → Index) : 𝕜 :=
  ∑ deleted : Fin (degree + 2), (-1 : 𝕜) ^ deleted.val *
    cochain (tuple ∘ deleted.succAbove)

def scalarSimplexContraction {Index : Type*} (anchor : Index) (degree : ℕ)
    (cochain : (Fin (degree + 2) → Index) → 𝕜)
    (tuple : Fin (degree + 1) → Index) : 𝕜 :=
  cochain (Fin.cons anchor tuple)

theorem scalarSimplexContraction_identity {Index : Type*} (anchor : Index) (degree : ℕ)
    (cochain : (Fin (degree + 2) → Index) → 𝕜) (tuple : Fin (degree + 2) → Index) :
    scalarSimplexDifferential 𝕜 degree (scalarSimplexContraction 𝕜 anchor degree cochain) tuple +
      scalarSimplexContraction 𝕜 anchor (degree + 1)
        (scalarSimplexDifferential 𝕜 (degree + 1) cochain) tuple = cochain tuple := by
  unfold scalarSimplexDifferential scalarSimplexContraction
  dsimp only
  rw [Fin.sum_univ_succ (fun deleted : Fin (degree + 3) =>
    (-1 : 𝕜) ^ deleted.val * cochain (Fin.cons anchor tuple ∘ deleted.succAbove))]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.cons_comp_succ, Fin.val_succ,
    Fin.cons_comp_succ_succAbove]
  have cancellation :
      (∑ deleted : Fin (degree + 2), (-1 : 𝕜) ^ deleted.val *
        cochain (Fin.cons anchor (tuple ∘ deleted.succAbove))) +
      (∑ deleted : Fin (degree + 2), (-1 : 𝕜) ^ (deleted.val + 1) *
        cochain (Fin.cons anchor (tuple ∘ deleted.succAbove))) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro deleted _
    rw [pow_succ]
    ring
  have remove_eq (deleted : Fin (degree + 2)) :
      deleted.removeNth tuple = tuple ∘ deleted.succAbove := by
    funext entry
    exact Fin.removeNth_apply deleted tuple entry
  simp_rw [remove_eq]
  linear_combination cancellation

end BondalThomsen.ToricNefCechAcyclicity

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable section

def divisorWeightForbiddenRegion (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) : Set Ambient :=
  {point | fan.lattice.realCharacter character point <
    fan.divisorSupportFunction complete regular divisor point}

theorem divisorWeightForbiddenRegion_ray_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) (ray : fan.Ray) :
    embedding ray.val ∈ fan.divisorWeightForbiddenRegion complete regular divisor character ↔
      divisor ray + character ray.val < 0 := by
  unfold divisorWeightForbiddenRegion
  simp only [Set.mem_ofPred_eq, fan.lattice.realCharacter_apply,
    fan.divisorSupportFunction_ray]
  rw [Int.cast_lt]
  omega

theorem divisorWeightForbiddenRegion_convex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)
    (character : Lattice →+ ℤ) :
    Convex ℝ (fan.divisorWeightForbiddenRegion complete regular divisor character) := by
  have concavity := (fan.divisorSupportFunction_concave complete regular divisor support).sub
    ((fan.lattice.realCharacter character).convexOn convex_univ)
  simpa only [divisorWeightForbiddenRegion, Set.mem_univ, true_and,
    Pi.sub_apply, sub_pos] using concavity.convex_gt 0

theorem divisorSectionExponents_iff_forbiddenRegion_disjoint (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) (cone : fan.cones) :
    ofAdd character ∈ fan.divisorSectionExponents cone.val divisor ↔
      Disjoint (cone.val : Set Ambient)
        (fan.divisorWeightForbiddenRegion complete regular divisor character) := by
  obtain ⟨chartCharacter, presentation⟩ :=
    fan.divisorSupportFunction_eqOn_cone complete regular divisor cone.val cone.property
  have ray_presentation : ∀ ray : fan.Ray, embedding ray.val ∈ cone.val →
      chartCharacter ray.val = -divisor ray := by
    intro ray contains
    have same := presentation contains
    rw [fan.divisorSupportFunction_ray, fan.lattice.realCharacter_apply] at same
    exact_mod_cast same.symm
  change (∀ ray : fan.Ray, embedding ray.val ∈ cone.val → -divisor ray ≤ character ray.val) ↔ _
  rw [← fan.translatedCharacter_mem_dualSemigroup_iff_rays cone divisor chartCharacter character
    ray_presentation, mem_dualSemigroup]
  constructor
  · intro nonnegative
    apply Set.disjoint_left.mpr
    intro point contains forbidden
    have bound := nonnegative contains
    simp only [map_sub, LinearMap.sub_apply] at bound
    change fan.lattice.realCharacter character point <
      fan.divisorSupportFunction complete regular divisor point at forbidden
    rw [presentation contains] at forbidden
    linarith
  · intro disjoint point contains
    have absent := Set.disjoint_left.mp disjoint contains
    change ¬fan.lattice.realCharacter character point <
      fan.divisorSupportFunction complete regular divisor point at absent
    rw [presentation contains] at absent
    simp only [map_sub, LinearMap.sub_apply]
    exact sub_nonneg.mpr (not_lt.mp absent)

end

end TauCeti.Toric.Fan
