module

public import BondalThomsen.Toric.Scheme.CompleteRegularStar
public import BondalThomsen.Toric.Scheme.ValuationConeSelection
public import BondalThomsen.DeepFan.StarDeep

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem complete_regular_valuativeSquare_hasLift_of_basis {dimension : ℕ}
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin dimension) ℤ Lattice)
    (square : ValuativeCommSq (fan.structureMap 𝕜 regular)) : square.commSq.HasLift := by
  induction dimension using Nat.strong_induction_on generalizing Lattice Ambient with
  | h dimension induction =>
    have nonempty : Nonempty fan.cones := by
      obtain ⟨cone, member, _⟩ := fan.isComplete_iff.mp complete 0
      exact ⟨⟨cone, member⟩⟩
    obtain torus_case | star_case := fan.complete_regular_fieldMorphism_torus_or_star 𝕜
      complete regular nonempty square.i₁
    · obtain ⟨torus_generic, factorization⟩ := torus_case
      exact fan.complete_regular_valuationTorusSquare_hasLift 𝕜 complete regular nonempty square
        torus_generic factorization
    · obtain ⟨ray, star_generic, factorization⟩ := star_case
      let : IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
        Submodule.closed_of_finiteDimensional _
      have source_rank : Module.finrank ℝ Ambient = dimension := by
        simpa only [Fintype.card_fin] using
          finrank_eq_card_basis (fan.lattice.isBaseChange.basis reference)
      have star_rank : Module.finrank ℝ (fan.StarAmbient ray) = dimension - 1 := by
        have drop := fan.starAmbient_finrank_add_one ray
        omega
      have smaller : dimension - 1 < dimension := by
        have drop := fan.starAmbient_finrank_lt ray
        omega
      let := (fan.star ray).lattice.free
      let := (fan.star ray).lattice.finite
      have integral_rank : Module.finrank ℤ (fan.StarLattice ray) = dimension - 1 := by
        rw [← (fan.star ray).lattice.isBaseChange.finrank_eq]
        exact star_rank
      let star_reference := Module.finBasisOfFinrankEq ℤ (fan.StarLattice ray) integral_rank
      have star_existence : ValuativeCriterion.Existence
          ((fan.star ray).structureMap 𝕜 (fan.star_isRegular complete regular ray)) := by
        intro star_square
        exact induction (dimension - 1) smaller (fan.star ray)
          (fan.star_isComplete_of_isComplete complete ray)
          (fan.star_isRegular complete regular ray) star_reference star_square
      exact fan.starImage_valuativeSquare_hasLift_of_starExistence 𝕜 regular ray
        (fan.star_isRegular complete regular ray) star_existence square star_generic factorization

theorem complete_regular_valuativeSquare_hasLift
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (square : ValuativeCommSq (fan.structureMap 𝕜 regular)) : square.commSq.HasLift := by
  let := fan.lattice.free
  let := fan.lattice.finite
  exact fan.complete_regular_valuativeSquare_hasLift_of_basis 𝕜 complete regular
    (Module.finBasis ℤ Lattice) square

theorem complete_regular_valuativeCriterion
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    ValuativeCriterion (fan.structureMap 𝕜 regular) := by
  intro square
  let := fan.structureMap_isSeparated 𝕜 regular
  let : Subsingleton square.commSq.LiftStruct :=
    IsSeparated.valuativeCriterion (fan.structureMap 𝕜 regular) square
  obtain ⟨⟨lift⟩⟩ := fan.complete_regular_valuativeSquare_hasLift 𝕜 complete regular square
  exact ⟨{ default := lift, uniq := fun other => Subsingleton.elim _ _ }⟩

theorem complete_regular_structureMap_isProper
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    IsProper (fan.structureMap 𝕜 regular) := by
  let := fan.structureMap_locallyOfFiniteType 𝕜 regular
  let := fan.structureMap_quasiCompact 𝕜 regular
  let := fan.structureMap_isSeparated 𝕜 regular
  exact IsProper.of_valuativeCriterion _
    (fan.complete_regular_valuativeCriterion 𝕜 complete regular)

end TauCeti.Toric.Fan
