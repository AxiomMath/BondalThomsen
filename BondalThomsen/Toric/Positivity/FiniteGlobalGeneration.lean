module

public import BondalThomsen.Toric.Projective.AllSectionPullbackSheafIso
public import BondalThomsen.Toric.Positivity.GlobalGenerationCriterion

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)

noncomputable def allDivisorMonomialSheafSectionFamily
    (exponent : fan.globalDivisorSectionExponents divisor) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.sections :=
  (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.unitHomEquiv
    (fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor exponent)

noncomputable def allDivisorMonomialSheafEvaluation :
    SheafOfModules.free (R := (fan.algebraicRealization 𝕜 regular).ringCatSheaf)
      (fan.globalDivisorSectionExponents divisor) ⟶
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj :=
  (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.freeHomEquiv.symm
    (fan.allDivisorMonomialSheafSectionFamily 𝕜 complete regular divisor)

variable (support : fan.HasRaySupportInequalities divisor)

theorem allDivisorMonomialSheafSectionFamily_denominator
    (chart : Fin (Nat.card fan.cones)) :
    fan.allDivisorMonomialSheafSectionFamily 𝕜 complete regular divisor
        (fan.allSectionProjectiveDenominator complete regular divisor support chart) =
      fan.invariantDivisorSheafGeneratorFamily 𝕜 complete regular divisor support chart := by
  unfold allDivisorMonomialSheafSectionFamily
  rw [fan.allSectionProjectiveSourceCoordinateHom_denominator 𝕜 complete regular divisor support chart]
  unfold divisorProjectiveSourceCoordinateHom BondalThomsen.moduleGlobalSectionHom
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro open_set
  rfl

noncomputable def divisorCartierToAllMonomialFreeMap :
    SheafOfModules.free (R := (fan.algebraicRealization 𝕜 regular).ringCatSheaf)
      (Fin (Nat.card fan.cones)) ⟶
    SheafOfModules.free (R := (fan.algebraicRealization 𝕜 regular).ringCatSheaf)
      (fan.globalDivisorSectionExponents divisor) :=
  SheafOfModules.freeMap (fan.allSectionProjectiveDenominator complete regular divisor support)

theorem divisorCartierToAllMonomialFreeMap_evaluation :
    fan.divisorCartierToAllMonomialFreeMap 𝕜 complete regular divisor support ≫
        fan.allDivisorMonomialSheafEvaluation 𝕜 complete regular divisor =
      fan.invariantDivisorSheafEvaluation 𝕜 complete regular divisor support := by
  apply (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.freeHomEquiv.injective
  funext chart
  rw [SheafOfModules.freeHomEquiv_comp_apply]
  simp only [divisorCartierToAllMonomialFreeMap, SheafOfModules.freeHomEquiv_freeMap,
    Function.comp_apply, allDivisorMonomialSheafEvaluation,
    SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection,
    invariantDivisorSheafEvaluation, Equiv.apply_symm_apply]
  exact fan.allDivisorMonomialSheafSectionFamily_denominator 𝕜 complete regular divisor support chart

include support in
theorem allDivisorMonomialSheafEvaluation_epi :
    Epi (fan.allDivisorMonomialSheafEvaluation 𝕜 complete regular divisor) := by
  let := fan.invariantDivisorSheafEvaluation_epi 𝕜 complete regular divisor support
  exact epi_of_epi_fac (fan.divisorCartierToAllMonomialFreeMap_evaluation 𝕜 complete regular divisor support)

noncomputable def allDivisorMonomialSheafGeneratingSections :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.GeneratingSections where
  I := fan.globalDivisorSectionExponents divisor
  s := fan.allDivisorMonomialSheafSectionFamily 𝕜 complete regular divisor
  epi := fan.allDivisorMonomialSheafEvaluation_epi 𝕜 complete regular divisor support

variable {𝕜} in
instance allDivisorMonomialSheafGeneratingSections_isFiniteType :
    (fan.allDivisorMonomialSheafGeneratingSections 𝕜 complete regular divisor support).IsFiniteType where
  finite := fan.allDivisorMonomialCharacters_finite complete regular divisor

end TauCeti.Toric.Fan
