module

public import BondalThomsen.Toric.Cohomology.DemazureAllDegree
public import BondalThomsen.Toric.Positivity.NefMoriProof
public import BondalThomsen.Toric.Positivity.ReidConeExtension
public import BondalThomsen.Collection.SectionThree.ActualFanoSupport
public import BondalThomsen.LineBundle.PicardGeometricNef
public import BondalThomsen.Toric.Positivity.SemiampleClassCriterion
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Collection.SectionThree.Equivalences
public import BondalThomsen.Toric.Cohomology.PrimitivePairCohomology
public import BondalThomsen.Toric.Frobenius.FrobeniusRemainingSteps
public import BondalThomsen.Cohomology.FiniteAffineCoverQuasicoherentExtensions
public import BondalThomsen.Toric.Frobenius.MultiplicationGlobalResidueIso
public import BondalThomsen.DeepFan.PrimitiveCoefficientCriterion
public import BondalThomsen.Rarity.DeepFanUnconditionalCounting
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryDerivedCohomology
public import BondalThomsen.Toric.Cohomology.NefFirstCohomologyVanishing

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem primitiveNefCriterion_proved
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : ToricSchemeIsProjective 𝕜 fan regular) :
    letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
      ⟨fan.structureMap 𝕜 regular⟩
    ToricClassNefPrimitiveCriterion fan
      (fun divisorClass => SchemeLineBundleClassIsNef (baseField := 𝕜)
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass)))
      (fun _left _right relation => relation.IsMoriExtremal 𝕜 complete regular) :=
  toricNefMoriCriterion_proved 𝕜 Lattice Ambient embedding fan complete regular projective

theorem necessaryNefSupport_proved
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (dimension : ℕ) :
    letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
      ⟨fan.structureMap 𝕜 regular⟩
    ToricNefSupportCriterion fan dimension (fun divisor =>
      SchemeLineBundleClassIsNef (baseField := 𝕜) (LineBundleClass.mk
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor))) := by
  let : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨fan.structureMap 𝕜 regular⟩
  intro divisor nef basis coneBasis ray
  have actualNef := (schemeLineBundleClassIsNef_mk_iff
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).mp nef
  exact (toricGeometricNefSupportCriterion_proved 𝕜 Lattice Ambient embedding
    fan complete regular divisor).mp actualNef dimension basis coneBasis ray

theorem extremalDropOneIncidence_proved
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : ToricSchemeIsProjective 𝕜 fan regular) :
    ToricExtremalDropOneConeIncidence fan
      (fun _left _right relation => relation.IsMoriExtremal 𝕜 complete regular) := by
  intro left right relation extremal distinguished
  have emptyCone : fan.finiteRayHull ∅ ∈ fan.cones := by
    rw [fan.finiteRayHull_empty]
    obtain ⟨cone, member⟩ := fan.completeFan_nonemptyCones complete
    exact fan.bot_mem member
  have incidence := reidExtremalPrimitiveConeIncidence_proved 𝕜 Lattice Ambient embedding
    fan complete regular projective left right relation extremal ∅
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) emptyCone
    (by simpa using relation.right_cone) distinguished
  simpa only [TauCeti.Toric.Fan.PrimitiveLatticeRelation.DropOneConeIncidence,
    Finset.union_empty] using incidence

end BondalThomsen
