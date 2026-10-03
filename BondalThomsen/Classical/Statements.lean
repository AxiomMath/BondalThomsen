module

public import BondalThomsen.Fan.MoriCone
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
public import BondalThomsen.Rarity.ToricFanoSchemeClasses

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Classical
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BondalThomsen

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def ToricSchemeIsProjective (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) : Prop :=
  ∃ Index : Type, Finite Index ∧
    ∃ closedMap : fan.algebraicRealization 𝕜 regular ⟶
        Proj (MvPolynomial.homogeneousSubmodule Index 𝕜),
      IsClosedImmersion closedMap ∧ closedMap ≫ polynomialProjStructureMap 𝕜 Index =
        fan.structureMap 𝕜 regular

def ToricNefMoriCriterion : Prop :=
  ∀ (Lattice Ambient : Type) [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] (embedding : Lattice →+ Ambient)
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular), ToricSchemeIsProjective 𝕜 fan regular →
    letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
      ⟨fan.structureMap 𝕜 regular⟩
    ∀ divisorClass : fan.InvariantRayDivisorClass,
      SchemeLineBundleClassIsNef (baseField := 𝕜)
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass)) ↔
      ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
        relation.IsMoriExtremal 𝕜 complete regular → 0 ≤ relation.classPairing divisorClass

def ToricGeometricNefSupportCriterion : Prop :=
  ∀ (Lattice Ambient : Type) [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] (embedding : Lattice →+ Ambient)
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular),
    letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
      ⟨fan.structureMap 𝕜 regular⟩
    ∀ divisor : fan.InvariantRayDivisor,
      AlgebraicGeometry.IsNef (baseField := 𝕜)
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ↔
      fan.HasRaySupportInequalities divisor

def ReidExtremalPrimitiveConeIncidence : Prop :=
  ∀ (Lattice Ambient : Type) [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] (embedding : Lattice →+ Ambient)
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular), ToricSchemeIsProjective 𝕜 fan regular →
    ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      relation.IsMoriExtremal 𝕜 complete regular →
      ∀ extra : Finset fan.Ray, Disjoint extra left → Disjoint extra right →
        fan.finiteRayHull extra ∈ fan.cones →
        fan.finiteRayHull (right ∪ extra) ∈ fan.cones →
        ∀ distinguished : left,
          fan.finiteRayHull (left.erase distinguished.val ∪ right ∪ extra) ∈ fan.cones

end BondalThomsen
