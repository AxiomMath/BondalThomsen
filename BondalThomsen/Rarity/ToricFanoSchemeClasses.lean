module

public import BondalThomsen.ProjectiveBundle.CanonicalFano
public import BondalThomsen.Rarity.DeepFanUnconditionalCounting
public import BondalThomsen.Rarity.DeepFanTreeSchemeCounting
public import BondalThomsen.ProjectiveBundle.SchemeAsymptoticLower
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Collection.SectionThree.Equivalences
public import BondalThomsen.Toric.Cohomology.PrimitivePairCohomology
public import BondalThomsen.Toric.Frobenius.FrobeniusRemainingSteps
public import BondalThomsen.Cohomology.FiniteAffineCoverQuasicoherentExtensions
public import BondalThomsen.Toric.Frobenius.MultiplicationGlobalResidueIso
public import BondalThomsen.DeepFan.PrimitiveCoefficientCriterion
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryDerivedCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Filter Real
open BondalThomsen.ProjectiveBundle
open scoped Topology

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BondalThomsen

structure SmoothProjectiveToricFanoPresentation (dimension : ℕ) where
  Lattice : Type
  [latticeGroup : AddCommGroup Lattice]
  Ambient : Type
  [ambientGroup : NormedAddCommGroup Ambient]
  [ambientSpace : NormedSpace ℝ Ambient]
  [ambientFinite : FiniteDimensional ℝ Ambient]
  embedding : Lattice →+ Ambient
  fan : TauCeti.Toric.Fan embedding
  complete : fan.IsComplete
  regular : fan.IsRegular
  smooth : SmoothOfRelativeDimension dimension (fan.structureMap 𝕜 regular)
  projective : ∃ Index : Type, Finite Index ∧
    ∃ closedMap : fan.algebraicRealization 𝕜 regular ⟶
        Proj (MvPolynomial.homogeneousSubmodule Index 𝕜),
      IsClosedImmersion closedMap ∧ closedMap ≫ polynomialProjStructureMap 𝕜 Index =
        fan.structureMap 𝕜 regular
  inverseCanonicalAmple :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹)

attribute [instance] SmoothProjectiveToricFanoPresentation.latticeGroup
  SmoothProjectiveToricFanoPresentation.ambientGroup
  SmoothProjectiveToricFanoPresentation.ambientSpace
  SmoothProjectiveToricFanoPresentation.ambientFinite

end BondalThomsen
