module

public import BondalThomsen.Rarity.DeepIntegralFanClassCounting
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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set Filter Real
open BondalThomsen.ToricTransport
open scoped Classical Topology

namespace BondalThomsen

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

namespace ProjectiveBundle

def parameterIntegralFanClasses (dimension : ℕ) :
    Set (IntegralFanClass
      (latticeEmbedding (familyRows dimension) (familyWeight dimension) (familyColumns dimension))) :=
  Set.range (fun matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
    (familyWeight dimension) => integralFanClass (parameterFan dimension matrix))

theorem parameterIntegralFanClasses_finite (dimension : ℕ) :
    (parameterIntegralFanClasses dimension).Finite := Set.finite_range _

end ProjectiveBundle

end BondalThomsen
