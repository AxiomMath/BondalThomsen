module

public import BondalThomsen.ProjectiveBundle.CanonicalFano
public import BondalThomsen.LineBundle.GlobalGenerationGeometricNef
public import BondalThomsen.Toric.Divisor.PicardEquivalence
public import BondalThomsen.ProjectiveBundle.Scheme
public import BondalThomsen.ProjectiveBundle.NefSupport
public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Toric.Positivity.GlobalGenerationCriterion
public import BondalThomsen.Toric.Cohomology.NefFirstCohomologyVanishing
public import BondalThomsen.ProjectiveBundle.DivisorClasses
public import BondalThomsen.FloorClasses.FloorClassFiniteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.NhdsWithin
public import BondalThomsen.Toric.RankOne.GeometricNefCriterion
public import BondalThomsen.Toric.RankOne.NefVanishing
public import BondalThomsen.Toric.Divisor.DivisorExtCohomology
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Toric.RankOne.BondalThomsenClassification
public import BondalThomsen.Toric.Surface.GeometricNefSupport
public import BondalThomsen.LineBundle.PicardGeometricNef
public import BondalThomsen.Toric.Positivity.SemiampleClassCriterion
public import BondalThomsen.DeepFan.CriterionConverse

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry
open BondalThomsen.ProjectiveBundle
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace BondalThomsen.Examples

abbrev projectiveLineFan := fan (baseDimension := 1) (0 : Matrix (Fin 0) (Fin 1) ℤ)

abbrev projectiveLineScheme : Scheme :=
  scheme 𝕜 (baseDimension := 1) (0 : Matrix (Fin 0) (Fin 1) ℤ)

abbrev projectiveLineStructureMap : projectiveLineScheme 𝕜 ⟶ Spec (CommRingCat.of 𝕜) :=
  schemeStructureMap 𝕜 (baseDimension := 1) (0 : Matrix (Fin 0) (Fin 1) ℤ)

theorem projectiveLineFan_complete_regular :
    projectiveLineFan.IsComplete ∧ projectiveLineFan.IsRegular :=
  ⟨fan_isComplete _, fan_isRegular _⟩

variable {𝕜} in
instance projectiveLineScheme_integral : IsIntegral (projectiveLineScheme 𝕜) :=
  scheme_isIntegral 𝕜 _

variable {𝕜} in
instance projectiveLineRealization_integral :
    IsIntegral (projectiveLineFan.algebraicRealization 𝕜 projectiveLineFan_complete_regular.2) :=
  projectiveLineFan.algebraicRealization_isIntegral 𝕜 projectiveLineFan_complete_regular.2
    (projectiveLineFan.completeFan_nonemptyCones projectiveLineFan_complete_regular.1)

instance projectiveLineFan_nonemptyCones : Nonempty projectiveLineFan.cones :=
  projectiveLineFan.completeFan_nonemptyCones projectiveLineFan_complete_regular.1

variable {𝕜} in
instance projectiveLineScheme_over : (projectiveLineScheme 𝕜).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨projectiveLineStructureMap 𝕜⟩

theorem projectiveLine_strict_anticanonical_support :
    projectiveLineFan.HasStrictAnticanonicalConeSupport :=
  hasStrictAnticanonicalConeSupport_of_row_bounds _ (by decide) (by decide)
    (by simp) (by simp)

theorem projectiveLineScheme_projective :
    ∃ Index : Type, Finite Index ∧
      ∃ closedMap : projectiveLineScheme 𝕜 ⟶ Proj (MvPolynomial.homogeneousSubmodule Index 𝕜),
        IsClosedImmersion closedMap ∧
          closedMap ≫ polynomialProjStructureMap 𝕜 Index = projectiveLineStructureMap 𝕜 :=
  scheme_projectiveClosedEmbedding_of_strictAnticanonicalSupport 𝕜
    (baseDimension := 1) (0 : Matrix (Fin 0) (Fin 1) ℤ)
    projectiveLine_strict_anticanonical_support

theorem projectiveLine_anticanonical_isAmple :
    IsAmple (projectiveLineFan.invariantDivisorLineBundle 𝕜
      projectiveLineFan_complete_regular.1 projectiveLineFan_complete_regular.2
      projectiveLineFan.anticanonicalRayDivisor).obj := by
  apply projectiveLineFan.divisorLineBundle_isAmple_of_strictSupport 𝕜
    projectiveLineFan_complete_regular.1 projectiveLineFan_complete_regular.2
  intro dimension basis coneBasis ray outside
  simpa only [projectiveLineFan.anticanonicalRayDivisor_apply,
    projectiveLineFan.coneDivisorCharacter_anticanonical] using
    projectiveLine_strict_anticanonical_support dimension basis coneBasis ray outside

theorem projectiveLine_inverseCanonical_isAmple :
    SchemeLineBundleClassAmple ((projectiveLineFan.toricCanonicalLineBundleClass 𝕜
      projectiveLineFan_complete_regular.1 projectiveLineFan_complete_regular.2)⁻¹) :=
  (projectiveLineFan.toricCanonicalInverseClass_isAmple_iff_raySum 𝕜
    projectiveLineFan_complete_regular.1 projectiveLineFan_complete_regular.2).mpr
      (projectiveLine_anticanonical_isAmple 𝕜)

end BondalThomsen.Examples
