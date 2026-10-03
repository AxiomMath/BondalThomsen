module

public import BondalThomsen.Cohomology.FiniteSimplicialCechNerveTotalComparison
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import BondalThomsen.Toric.Cohomology.FanNegativeSupportCohomology

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

open CategoryTheory CategoryTheory.Limits
open BondalThomsen.FiniteSimplicialCechNerveComparison
open BondalThomsen.FiniteSimplicialCechNerveTotalComparison

open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.FiniteSimplicialCechNerveAllDegreeHomology

attribute [local instance] nonnegativeCochainTensorSigns nonnegativeTotalSymmetry

variable {Row Column : Type}

theorem negativeComplex_homology_isZero_of_no_incidence
    (relation : Row → Column → Prop) (negative : Row → Prop)
    (emptyIncidence : ∀ row column, negative row → ¬relation row column) (degree : ℕ) :
    IsZero ((negativeComplex 𝕜 relation negative).homology degree) := by
  have degreeZero : IsZero ((negativeComplex 𝕜 relation negative).X degree) := by
    have : IsEmpty (forbiddenTuple relation negative degree) := ⟨fun tuple => by
      obtain ⟨row, negativeRow, incident⟩ := tuple.property
      exact emptyIncidence row (tuple.val 0) negativeRow (incident 0)⟩
    have : Subsingleton ((negativeComplex 𝕜 relation negative).X degree) := by
      change Subsingleton (forbiddenTuple relation negative degree → 𝕜)
      infer_instance
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact (HomologicalComplex.ExactAt.of_isZero degreeZero).isZero_homology

end BondalThomsen.FiniteSimplicialCechNerveAllDegreeHomology

