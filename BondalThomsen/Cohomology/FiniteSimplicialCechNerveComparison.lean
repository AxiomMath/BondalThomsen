module

public import BondalThomsen.Toric.Cohomology.NegativeSupportRelativeCohomology
public import BondalThomsen.Toric.Cohomology.CechNegativeSupportComparison
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryCechNonvanishing
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.Functor

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open BondalThomsen.ToricNefCechAcyclicity
open scoped Classical Simplicial

namespace BondalThomsen.FiniteSimplicialCechNerveComparison

variable {Row Column : Type}

structure IncidenceRectangle (relation : Row → Column → Prop) (rowDegree columnDegree : ℕ) where
  rows : Fin (rowDegree + 1) → Row
  columns : Fin (columnDegree + 1) → Column
  incident : ∀ row column, relation (rows row) (columns column)

local instance alternatingCofacePreservesZeroMorphisms :
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).PreservesZeroMorphisms where
  map_zero _source _target := by
    apply HomologicalComplex.Hom.ext
    funext degree
    rfl

local instance alternatingCofaceAdditive :
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).Additive where
  map_add := by
    intro source target first second
    ext degree cochain
    rfl

end BondalThomsen.FiniteSimplicialCechNerveComparison
