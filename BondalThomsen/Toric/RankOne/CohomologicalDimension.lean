module

public import BondalThomsen.Toric.RankOne.PicardCohomology
public import BondalThomsen.Cohomology.FiniteAffineCechCohomology

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.ToricRankOneNefVanishing

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in
theorem rankOne_basisHull_eq_positive_or_negative
    (basis : Basis (Fin 1) ℤ Lattice) {dimension : ℕ}
    (otherBasis : Basis (Fin dimension) ℤ Lattice) :
    PointedCone.hull ℝ (Set.range (fun index => embedding (otherBasis index))) =
        PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∨
      PointedCone.hull ℝ (Set.range (fun index => embedding (otherBasis index))) =
        PointedCone.hull ℝ (Set.range (fun index => embedding (rankOneNegativeBasis basis index))) := by
  have dimensionOne : dimension = 1 := by
    have rank := (Module.finrank_eq_card_basis otherBasis).symm.trans
      (Module.finrank_eq_card_basis basis)
    simpa only [Fintype.card_fin] using rank
  subst dimension
  rcases primitive_eq_signed_rankOne_basis basis (otherBasis 0)
    (otherBasis.isPrimitive 0) with positive | negative
  · left
    have same : otherBasis = basis := by
      ext index
      have indexZero : index = 0 := Subsingleton.elim _ _
      simpa only [indexZero] using positive
    rw [same]
  · right
    have same : otherBasis = rankOneNegativeBasis basis := by
      ext index
      have indexZero : index = 0 := Subsingleton.elim _ _
      simpa only [indexZero, rankOneNegativeBasis_apply] using negative
    rw [same]

end TauCeti.Toric.Fan
