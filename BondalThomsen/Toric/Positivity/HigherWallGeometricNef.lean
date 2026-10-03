module

public import BondalThomsen.Toric.Positivity.HigherWallLocalConcavity
public import BondalThomsen.Toric.Positivity.HigherWallIteratedStar

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Set BondalThomsen
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance higherWallRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

variable {𝕜} in
local instance higherWallBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

theorem wallRestrictionInvariantDivisor_isNef_of_isNef
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray)
    (reference : (fan.star ray).cones)
    (nef : AlgebraicGeometry.IsNef (baseField := 𝕜)
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) :
    AlgebraicGeometry.IsNef (baseField := 𝕜)
      ((fan.star ray).invariantDivisorLineBundle 𝕜
        (fan.star_isComplete_of_isComplete complete ray)
        (fan.star_isRegular complete regular ray)
        (fan.wallRestrictionInvariantDivisor complete regular divisor ray reference)).obj := by
  exact AlgebraicGeometry.IsNef.of_iso
    (fan.wallRestrictionLineBundleIsoInvariantDivisor 𝕜 complete regular divisor ray reference)
    (fan.surfaceWallQuotient_isNef_of_isNef 𝕜 complete regular divisor ray reference nef)

def higherWallQuotientBasis (fan : Fan embedding) {dimension quotientDimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray)
    (contracted : Fin dimension) (equality : basis contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension) :
    Basis (Fin quotientDimension) ℤ (fan.StarLattice ray) :=
  (basisVectorQuotient basis contracted ray.val equality).reindex indices

omit [FiniteDimensional ℝ Ambient] in
@[simp] theorem higherWallQuotientBasis_apply (fan : Fan embedding)
    {dimension quotientDimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) (contracted : Fin dimension) (equality : basis contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension)
    (index : Fin quotientDimension) :
    fan.higherWallQuotientBasis basis ray contracted equality indices index =
      (Submodule.span ℤ {ray.val}).mkQ (basis (indices.symm index).val) := by
  simp only [higherWallQuotientBasis, Basis.reindex_apply, basisVectorQuotient_apply]

omit [FiniteDimensional ℝ Ambient] in
@[simp] theorem higherWallQuotientBasis_repr_mkQ (fan : Fan embedding)
    {dimension quotientDimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) (contracted : Fin dimension) (equality : basis contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension)
    (vector : Lattice) (index : Fin quotientDimension) :
    (fan.higherWallQuotientBasis basis ray contracted equality indices).repr
      ((Submodule.span ℤ {ray.val}).mkQ vector) index =
        basis.repr vector (indices.symm index).val := by
  simp only [higherWallQuotientBasis, Basis.repr_reindex_apply, basisVectorQuotient_repr]

omit [FiniteDimensional ℝ Ambient] in
theorem higherWallQuotientBasis_hull (fan : Fan embedding)
    {dimension quotientDimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) (contracted : Fin dimension) (equality : basis contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension) :
    PointedCone.hull ℝ (Set.range (fun index => fan.starEmbedding ray
      (fan.higherWallQuotientBasis basis ray contracted equality indices index))) =
        PointedCone.map (fan.starProjection ray)
          (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) := by
  rw [fan.starConeBasis_eq_hull basis ray contracted equality]
  congr 1
  ext vector
  constructor
  · rintro ⟨index, rfl⟩
    exact ⟨indices.symm index, by
      simp only [higherWallQuotientBasis, Basis.reindex_apply]⟩
  · rintro ⟨index, rfl⟩
    refine ⟨indices index, ?_⟩
    simp only [higherWallQuotientBasis, Basis.reindex_apply, Equiv.symm_apply_apply]

omit [FiniteDimensional ℝ Ambient] in
theorem higherWallQuotientBasis_isConeBasis (fan : Fan embedding)
    {dimension quotientDimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (ray : fan.Ray)
    (contracted : Fin dimension) (equality : basis contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension) :
    (fan.star ray).IsConeBasis
      (fan.higherWallQuotientBasis basis ray contracted equality indices) := by
  change PointedCone.hull ℝ (Set.range (fun index => fan.starEmbedding ray
    (fan.higherWallQuotientBasis basis ray contracted equality indices index))) ∈
      (fan.star ray).cones
  rw [fan.higherWallQuotientBasis_hull]
  exact ⟨_, ⟨cone_basis, by
    rw [← equality]
    exact PointedCone.subset_hull ⟨contracted, rfl⟩⟩, rfl⟩

theorem wallRestrictionQuotientConeCharacter_eq (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension quotientDimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (ray : fan.Ray) (contracted : Fin dimension) (equality : basis contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension)
    (reference : (fan.star ray).cones) :
    (fan.star ray).coneDivisorCharacter
        (fan.higherWallQuotientBasis basis ray contracted equality indices)
        (fan.higherWallQuotientBasis_isConeBasis basis cone_basis ray contracted equality indices)
        (fan.wallRestrictionInvariantDivisor complete regular divisor ray reference) =
      fan.wallRestrictionQuotientCharacter complete regular divisor ray reference
        (fan.wallDescentProjectedCone ray ⟨_, cone_basis⟩
          (by rw [← equality]; exact PointedCone.subset_hull ⟨contracted, rfl⟩)) := by
  let quotientBasis := fan.higherWallQuotientBasis basis ray contracted equality indices
  let quotientCone := fan.higherWallQuotientBasis_isConeBasis
    basis cone_basis ray contracted equality indices
  let projected := fan.wallDescentProjectedCone ray ⟨_, cone_basis⟩
    (by rw [← equality]; exact PointedCone.subset_hull ⟨contracted, rfl⟩)
  apply AddMonoidHom.toIntLinearMap_injective
  apply quotientBasis.ext
  intro index
  change (fan.star ray).coneDivisorCharacter quotientBasis quotientCone
      (fan.wallRestrictionInvariantDivisor complete regular divisor ray reference)
      (quotientBasis index) =
    fan.wallRestrictionQuotientCharacter complete regular divisor ray reference projected
      (quotientBasis index)
  rw [(fan.star ray).coneDivisorCharacter_basis]
  rw [fan.wallRestrictionInvariantDivisor_apply complete regular divisor ray reference projected]
  · simp only [neg_neg]
    rfl
  · apply (fan.wallRestrictionQuotientCone_above complete regular ray projected).le
    change fan.starEmbedding ray (quotientBasis index) ∈ projected.val
    dsimp only [projected, wallDescentProjectedCone]
    rw [← fan.higherWallQuotientBasis_hull basis ray contracted equality indices]
    exact PointedCone.subset_hull ⟨index, rfl⟩

theorem wallRestrictionQuotientConeCharacter_mkQ (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension quotientDimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (ray : fan.Ray) (contracted : Fin dimension) (equality : basis contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension)
    (reference : (fan.star ray).cones) (vector : Lattice) :
    (fan.star ray).coneDivisorCharacter
        (fan.higherWallQuotientBasis basis ray contracted equality indices)
        (fan.higherWallQuotientBasis_isConeBasis basis cone_basis ray contracted equality indices)
        (fan.wallRestrictionInvariantDivisor complete regular divisor ray reference)
        ((Submodule.span ℤ {ray.val}).mkQ vector) =
      fan.coneDivisorCharacter basis cone_basis divisor vector -
        fan.wallRestrictionSourceCharacter complete regular divisor ray reference vector := by
  rw [fan.wallRestrictionQuotientConeCharacter_eq complete regular basis cone_basis divisor
    ray contracted equality indices reference]
  rw [fan.wallRestrictionQuotientCharacter_mkQ]
  rw [fan.wallRestrictionSourceCharacter_eq_coneCharacter complete regular basis cone_basis
    divisor ray contracted equality]

theorem adjacentCartierGap_eq_quotientCartierGap (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension quotientDimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray) (contracted : Fin dimension)
    (basis_equality : basis contracted = ray.val)
    (adjacent_equality : adjacent contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension)
    (reference : (fan.star ray).cones) (removed : Fin quotientDimension) :
    let quotientBasis := fan.higherWallQuotientBasis basis ray contracted basis_equality indices
    let quotientAdjacent := fan.higherWallQuotientBasis adjacent ray contracted adjacent_equality indices
    let quotientCone := fan.higherWallQuotientBasis_isConeBasis
      basis cone_basis ray contracted basis_equality indices
    let quotientAdjacentCone := fan.higherWallQuotientBasis_isConeBasis
      adjacent adjacent_cone ray contracted adjacent_equality indices
    let quotientDivisor := fan.wallRestrictionInvariantDivisor complete regular divisor ray reference
    (fan.star ray).coneDivisorCharacter quotientAdjacent quotientAdjacentCone quotientDivisor
        (quotientBasis removed) +
      quotientDivisor ((fan.star ray).basisRay quotientBasis quotientCone removed) =
        fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis (indices.symm removed).val) +
          divisor (fan.basisRay basis cone_basis (indices.symm removed).val) := by
  dsimp only
  have coefficient := (fan.star ray).coneDivisorCharacter_basis
    (fan.higherWallQuotientBasis basis ray contracted basis_equality indices)
    (fan.higherWallQuotientBasis_isConeBasis basis cone_basis ray contracted basis_equality indices)
    (fan.wallRestrictionInvariantDivisor complete regular divisor ray reference) removed
  have coefficient_eq := congrArg Neg.neg coefficient
  simp only [neg_neg] at coefficient_eq
  rw [← coefficient_eq]
  rw [fan.higherWallQuotientBasis_apply]
  rw [fan.wallRestrictionQuotientConeCharacter_mkQ complete regular adjacent adjacent_cone
    divisor ray contracted adjacent_equality indices reference]
  rw [fan.wallRestrictionQuotientConeCharacter_mkQ complete regular basis cone_basis
    divisor ray contracted basis_equality indices reference]
  rw [fan.coneDivisorCharacter_basis]
  omega

theorem adjacentCartierGap_nonnegative_of_isNef
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (adjacent_cone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (divisor : fan.InvariantRayDivisor)
    (nef : AlgebraicGeometry.IsNef (baseField := 𝕜)
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) :
    0 ≤ fan.coneDivisorCharacter adjacent adjacent_cone divisor (basis removed) +
      divisor (fan.basisRay basis cone_basis removed) := by
  classical
  induction dimension using Nat.strong_induction_on generalizing Lattice Ambient with
  | h dimension inductionHypothesis =>
    by_cases rankOne : dimension = 1
    · subst dimension
      exact fan.hasAdjacentWallCartierInequalities_of_raySupport divisor
        ((fan.rankOneInvariantDivisor_isNef_iff_support 𝕜 complete regular basis divisor).mp nef)
        1 basis adjacent cone_basis adjacent_cone removed shared opposite
    · have dimensionPositive : 0 < dimension := Nat.zero_lt_of_lt removed.isLt
      have dimensionLarge : 1 < dimension := by omega
      obtain ⟨contracted, distinct⟩ : ∃ contracted : Fin dimension, contracted ≠ removed := by
        let zeroIndex : Fin dimension := ⟨0, dimensionPositive⟩
        by_cases zero : removed = zeroIndex
        · refine ⟨⟨1, dimensionLarge⟩, ?_⟩
          intro equal
          have values := congrArg Fin.val (equal.trans zero)
          change 1 = 0 at values
          omega
        · exact ⟨zeroIndex, Ne.symm zero⟩
      let ray := fan.basisRay basis cone_basis contracted
      let quotientIndex := {index : Fin dimension // index ≠ contracted}
      let indices := Fintype.equivFin quotientIndex
      let quotientBasis := fan.higherWallQuotientBasis basis ray contracted rfl indices
      let adjacentEquality : adjacent contracted = ray.val := shared contracted distinct
      let quotientAdjacent := fan.higherWallQuotientBasis adjacent ray contracted adjacentEquality indices
      let quotientCone := fan.higherWallQuotientBasis_isConeBasis
        basis cone_basis ray contracted rfl indices
      let quotientAdjacentCone := fan.higherWallQuotientBasis_isConeBasis
        adjacent adjacent_cone ray contracted adjacentEquality indices
      let reference := fan.wallDescentProjectedCone ray ⟨_, cone_basis⟩
        (PointedCone.subset_hull ⟨contracted, rfl⟩)
      let quotientDivisor := fan.wallRestrictionInvariantDivisor complete regular divisor ray reference
      let quotientRemoved := indices ⟨removed, Ne.symm distinct⟩
      have quotientRemoved_lift : (indices.symm quotientRemoved).val = removed :=
        congrArg Subtype.val (indices.symm_apply_apply ⟨removed, Ne.symm distinct⟩)
      have smaller : Fintype.card quotientIndex < dimension := by
        have card := Fintype.card_subtype_compl (fun index : Fin dimension => index = contracted)
        simp only [Fintype.card_fin, Fintype.card_unique] at card
        change Fintype.card {index : Fin dimension // ¬index = contracted} < dimension
        rw [card]
        omega
      have quotientShared : ∀ index, index ≠ quotientRemoved →
          quotientAdjacent index = quotientBasis index := by
        intro index different
        have originalDifferent : (indices.symm index).val ≠ removed := by
          intro equal
          apply different
          have same : indices.symm index = ⟨removed, Ne.symm distinct⟩ := Subtype.ext equal
          exact (indices.apply_symm_apply index).symm.trans (congrArg indices same)
        dsimp only [quotientAdjacent, quotientBasis]
        rw [fan.higherWallQuotientBasis_apply, fan.higherWallQuotientBasis_apply]
        rw [shared _ originalDifferent]
      have quotientOpposite : quotientBasis.repr (quotientAdjacent quotientRemoved)
          quotientRemoved = -1 := by
        dsimp only [quotientBasis, quotientAdjacent]
        rw [fan.higherWallQuotientBasis_apply, fan.higherWallQuotientBasis_repr_mkQ]
        rw [quotientRemoved_lift]
        exact opposite
      have bound := inductionHypothesis (Fintype.card quotientIndex) smaller
        (fan.star ray) (fan.star_isComplete_of_isComplete complete ray)
        (fan.star_isRegular complete regular ray) quotientBasis quotientAdjacent
        quotientCone quotientAdjacentCone quotientRemoved quotientShared quotientOpposite
        quotientDivisor
        (fan.wallRestrictionInvariantDivisor_isNef_of_isNef 𝕜 complete regular divisor ray reference nef)
      have gap := fan.adjacentCartierGap_eq_quotientCartierGap complete regular basis adjacent
        cone_basis adjacent_cone divisor ray contracted rfl adjacentEquality indices reference
        quotientRemoved
      change 0 ≤ _ at bound
      rw [gap] at bound
      change 0 ≤ fan.coneDivisorCharacter adjacent adjacent_cone divisor
        (basis (indices.symm quotientRemoved).val) +
          divisor (fan.basisRay basis cone_basis (indices.symm quotientRemoved).val) at bound
      rw [quotientRemoved_lift] at bound
      exact bound

theorem hasAdjacentWallCartierInequalities_of_isNef
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (nef : AlgebraicGeometry.IsNef (baseField := 𝕜)
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) :
    fan.HasAdjacentWallCartierInequalities divisor := by
  intro dimension basis adjacent cone_basis adjacent_cone removed shared opposite
  exact fan.adjacentCartierGap_nonnegative_of_isNef 𝕜 complete regular basis adjacent
    cone_basis adjacent_cone removed shared opposite divisor nef

end TauCeti.Toric.Fan
