module

public import BondalThomsen.Toric.Positivity.PrescribedWallStarTower
public import BondalThomsen.Toric.Positivity.HigherWallGeometricNef
public import BondalThomsen.Fan.MoriCone
public import BondalThomsen.Examples.ProjectiveSpaces

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
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

local instance numericalWallRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

variable {𝕜} in
local instance numericalWallBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def adjacentBasisWallCone {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (removed : Fin dimension) : PointedCone ℝ Ambient :=
  prescribedBasisCone (embedding := embedding) basis (Finset.univ.erase removed)

omit [FiniteDimensional ℝ Ambient] in
theorem adjacentBasisWallCone_ray_index (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis)
    (removed : Fin dimension) (ray : fan.Ray)
    (contains : embedding ray.val ∈ adjacentBasisWallCone (embedding := embedding) basis removed) :
    ∃ contracted : Fin dimension, contracted ≠ removed ∧ basis contracted = ray.val := by
  classical
  have fullContains : embedding ray.val ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index))) := by
    apply Submodule.span_mono (s := (fun index => embedding (basis index)) ''
      (↑(Finset.univ.erase removed) : Set (Fin dimension))) _ contains
    rintro _ ⟨index, _, rfl⟩
    exact ⟨index, rfl⟩
  obtain ⟨contracted, equality⟩ := fan.ray_eq_basis_of_mem_coneBasis basis coneBasis ray fullContains
  refine ⟨contracted, ?_, equality⟩
  intro same
  let realBasis := fan.lattice.isBaseChange.basis basis
  have zeroCoordinate : ∀ point ∈ adjacentBasisWallCone (embedding := embedding) basis removed,
      realBasis.repr point removed = 0 := by
    intro point member
    induction member using Submodule.span_induction with
    | mem vector member =>
      obtain ⟨index, member, rfl⟩ := member
      have different := (Finset.mem_erase.mp member).1
      have realEquality : realBasis index = embedding (basis index) :=
        fan.lattice.isBaseChange.basis_apply basis index
      change realBasis.repr (embedding (basis index)) removed = 0
      rw [← realEquality]
      simp [different]
    | zero => simp
    | add first second _ _ firstZero secondZero => simp [firstZero, secondZero]
    | smul scalar vector _ vectorZero =>
      change realBasis.repr ((scalar : ℝ) • vector) removed = 0
      rw [map_smul]
      simp [vectorZero]
  have impossible := zeroCoordinate (embedding ray.val) contains
  have realEquality : realBasis removed = embedding (basis removed) :=
    fan.lattice.isBaseChange.basis_apply basis removed
  rw [← equality, same, ← realEquality] at impossible
  simp at impossible

omit [FiniteDimensional ℝ Ambient] in
theorem adjacentBasisWallCone_projected (fan : Fan embedding)
    {dimension quotientDimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (removed contracted : Fin dimension) (distinct : contracted ≠ removed)
    (ray : fan.Ray) (equality : basis contracted = ray.val)
    (indices : {index : Fin dimension // index ≠ contracted} ≃ Fin quotientDimension) :
    PointedCone.map (fan.starProjection ray)
        (adjacentBasisWallCone (embedding := embedding) basis removed) =
      adjacentBasisWallCone (embedding := fan.starEmbedding ray)
        (fan.higherWallQuotientBasis basis ray contracted equality indices)
        (indices ⟨removed, Ne.symm distinct⟩) := by
  classical
  rw [adjacentBasisWallCone, prescribedBasisCone, pointedCone_map_hull]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨index, member, rfl⟩, rfl⟩
    by_cases same : index = contracted
    · subst index
      have killed : fan.starProjection ray (embedding (basis contracted)) = 0 := by
        rw [equality]
        change (Submodule.span ℝ {embedding ray.val}).mkQ (embedding ray.val) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton _)
      rw [killed]
      exact Submodule.zero_mem _
    · apply PointedCone.subset_hull
      refine ⟨indices ⟨index, same⟩, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
        intro equal
        have original := congrArg (fun quotientIndex => (indices.symm quotientIndex).val) equal
        simp only [Equiv.symm_apply_apply] at original
        exact (Finset.mem_erase.mp member).1 original
      · simp only [higherWallQuotientBasis_apply, Equiv.symm_apply_apply, starEmbedding_mkQ]
  · apply Submodule.span_le.mpr
    rintro _ ⟨index, member, rfl⟩
    dsimp only
    rw [higherWallQuotientBasis_apply, starEmbedding_mkQ]
    apply PointedCone.subset_hull
    refine ⟨embedding (basis (indices.symm index).val), ⟨(indices.symm index).val, ?_, rfl⟩, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
    intro equal
    apply (Finset.mem_erase.mp member).1
    have same : indices.symm index = ⟨removed, Ne.symm distinct⟩ := Subtype.ext equal
    exact (indices.apply_symm_apply index).symm.trans (congrArg indices same)

theorem iteratedStarCurveLineBundleDegree_eq_of_iso (steps : ℕ) (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (chain : RayStarChain steps fan)
    (rankOne : fan.iteratedStarLatticeRank steps chain = 1)
    {first second : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)}
    (comparison : first.obj ≅ second.obj) :
    fan.iteratedStarCurveLineBundleDegree 𝕜 steps complete regular chain rankOne first =
      fan.iteratedStarCurveLineBundleDegree 𝕜 steps complete regular chain rankOne second :=
  (fan.iteratedStarIntegralCurve 𝕜 steps complete regular chain rankOne).lineBundleDegree_eq_of_iso
    ((Scheme.Modules.pullback _).mapIso comparison)

theorem iteratedStarCurveLineBundleDegree_succ (steps : ℕ) (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (chain : RayStarChain (steps + 1) fan)
    (rankOne : fan.iteratedStarLatticeRank (steps + 1) chain = 1)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    fan.iteratedStarCurveLineBundleDegree 𝕜 (steps + 1) complete regular chain rankOne bundle =
      (fan.star chain.1).iteratedStarCurveLineBundleDegree 𝕜 steps
        (fan.star_isComplete_of_isComplete complete chain.1)
        (fan.star_isRegular complete regular chain.1) chain.2 rankOne
        (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular chain.1 bundle) := by
  let := fan.completeStarOrbitClosureMap_isClosedImmersion 𝕜 complete regular chain.1
  let : (fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1).IsOver
      (Spec (CommRingCat.of 𝕜)) :=
    ⟨fan.starOrbitClosureMap_comp_structureMap 𝕜 regular chain.1
      (fan.star_isRegular complete regular chain.1)⟩
  let curve := (fan.star chain.1).iteratedStarIntegralCurve 𝕜 steps
    (fan.star_isComplete_of_isComplete complete chain.1)
    (fan.star_isRegular complete regular chain.1) chain.2 rankOne
  let : IsProper (curve.ι ≫ (fan.star chain.1).structureMap 𝕜
      (fan.star_isRegular complete regular chain.1)) := curve.isProper
  let : IsProper ((curve.ι ≫ fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1) ≫
      fan.structureMap 𝕜 regular) :=
    (curve.mapClosedImmersion (fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)).isProper
  let comparison :
      (Scheme.Modules.pullback curve.ι).obj
          ((Scheme.Modules.pullback (fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)).obj
            bundle.obj) ≅
        (Scheme.Modules.pullback (curve.ι ≫
          fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)).obj bundle.obj :=
    (Scheme.Modules.pullbackComp curve.ι
      (fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)).app bundle.obj
  have degreeEquality := curve.lineBundleDegree_eq_of_iso comparison
  change Intersection.lineBundleDegree
      (curve.ι ≫ (fan.star chain.1).structureMap 𝕜
        (fan.star_isRegular complete regular chain.1)) curve.dim_eq_one.le
      ((Scheme.Modules.pullback curve.ι).obj
        ((Scheme.Modules.pullback (fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)).obj
          bundle.obj)) =
    Intersection.lineBundleDegree
      (curve.ι ≫ (fan.star chain.1).structureMap 𝕜
        (fan.star_isRegular complete regular chain.1)) curve.dim_eq_one.le
      ((Scheme.Modules.pullback (curve.ι ≫
        fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)).obj bundle.obj) at degreeEquality
  change Intersection.lineBundleDegree
      ((curve.ι ≫ fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1) ≫
        fan.structureMap 𝕜 regular) curve.dim_eq_one.le
      ((Scheme.Modules.pullback (curve.ι ≫
        fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)).obj bundle.obj) =
    Intersection.lineBundleDegree
      (curve.ι ≫ (fan.star chain.1).structureMap 𝕜
        (fan.star_isRegular complete regular chain.1)) curve.dim_eq_one.le
      ((Scheme.Modules.pullback curve.ι).obj
        ((Scheme.Modules.pullback (fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1)).obj
          bundle.obj))
  have stepEquality : fan.completeStarOrbitClosureMap 𝕜 complete regular chain.1 ≫
      fan.structureMap 𝕜 regular =
    (fan.star chain.1).structureMap 𝕜 (fan.star_isRegular complete regular chain.1) :=
    fan.starOrbitClosureMap_comp_structureMap 𝕜 regular chain.1
      (fan.star_isRegular complete regular chain.1)
  simpa only [Category.assoc, stepEquality] using degreeEquality.symm

theorem iteratedStarInvariantDivisorDegree_succ (steps : ℕ) (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (chain : RayStarChain (steps + 1) fan)
    (rankOne : fan.iteratedStarLatticeRank (steps + 1) chain = 1)
    (divisor : fan.InvariantRayDivisor) (reference : (fan.star chain.1).cones) :
    fan.iteratedStarCurveLineBundleDegree 𝕜 (steps + 1) complete regular chain rankOne
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) =
      (fan.star chain.1).iteratedStarCurveLineBundleDegree 𝕜 steps
        (fan.star_isComplete_of_isComplete complete chain.1)
        (fan.star_isRegular complete regular chain.1) chain.2 rankOne
        ((fan.star chain.1).invariantDivisorLineBundle 𝕜
          (fan.star_isComplete_of_isComplete complete chain.1)
          (fan.star_isRegular complete regular chain.1)
          (fan.wallRestrictionInvariantDivisor complete regular divisor chain.1 reference)) := by
  rw [fan.iteratedStarCurveLineBundleDegree_succ 𝕜]
  apply iteratedStarCurveLineBundleDegree_eq_of_iso 𝕜
  exact (fan.wallRestrictionGlobalSheafIso 𝕜 complete regular divisor chain.1 reference).symm ≪≫
    fan.wallRestrictionLineBundleIsoInvariantDivisor 𝕜 complete regular divisor chain.1 reference

theorem rankOneInvariantDivisorDegree_eq_adjacentCartierGap (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis adjacent : Basis (Fin 1) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin 1) (opposite : basis.repr (adjacent removed) removed = -1)
    (divisor : fan.InvariantRayDivisor) :
    fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) =
      fan.coneDivisorCharacter adjacent adjacentCone divisor (basis removed) +
        divisor (fan.basisRay basis coneBasis removed) := by
  let : Nonempty fan.cones := fan.completeFan_nonemptyCones complete
  have indexZero : removed = 0 := Subsingleton.elim _ _
  subst removed
  have vectorEquality : adjacent 0 = -basis 0 := by
    rw [← basis.sum_repr (adjacent 0)]
    simp [opposite]
  have characterEquality := fan.coneDivisorCharacter_basis adjacent adjacentCone divisor 0
  rw [vectorEquality, map_neg] at characterEquality
  have positiveEquality : fan.basisRay basis coneBasis 0 =
      fan.rankOnePositiveRay complete regular basis := Subtype.ext rfl
  have negativeEquality : fan.basisRay adjacent adjacentCone 0 =
      fan.rankOneNegativeRay complete regular basis := by
    apply Subtype.ext
    exact vectorEquality.trans (fan.rankOneNegativeRay_val complete regular basis).symm
  rw [fan.rankOneGeometricDivisorDegree_eq_coefficientDegree 𝕜,
    rankOneDivisorCoefficientDegree, positiveEquality]
  rw [negativeEquality] at characterEquality
  omega

theorem iteratedStarInvariantDivisorDegree_eq_adjacentCartierGap (steps : ℕ)
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (chain : RayStarChain steps fan)
    (contracts : fan.RayStarChainContracts steps
      (adjacentBasisWallCone (embedding := embedding) basis removed) chain)
    (rankOne : fan.iteratedStarLatticeRank steps chain = 1)
    (divisor : fan.InvariantRayDivisor) :
    fan.iteratedStarCurveLineBundleDegree 𝕜 steps complete regular chain rankOne
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) =
      fan.coneDivisorCharacter adjacent adjacentCone divisor (basis removed) +
        divisor (fan.basisRay basis coneBasis removed) := by
  classical
  induction steps generalizing Lattice Ambient dimension with
  | zero =>
    let := fan.lattice.free
    let := fan.lattice.finite
    have dimensionOne : dimension = 1 := by
      have rank := Module.finrank_eq_card_basis basis
      simp only [Fintype.card_fin] at rank
      exact rank.symm.trans rankOne
    subst dimension
    let curve := fan.rankOneIntegralCurve 𝕜 complete regular basis
    let bundle := fan.invariantDivisorLineBundle 𝕜 complete regular divisor
    let comparison : (Scheme.Modules.pullback (𝟙 (fan.algebraicRealization 𝕜 regular))).obj
        bundle.obj ≅ bundle.obj :=
      (Scheme.Modules.pullbackId (fan.algebraicRealization 𝕜 regular)).app bundle.obj
    let : SheafOfModules.isInvertible curve.carrier bundle.obj := bundle.property
    have identityDegree := curve.lineBundleDegree_eq_of_iso comparison
    change curve.lineBundleDegree
      ((Scheme.Modules.pullback (𝟙 (fan.algebraicRealization 𝕜 regular))).obj
        bundle.obj) = _
    rw [identityDegree]
    change fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) = _
    exact fan.rankOneInvariantDivisorDegree_eq_adjacentCartierGap 𝕜 complete regular
      basis adjacent coneBasis adjacentCone removed opposite divisor
  | succ steps inductionHypothesis =>
    obtain ⟨contains, smallerContracts⟩ := contracts
    obtain ⟨contracted, distinct, basisEquality⟩ :=
      fan.adjacentBasisWallCone_ray_index basis coneBasis removed chain.1 contains
    let quotientIndex := {index : Fin dimension // index ≠ contracted}
    let indices := Fintype.equivFin quotientIndex
    let quotientBasis := fan.higherWallQuotientBasis basis chain.1 contracted basisEquality indices
    let adjacentEquality : adjacent contracted = chain.1.val :=
      (shared contracted distinct).trans basisEquality
    let quotientAdjacent :=
      fan.higherWallQuotientBasis adjacent chain.1 contracted adjacentEquality indices
    let quotientCone := fan.higherWallQuotientBasis_isConeBasis
      basis coneBasis chain.1 contracted basisEquality indices
    let quotientAdjacentCone := fan.higherWallQuotientBasis_isConeBasis
      adjacent adjacentCone chain.1 contracted adjacentEquality indices
    let reference := fan.wallDescentProjectedCone chain.1 ⟨_, coneBasis⟩ (by
      rw [← basisEquality]
      exact PointedCone.subset_hull ⟨contracted, rfl⟩)
    let quotientDivisor :=
      fan.wallRestrictionInvariantDivisor complete regular divisor chain.1 reference
    let quotientRemoved := indices ⟨removed, Ne.symm distinct⟩
    have quotientRemovedLift : (indices.symm quotientRemoved).val = removed :=
      congrArg Subtype.val (indices.symm_apply_apply ⟨removed, Ne.symm distinct⟩)
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
      rw [quotientRemovedLift]
      exact opposite
    rw [fan.adjacentBasisWallCone_projected basis removed contracted distinct chain.1
      basisEquality indices] at smallerContracts
    rw [fan.iteratedStarInvariantDivisorDegree_succ 𝕜 steps complete regular chain rankOne divisor reference]
    have degreeEquality := inductionHypothesis (fan.star chain.1)
      (fan.star_isComplete_of_isComplete complete chain.1)
      (fan.star_isRegular complete regular chain.1) quotientBasis quotientAdjacent
      quotientCone quotientAdjacentCone quotientRemoved quotientShared quotientOpposite
      chain.2 smallerContracts rankOne quotientDivisor
    rw [degreeEquality]
    have gapEquality := fan.adjacentCartierGap_eq_quotientCartierGap complete regular
      basis adjacent coneBasis adjacentCone divisor chain.1 contracted basisEquality
      adjacentEquality indices reference quotientRemoved
    dsimp only at gapEquality
    rw [quotientRemovedLift] at gapEquality
    exact gapEquality

theorem prescribedWallInvariantDivisorDegree_eq_adjacentCartierGap
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (wall : fan.cones)
    (wallEquality : wall.val = adjacentBasisWallCone (embedding := embedding) basis removed)
    (codimensionOne : Module.finrank ℝ (Submodule.span ℝ (wall.val : Set Ambient)) + 1 =
      Module.finrank ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    fan.prescribedWallLineBundleDegree 𝕜 complete regular wall codimensionOne
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) =
      fan.coneDivisorCharacter adjacent adjacentCone divisor (basis removed) +
        divisor (fan.basisRay basis coneBasis removed) := by
  apply fan.iteratedStarInvariantDivisorDegree_eq_adjacentCartierGap 𝕜 _ complete regular
    basis adjacent coneBasis adjacentCone removed shared opposite
  simpa only [← wallEquality] using fan.prescribedWallChain_contracts complete regular wall

theorem prescribedWallIntegralCurvePicardDegree_eq_adjacentCartierGap
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (basis adjacent : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (adjacentCone : fan.IsConeBasis adjacent)
    (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (wall : fan.cones)
    (wallEquality : wall.val = adjacentBasisWallCone (embedding := embedding) basis removed)
    (codimensionOne : Module.finrank ℝ (Submodule.span ℝ (wall.val : Set Ambient)) + 1 =
      Module.finrank ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    BondalThomsen.integralCurvePicardDegree
        (fan.prescribedWallIntegralCurve 𝕜 complete regular wall codimensionOne)
        (Additive.ofMul (LineBundleClass.mk
          (fan.invariantDivisorLineBundle 𝕜 complete regular divisor))) =
      fan.coneDivisorCharacter adjacent adjacentCone divisor (basis removed) +
        divisor (fan.basisRay basis coneBasis removed) := by
  rw [BondalThomsen.integralCurvePicardDegree_mk]
  exact fan.prescribedWallInvariantDivisorDegree_eq_adjacentCartierGap 𝕜 complete regular
    basis adjacent coneBasis adjacentCone removed shared opposite wall wallEquality codimensionOne divisor

end TauCeti.Toric.Fan
