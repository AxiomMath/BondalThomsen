module

public import BondalThomsen.Toric.Positivity.HigherWallIteratedStar
public import BondalThomsen.Fan.ConeBasisFaces

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module TopologicalSpace Set BondalThomsen
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient Index : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}
    [Fintype Index] [DecidableEq Index]

local instance prescribedStarRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

variable {𝕜} in
local instance prescribedStarBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def prescribedBasisCone (basis : Basis Index ℤ Lattice) (selected : Finset Index) :
    PointedCone ℝ Ambient :=
  PointedCone.hull ℝ ((fun index => embedding (basis index)) '' (selected : Set Index))

omit [FiniteDimensional ℝ Ambient] [Fintype Index] [DecidableEq Index] in
theorem prescribedBasisCone_mem (fan : Fan embedding) (basis : Basis Index ℤ Lattice)
    (fullMember : PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones)
    (selected : Finset Index) : prescribedBasisCone (embedding := embedding) basis selected ∈ fan.cones := by
  let realBasis := fan.lattice.isBaseChange.basis basis
  have fullEquality : PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) =
      PointedCone.hull ℝ (Set.range realBasis) := by
    congr 2
    funext index
    exact (fan.lattice.isBaseChange.basis_apply basis index).symm
  have face := basisSubsetCone_isFaceOf realBasis
    ((fun index => embedding (basis index)) '' (selected : Set Index)) (by
      rintro _ ⟨index, _, rfl⟩
      exact ⟨index, fan.lattice.isBaseChange.basis_apply basis index⟩)
  rw [← fullEquality] at face
  exact fan.mem_of_isFaceOf fullMember face

def prescribedBasisRay (fan : Fan embedding) (basis : Basis Index ℤ Lattice)
    (fullMember : PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones)
    (removed : Index) : fan.Ray :=
  ⟨basis removed, basis.isPrimitive removed, by
    simpa only [prescribedBasisCone, Finset.coe_singleton, Set.image_singleton] using
      fan.prescribedBasisCone_mem basis fullMember {removed}⟩

omit [FiniteDimensional ℝ Ambient] [Fintype Index] [DecidableEq Index] in
theorem prescribedBasisRay_mem (fan : Fan embedding) (basis : Basis Index ℤ Lattice)
    (fullMember : PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones)
    (selected : Finset Index) (removed : Index) (member : removed ∈ selected) :
    embedding (fan.prescribedBasisRay basis fullMember removed).val ∈
      prescribedBasisCone (embedding := embedding) basis selected :=
  PointedCone.subset_hull ⟨removed, member, rfl⟩

omit [FiniteDimensional ℝ Ambient] [Fintype Index] in

theorem prescribedBasisCone_projected (fan : Fan embedding) (basis : Basis Index ℤ Lattice)
    (fullMember : PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones)
    (selected : Finset Index) (removed : Index) :
    let ray := fan.prescribedBasisRay basis fullMember removed
    PointedCone.map (fan.starProjection ray)
        (prescribedBasisCone (embedding := embedding) basis selected) =
      prescribedBasisCone (embedding := fan.starEmbedding ray)
        (basisVectorQuotient basis removed ray.val rfl)
        (selected.subtype (fun index => index ≠ removed)) := by
  dsimp only
  rw [prescribedBasisCone, pointedCone_map_hull]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨index, member, rfl⟩, rfl⟩
    by_cases equal : index = removed
    · subst index
      have killed : fan.starProjection (fan.prescribedBasisRay basis fullMember removed)
          (embedding (basis removed)) = 0 := by
        change (Submodule.span ℝ {embedding (basis removed)}).mkQ (embedding (basis removed)) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton _)
      rw [killed]
      exact Submodule.zero_mem _
    · apply PointedCone.subset_hull
      refine ⟨⟨index, equal⟩, ?_, ?_⟩
      · simpa using member
      · simp only [basisVectorQuotient_apply, starEmbedding_mkQ]
  · apply Submodule.span_le.mpr
    rintro _ ⟨index, member, rfl⟩
    simp only [basisVectorQuotient_apply, starEmbedding_mkQ]
    apply PointedCone.subset_hull
    exact ⟨embedding (basis index.val), ⟨index.val, by simpa using member, rfl⟩, rfl⟩

omit [FiniteDimensional ℝ Ambient] in
theorem prescribedQuotientBasisCone_mem (fan : Fan embedding) (basis : Basis Index ℤ Lattice)
    (fullMember : PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones)
    (removed : Index) :
    let ray := fan.prescribedBasisRay basis fullMember removed
    PointedCone.hull ℝ (Set.range (fun index => fan.starEmbedding ray
      (basisVectorQuotient basis removed ray.val rfl index))) ∈ (fan.star ray).cones := by
  let ray := fan.prescribedBasisRay basis fullMember removed
  dsimp only
  let realBasis := fan.lattice.isBaseChange.basis basis
  have realEquality : realBasis removed = embedding ray.val :=
    fan.lattice.isBaseChange.basis_apply basis removed
  have quotientEquality := basisVectorQuotient_cone realBasis removed (embedding ray.val) realEquality
  have sourceEquality : Set.range realBasis = Set.range (fun index => embedding (basis index)) := by
    congr 1
    funext index
    exact fan.lattice.isBaseChange.basis_apply basis index
  have targetEquality : Set.range (basisVectorQuotient realBasis removed (embedding ray.val) realEquality) =
      Set.range (fun index => fan.starEmbedding ray (basisVectorQuotient basis removed ray.val rfl index)) := by
    congr 1
    funext index
    simp only [basisVectorQuotient_apply, starEmbedding_mkQ]
    rw [show realBasis index.val = embedding (basis index.val) from
      fan.lattice.isBaseChange.basis_apply basis index.val]
    rfl
  rw [sourceEquality, targetEquality] at quotientEquality
  rw [← quotientEquality]
  exact ⟨_, ⟨fullMember, PointedCone.subset_hull ⟨removed, rfl⟩⟩, rfl⟩

def RayStarChainContracts (steps : ℕ) {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient} (fan : Fan embedding) (cone : PointedCone ℝ Ambient)
    (chain : RayStarChain steps fan) : Prop :=
  match steps with
  | 0 => cone = ⊥
  | steps + 1 => embedding chain.1.val ∈ cone ∧
      RayStarChainContracts steps (fan.star chain.1) (PointedCone.map (fan.starProjection chain.1) cone) chain.2

theorem exists_basisSubset_contractingChain (steps : ℕ) {Lattice Ambient Index : Type}
    [AddCommGroup Lattice] [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Fintype Index] [DecidableEq Index]
    {embedding : Lattice →+ Ambient} (fan : Fan embedding) (basis : Basis Index ℤ Lattice)
    (fullMember : PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones)
    (selected : Finset Index) (cardinality : selected.card = steps) :
    ∃ chain : RayStarChain steps fan,
      fan.RayStarChainContracts steps (prescribedBasisCone (embedding := embedding) basis selected) chain := by
  induction steps generalizing Lattice Ambient Index with
  | zero =>
    have empty : selected = ∅ := Finset.card_eq_zero.mp cardinality
    exact ⟨PUnit.unit, by simp [RayStarChainContracts, prescribedBasisCone, empty]⟩
  | succ steps inductionHypothesis =>
    obtain ⟨removed, member⟩ := Finset.card_pos.mp (show 0 < selected.card by omega)
    let ray := fan.prescribedBasisRay basis fullMember removed
    let quotientBasis := basisVectorQuotient basis removed ray.val rfl
    let remaining := selected.subtype (fun index => index ≠ removed)
    have remainingCard : remaining.card = steps := by
      simp only [remaining, Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem member]
      omega
    obtain ⟨chain, contracts⟩ := inductionHypothesis (fan.star ray) quotientBasis
      (fan.prescribedQuotientBasisCone_mem basis fullMember removed) remaining remainingCard
    refine ⟨⟨ray, chain⟩, fan.prescribedBasisRay_mem basis fullMember selected removed member, ?_⟩
    rw [fan.prescribedBasisCone_projected basis fullMember selected removed]
    exact contracts

omit [FiniteDimensional ℝ Ambient] [Fintype Index] [DecidableEq Index] in
theorem prescribedBasisCone_span_finrank (fan : Fan embedding) (basis : Basis Index ℤ Lattice)
    (selected : Finset Index) :
    Module.finrank ℝ (Submodule.span ℝ
      (prescribedBasisCone (embedding := embedding) basis selected : Set Ambient)) = selected.card := by
  let realBasis := fan.lattice.isBaseChange.basis basis
  have generatorEquality : ((fun index => embedding (basis index)) '' (selected : Set Index)) =
      Set.range (fun index : selected => realBasis index.val) := by
    ext point
    constructor
    · rintro ⟨index, member, rfl⟩
      exact ⟨⟨index, member⟩, fan.lattice.isBaseChange.basis_apply basis index⟩
    · rintro ⟨index, rfl⟩
      exact ⟨index.val, index.property, (fan.lattice.isBaseChange.basis_apply basis index.val).symm⟩
  rw [prescribedBasisCone, PointedCone.hull, Submodule.span_span_of_tower (Nonneg ℝ) ℝ,
    generatorEquality]
  have independent := realBasis.linearIndependent.comp
    (fun index : selected => index.val) Subtype.val_injective
  simpa only [Function.comp_def, Fintype.card_coe] using finrank_span_eq_card independent

omit [Fintype Index] [DecidableEq Index] in

theorem exists_prescribedConeBasisSubset (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones) :
    ∃ size : ℕ, ∃ basis : Basis (Fin size) ℤ Lattice, ∃ selected : Finset (Fin size),
      fan.IsConeBasis basis ∧
        cone.val = prescribedBasisCone (embedding := embedding) basis selected ∧
        selected.card = Module.finrank ℝ (Submodule.span ℝ (cone.val : Set Ambient)) := by
  classical
  obtain ⟨size, basis, fullMember, face⟩ :=
    fan.exists_coneBasis_above complete regular cone.val cone.property
  let selected := Finset.univ.filter (fun index => embedding (basis index) ∈ cone.val)
  have coneEquality : cone.val = prescribedBasisCone (embedding := embedding) basis selected := by
    have faceEquality := (⟨cone.val, face⟩ :
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))).Face).eq_hull_image rfl
    change cone.val = PointedCone.hull ℝ
      ((fun index => embedding (basis index)) '' {index | embedding (basis index) ∈ cone.val})
      at faceEquality
    simpa only [prescribedBasisCone, selected, Finset.coe_filter, Finset.coe_univ,
      Finset.mem_univ, true_and] using faceEquality
  refine ⟨size, basis, selected, fullMember, coneEquality, ?_⟩
  rw [coneEquality]
  exact (fan.prescribedBasisCone_span_finrank basis selected).symm

omit [Fintype Index] [DecidableEq Index] in

theorem exists_prescribedCone_contractingChain (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones) :
    ∃ chain : RayStarChain (Module.finrank ℝ (Submodule.span ℝ (cone.val : Set Ambient))) fan,
      fan.RayStarChainContracts _ cone.val chain := by
  obtain ⟨_, basis, selected, fullMember, coneEquality, cardinality⟩ :=
    fan.exists_prescribedConeBasisSubset complete regular cone
  obtain ⟨chain, contracts⟩ := fan.exists_basisSubset_contractingChain _ basis fullMember selected cardinality
  exact ⟨chain, by simpa only [coneEquality] using contracts⟩

omit [Fintype Index] [DecidableEq Index] in

def prescribedWallChain (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (wall : fan.cones) :
    RayStarChain (Module.finrank ℝ (Submodule.span ℝ (wall.val : Set Ambient))) fan :=
  (fan.exists_prescribedCone_contractingChain complete regular wall).choose

omit [Fintype Index] [DecidableEq Index] in
theorem prescribedWallChain_contracts (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (wall : fan.cones) :
    fan.RayStarChainContracts _ wall.val (fan.prescribedWallChain complete regular wall) :=
  (fan.exists_prescribedCone_contractingChain complete regular wall).choose_spec

omit [Fintype Index] [DecidableEq Index] in
theorem prescribedWallChain_rank_one (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (wall : fan.cones)
    (codimensionOne : Module.finrank ℝ (Submodule.span ℝ (wall.val : Set Ambient)) + 1 =
      Module.finrank ℤ Lattice) :
    fan.iteratedStarLatticeRank _ (fan.prescribedWallChain complete regular wall) = 1 :=
  (fan.iteratedStarChain_rank_one_iff _ _).mpr codimensionOne

omit [Fintype Index] [DecidableEq Index] in

def prescribedWallIntegralCurve (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (wall : fan.cones)
    (codimensionOne : Module.finrank ℝ (Submodule.span ℝ (wall.val : Set Ambient)) + 1 =
      Module.finrank ℤ Lattice) : IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular) :=
  fan.iteratedStarIntegralCurve 𝕜 _ complete regular (fan.prescribedWallChain complete regular wall)
    (fan.prescribedWallChain_rank_one complete regular wall codimensionOne)

omit [Fintype Index] [DecidableEq Index] in
def prescribedWallLineBundleDegree (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (wall : fan.cones)
    (codimensionOne : Module.finrank ℝ (Submodule.span ℝ (wall.val : Set Ambient)) + 1 =
      Module.finrank ℤ Lattice) (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) : ℤ :=
  fan.iteratedStarCurveLineBundleDegree 𝕜 _ complete regular (fan.prescribedWallChain complete regular wall)
    (fan.prescribedWallChain_rank_one complete regular wall codimensionOne) bundle

end TauCeti.Toric.Fan
