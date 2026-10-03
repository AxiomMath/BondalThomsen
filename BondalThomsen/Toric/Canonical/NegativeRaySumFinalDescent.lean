module

public import BondalThomsen.Toric.Canonical.NegativeRaySumGlobalComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem canonicalNegativeRaySumRankLocalIso_faceSection [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin (Module.finrank ℤ Lattice)) ℤ Lattice)
    (index : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).Index)
    (face : fan.cones)
    (face_of : face.val.IsFaceOf
      (fan.divisorChartCone complete regular ((Finite.equivFin fan.cones).symm index)).val)
    (denominator : affineCoordinateRing 𝕜 fan.lattice face.val) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let atlas := ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).neg 𝕜).cartierEquationAtlas 𝕜
        (fan.completeFan_nonemptyCones complete)
    let cone := (Finite.equivFin fan.cones).symm index
    let basis := fan.canonicalDivisorChartRankBasis complete regular cone
    let faceProof := Eq.mp (congrArg (fun actualCone => face.val.IsFaceOf actualCone)
      (fan.canonicalDivisorChartRankBasis_cone complete regular cone).symm) face_of
    let domain := (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj
      (PrimeSpectrum.basicOpen denominator)
    let contained := (fan.canonicalFaceChartLE 𝕜 regular
      (cone := fan.divisorChartCone complete regular cone) face_of
      (PrimeSpectrum.basicOpen denominator)).trans
        (fan.affineToricChartι 𝕜 regular (fan.divisorChartCone complete regular cone)).image_top_eq_opensRange.le
    (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference index).hom.val.app
      (op (Over.mk (homOfLE contained)))
      (fan.globalOrientedFaceCanonicalSection 𝕜 regular reference basis face faceProof denominator) =
    BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction atlas index domain contained := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  dsimp only
  let cone := (Finite.equivFin fan.cones).symm index
  let basis := fan.canonicalDivisorChartRankBasis complete regular cone
  let cone_basis := fan.canonicalDivisorChartRankBasis_isConeBasis complete regular cone
  let atlas := ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular
    (-fan.anticanonicalRayDivisor)).neg 𝕜).cartierEquationAtlas 𝕜 (fan.completeFan_nonemptyCones complete)
  let chartEquality := (fan.canonicalDivisorChartRankBasis_chart 𝕜 complete regular cone).symm
  have image := fan.normalizedCanonicalCartierIso_faceSection 𝕜 regular reference basis cone_basis
    atlas index chartEquality face
    (Eq.mp (congrArg (fun actualCone => face.val.IsFaceOf actualCone)
      (fan.canonicalDivisorChartRankBasis_cone complete regular cone).symm) face_of)
    denominator
  exact image

theorem canonicalNegativeRaySumRankLocalCharacter [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (index : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).Index) :
    let cone := (Finite.equivFin fan.cones).symm index
    let basis := fan.canonicalDivisorChartRankBasis complete regular cone
    fan.coneDivisorCharacter basis
      (fan.canonicalDivisorChartRankBasis_isConeBasis complete regular cone)
      (-fan.anticanonicalRayDivisor) =
    (fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).character
      index :=
  fan.canonicalDivisorChartRankBasis_character complete regular
    ((Finite.equivFin fan.cones).symm index) (-fan.anticanonicalRayDivisor)

theorem canonicalNegativeRaySumRankOverlapCone [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).Index) :
    let firstBasis := fan.canonicalDivisorChartRankBasis complete regular
      ((Finite.equivFin fan.cones).symm first)
    let secondBasis := fan.canonicalDivisorChartRankBasis complete regular
      ((Finite.equivFin fan.cones).symm second)
    PointedCone.hull ℝ (Set.range (fun index => embedding (firstBasis index))) ⊓
      PointedCone.hull ℝ (Set.range (fun index => embedding (secondBasis index))) =
    ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
      first ⊓
      (fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
        second).val := by
  dsimp only
  exact congrArg₂ (fun firstCone secondCone : PointedCone ℝ Ambient => firstCone ⊓ secondCone)
    (fan.canonicalDivisorChartRankBasis_cone complete regular ((Finite.equivFin fan.cones).symm first))
    (fan.canonicalDivisorChartRankBasis_cone complete regular ((Finite.equivFin fan.cones).symm second))

theorem canonicalNegativeRaySumRankTransitionMonomial [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).Index) :
    let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)
    let firstBasis := fan.canonicalDivisorChartRankBasis complete regular
      ((Finite.equivFin fan.cones).symm first)
    let secondBasis := fan.canonicalDivisorChartRankBasis complete regular
      ((Finite.equivFin fan.cones).symm second)
    let overlapEquality := fan.canonicalNegativeRaySumRankOverlapCone 𝕜 complete regular first second
    Eq.mp (congrArg (fun actualCone => (affineCoordinateRing 𝕜 fan.lattice actualCone)ˣ)
      overlapEquality)
      ((fan.coneDivisorTransitionUnit 𝕜 firstBasis
        (fan.canonicalDivisorChartRankBasis_isConeBasis complete regular
          ((Finite.equivFin fan.cones).symm first)) secondBasis
        (fan.canonicalDivisorChartRankBasis_isConeBasis complete regular
          ((Finite.equivFin fan.cones).symm second)) (-fan.anticanonicalRayDivisor))⁻¹) =
    toricMonomialUnit 𝕜 fan.lattice (atlas.cone first ⊓ atlas.cone second).val
      (-atlas.character first - -atlas.character second)
      ((atlas.neg 𝕜).positive first second) ((atlas.neg 𝕜).negative first second) := by
  dsimp only
  have firstCharacter := fan.canonicalNegativeRaySumRankLocalCharacter 𝕜 complete regular first
  have secondCharacter := fan.canonicalNegativeRaySumRankLocalCharacter 𝕜 complete regular second
  have transport : ∀ {sourceCone targetCone : PointedCone ℝ Ambient}
      (same : sourceCone = targetCone) (character : Lattice →+ ℤ)
      (positive : character ∈ dualSemigroup fan.lattice sourceCone)
      (negative : -character ∈ dualSemigroup fan.lattice sourceCone),
      Eq.mp (congrArg (fun actualCone => (affineCoordinateRing 𝕜 fan.lattice actualCone)ˣ) same)
        ((toricMonomialUnit 𝕜 fan.lattice sourceCone character positive negative)⁻¹) =
      toricMonomialUnit 𝕜 fan.lattice targetCone (-character)
        (Eq.mp (congrArg (fun actualCone => -character ∈ dualSemigroup fan.lattice actualCone)
          same) negative)
        (by simpa only [neg_neg] using (Eq.mp
          (congrArg (fun actualCone => character ∈ dualSemigroup fan.lattice actualCone) same)
          positive)) := by
    intro sourceCone targetCone same character positive negative
    cases same
    apply Units.ext
    rfl
  unfold coneDivisorTransitionUnit
  rw [transport (fan.canonicalNegativeRaySumRankOverlapCone 𝕜 complete regular first second)]
  apply Units.ext
  simp only [toricMonomialUnit_val]
  congr 2
  apply Subtype.ext
  exact (congrArg (fun character : Lattice →+ ℤ => -character)
    (congrArg₂ (fun firstCharacter secondCharacter : Lattice →+ ℤ =>
      firstCharacter - secondCharacter) firstCharacter secondCharacter)).trans (by abel_nf)

theorem canonicalNegativeRaySumRankFaceTransition [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin (Module.finrank ℤ Lattice)) ℤ Lattice)
    (first second : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).Index)
    (firstFace :
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
        first ⊓
        (fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
          second).val.IsFaceOf
        (PointedCone.hull ℝ (Set.range (fun index => embedding
          (fan.canonicalDivisorChartRankBasis complete regular
            ((Finite.equivFin fan.cones).symm first) index)))))
    (secondFace :
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
        first ⊓
        (fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
          second).val.IsFaceOf
        (PointedCone.hull ℝ (Set.range (fun index => embedding
          (fan.canonicalDivisorChartRankBasis complete regular
            ((Finite.equivFin fan.cones).symm second) index)))))
    (denominator : affineCoordinateRing 𝕜 fan.lattice
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
        first ⊓
        (fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
          second).val) :
    let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)
    let face := atlas.cone first ⊓ atlas.cone second
    let domain := PrimeSpectrum.basicOpen denominator
    let contained := ((fan.affineToricChartι 𝕜 regular face).opensFunctor.map domain.leTop).le.trans
      ((fan.affineToricChartι 𝕜 regular face).image_top_eq_opensRange.le.trans
        (fan.chart_opensRange_intersection 𝕜 regular (atlas.cone first) (atlas.cone second)).le)
    (fan.globalOrientedFaceCanonicalSection 𝕜) regular reference
      (fan.canonicalDivisorChartRankBasis complete regular ((Finite.equivFin fan.cones).symm second))
      face secondFace denominator =
    (fan.algebraicRealization 𝕜 regular).presheaf.map (homOfLE contained).op
      ((atlas.neg 𝕜).transition 𝕜 first second).val •
    fan.globalOrientedFaceCanonicalSection 𝕜 regular reference
      (fan.canonicalDivisorChartRankBasis complete regular ((Finite.equivFin fan.cones).symm first))
      face firstFace denominator := by
  let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)
  let firstBasis := fan.canonicalDivisorChartRankBasis complete regular
    ((Finite.equivFin fan.cones).symm first)
  let secondBasis := fan.canonicalDivisorChartRankBasis complete regular
    ((Finite.equivFin fan.cones).symm second)
  let firstCone := fan.canonicalDivisorChartRankBasis_isConeBasis complete regular
    ((Finite.equivFin fan.cones).symm first)
  let secondCone := fan.canonicalDivisorChartRankBasis_isConeBasis complete regular
    ((Finite.equivFin fan.cones).symm second)
  let basisFace : fan.cones := ⟨_, fan.inf_mem firstCone secondCone⟩
  let face := atlas.cone first ⊓ atlas.cone second
  let monomial := (fan.coneDivisorTransitionUnit 𝕜 firstBasis firstCone secondBasis secondCone
    (-fan.anticanonicalRayDivisor))⁻¹
  let transitionProperty (actualFace : fan.cones)
      (actualUnit : (affineCoordinateRing 𝕜 fan.lattice actualFace.val)ˣ) : Prop :=
    ∀ (leftFace : actualFace.val.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (firstBasis index)))) )
      (rightFace : actualFace.val.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (secondBasis index)))))
      (denominator : affineCoordinateRing 𝕜 fan.lattice actualFace.val),
    fan.globalOrientedFaceCanonicalSection 𝕜 regular reference secondBasis actualFace rightFace denominator =
      ((fan.affineToricChartι 𝕜 regular actualFace).appIso (PrimeSpectrum.basicOpen denominator)).inv
        (BondalThomsen.CanonicalRaySumSheaf.affineRegularSection
          (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice actualFace.val)) denominator actualUnit.val) •
        fan.globalOrientedFaceCanonicalSection 𝕜 regular reference firstBasis actualFace leftFace denominator
  have onBasisFace : transitionProperty basisFace monomial := by
    intro leftFace rightFace denominator
    exact fan.globalOrientedOverlapCanonicalSection_transition 𝕜 regular reference firstBasis firstCone
      secondBasis secondCone denominator
  have transfer : ∀ (left right : fan.cones) (same : left = right)
      (actualUnit : (affineCoordinateRing 𝕜 fan.lattice left.val)ˣ),
      transitionProperty left actualUnit → transitionProperty right
        (Eq.mp (congrArg (fun actualFace => (affineCoordinateRing 𝕜 fan.lattice actualFace.val)ˣ)
          same) actualUnit) := by
    intro left right same actualUnit proved
    cases same
    exact proved
  have faceEquality : basisFace = face :=
    Subtype.ext (fan.canonicalNegativeRaySumRankOverlapCone 𝕜 complete regular first second)
  have transported := transfer basisFace face faceEquality monomial onBasisFace
  have unitEquality := fan.canonicalNegativeRaySumRankTransitionMonomial 𝕜 complete regular first second
  have onAtlasFace : transitionProperty face
      (toricMonomialUnit 𝕜 fan.lattice face.val (-atlas.character first - -atlas.character second)
        ((atlas.neg 𝕜).positive first second) ((atlas.neg 𝕜).negative first second)) :=
    Eq.mp (congrArg (transitionProperty face) unitEquality) transported
  have determinant := onAtlasFace firstFace secondFace denominator
  have scalar := (atlas.neg 𝕜).transition_principalOpen 𝕜 first second denominator
  exact determinant.trans (congrArg (fun coefficient => coefficient •
    fan.globalOrientedFaceCanonicalSection 𝕜 regular reference firstBasis face firstFace denominator)
    scalar.symm)

theorem canonicalNegativeRaySumRankLocalIso_faceCompatible [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin (Module.finrank ℤ Lattice)) ℤ Lattice)
    (first second : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).Index) :
    let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)
    let face := atlas.cone first ⊓ atlas.cone second
    let _domain := (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj
      (PrimeSpectrum.basicOpen (1 : affineCoordinateRing 𝕜 fan.lattice face.val))
    let inOverlap := ((fan.affineToricChartι 𝕜 regular face).opensFunctor.map
      (PrimeSpectrum.basicOpen (1 : affineCoordinateRing 𝕜 fan.lattice face.val)).leTop).le.trans
      ((fan.affineToricChartι 𝕜 regular face).image_top_eq_opensRange.le.trans
        (fan.chart_opensRange_intersection 𝕜 regular (atlas.cone first) (atlas.cone second)).le)
    BondalThomsen.restrictLocalModuleHom (inOverlap.trans inf_le_left)
      (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference first).hom =
    BondalThomsen.restrictLocalModuleHom (inOverlap.trans inf_le_right)
      (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference second).hom := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)
  let cartier := (atlas.neg 𝕜).cartierEquationAtlas 𝕜 (fan.completeFan_nonemptyCones complete)
  let source := fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice)
  let target := (fan.invariantDivisorLineBundle 𝕜 complete regular (-fan.anticanonicalRayDivisor)).obj
  let firstCone := (Finite.equivFin fan.cones).symm first
  let secondCone := (Finite.equivFin fan.cones).symm second
  let firstBasis := fan.canonicalDivisorChartRankBasis complete regular firstCone
  let secondBasis := fan.canonicalDivisorChartRankBasis complete regular secondCone
  let firstBasisCone := fan.canonicalDivisorChartRankBasis_isConeBasis complete regular firstCone
  let secondBasisCone := fan.canonicalDivisorChartRankBasis_isConeBasis complete regular secondCone
  let face := atlas.cone first ⊓ atlas.cone second
  let denominator := (1 : affineCoordinateRing 𝕜 fan.lattice face.val)
  let domain := (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj (PrimeSpectrum.basicOpen denominator)
  have firstFace : face.val.IsFaceOf (atlas.cone first).val :=
    fan.inf_isFaceOf_left (atlas.cone first).property (atlas.cone second).property
  have secondFace : face.val.IsFaceOf (atlas.cone second).val :=
    fan.inf_isFaceOf_right (atlas.cone first).property (atlas.cone second).property
  let firstBasisFace := Eq.mp (congrArg (fun actualCone => face.val.IsFaceOf actualCone)
    (fan.canonicalDivisorChartRankBasis_cone complete regular firstCone).symm) firstFace
  let secondBasisFace := Eq.mp (congrArg (fun actualCone => face.val.IsFaceOf actualCone)
    (fan.canonicalDivisorChartRankBasis_cone complete regular secondCone).symm) secondFace
  let firstFrame := fan.globalOrientedFaceCanonicalSection 𝕜 regular reference firstBasis face
    firstBasisFace denominator
  let secondFrame := fan.globalOrientedFaceCanonicalSection 𝕜 regular reference secondBasis face
    secondBasisFace denominator
  have inOverlap : domain ≤ cartier.chart first ⊓ cartier.chart second :=
    ((fan.affineToricChartι 𝕜 regular face).opensFunctor.map (PrimeSpectrum.basicOpen denominator).leTop).le.trans
      ((fan.affineToricChartι 𝕜 regular face).image_top_eq_opensRange.le.trans
        (fan.chart_opensRange_intersection 𝕜 regular (atlas.cone first) (atlas.cone second)).le)
  let firstMap := BondalThomsen.restrictLocalModuleHom (inOverlap.trans inf_le_left)
    (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference first).hom
  let secondMap := BondalThomsen.restrictLocalModuleHom (inOverlap.trans inf_le_right)
    (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference second).hom
  let secondInclusion := fan.affineToricChartι 𝕜 regular ⟨_, secondBasisCone⟩
  have inSecondBasis : domain ≤ secondInclusion.opensRange :=
    (inOverlap.trans inf_le_right).trans
      (fan.canonicalDivisorChartRankBasis_chart 𝕜 complete regular secondCone).symm.le
  let coordinates := BondalThomsen.CanonicalGlobalRaySum.restrictLocalModuleIso inSecondBasis
    (BondalThomsen.CanonicalNegativeRaySum.openImmersionUnitOverIso secondInclusion source
      (fan.basisConeOrientedCanonicalUnitIso 𝕜 regular reference secondBasis secondBasisCone))
  have coordinate_one : coordinates.hom.val.app (op (Over.mk (𝟙 domain))) secondFrame =
      (1 : Γ(fan.algebraicRealization 𝕜 regular, domain)) := by
    have restriction := fan.basisConeOrientedGlobalCanonicalFrame_restriction 𝕜 regular reference
      secondBasis secondBasisCone face secondBasisFace denominator
    have image := BondalThomsen.CanonicalNegativeRaySumGlobal.openImmersionUnitOverIso_hom_restrictedFrame
      secondInclusion source
      (fan.basisConeOrientedCanonicalUnitIso 𝕜 regular reference secondBasis secondBasisCone)
      (fan.basisConeOrientedGlobalCanonicalFrame 𝕜 regular reference secondBasis secondBasisCone)
      (fan.basisConeOrientedCanonicalUnitIso_topFrame 𝕜 regular reference secondBasis secondBasisCone)
      domain inSecondBasis
    exact (congrArg
      ((BondalThomsen.CanonicalNegativeRaySum.openImmersionUnitOverIso secondInclusion source
        (fan.basisConeOrientedCanonicalUnitIso 𝕜 regular reference secondBasis secondBasisCone)).hom.val.app
          (op (Over.mk (homOfLE inSecondBasis)))) restriction.symm).trans image
  apply BondalThomsen.CanonicalNegativeRaySumGlobal.localHom_ext_frame domain source target coordinates
    secondFrame coordinate_one firstMap secondMap
  have firstImage := fan.canonicalNegativeRaySumRankLocalIso_faceSection 𝕜 complete regular reference
    first face firstFace denominator
  have secondImage := fan.canonicalNegativeRaySumRankLocalIso_faceSection 𝕜 complete regular reference
    second face secondFace denominator
  have determinant := fan.canonicalNegativeRaySumRankFaceTransition 𝕜 complete regular reference first
    second firstBasisFace secondBasisFace denominator
  let scalar := (fan.algebraicRealization 𝕜 regular).presheaf.map (homOfLE inOverlap).op
    (cartier.transition first second).val
  have generators : BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction cartier second domain
      (inOverlap.trans inf_le_right) =
    scalar • BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction cartier first domain
      (inOverlap.trans inf_le_left) := by
    have transition := congrArg (target.val.map (homOfLE inOverlap).op)
      (BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrame_transition cartier first second)
    have scaled := target.val.map_smul (homOfLE inOverlap).op
      (cartier.transition first second).val
      (BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction cartier first
        (cartier.chart first ⊓ cartier.chart second) inf_le_left)
    have restriction : ∀ (index : cartier.Index)
        (contained : cartier.chart first ⊓ cartier.chart second ≤ cartier.chart index),
        target.val.map (homOfLE inOverlap).op
          (BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction cartier index
            (cartier.chart first ⊓ cartier.chart second) contained) =
        BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction cartier index domain
          (inOverlap.trans contained) := by
      intro index contained
      change target.val.presheaf.map _ (target.val.presheaf.map _ _) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    exact (restriction second inf_le_right).symm.trans
      (transition.trans (scaled.trans (congrArg (fun sectionValue : target.val.obj (op domain) =>
        scalar • sectionValue)
        (restriction first inf_le_left))))
  have firstImage' : firstMap.val.app (op (Over.mk (𝟙 domain))) firstFrame =
      BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction cartier first domain
        (inOverlap.trans inf_le_left) := firstImage
  have secondImage' : secondMap.val.app (op (Over.mk (𝟙 domain))) secondFrame =
      BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrameRestriction cartier second domain
        (inOverlap.trans inf_le_right) := secondImage
  exact (congrArg (firstMap.val.app (op (Over.mk (𝟙 domain)))) determinant).trans
    (((firstMap.val.app (op (Over.mk (𝟙 domain)))).hom.map_smul scalar firstFrame).trans
      ((congrArg (fun sectionValue => scalar • sectionValue) firstImage').trans
        (generators.symm.trans secondImage'.symm)))

theorem canonicalNegativeRaySumRankLocalIso_compatible [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin (Module.finrank ℤ Lattice)) ℤ Lattice)
    (first second : (fan.invariantDivisorCharacterAtlas 𝕜 complete regular
      (-fan.anticanonicalRayDivisor)).Index) :
    let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)
    BondalThomsen.restrictLocalModuleHom
      (inf_le_left : (fan.affineToricChartι 𝕜 regular (atlas.cone first)).opensRange ⊓
        (fan.affineToricChartι 𝕜 regular (atlas.cone second)).opensRange ≤
        (fan.affineToricChartι 𝕜 regular (atlas.cone first)).opensRange)
      (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference first).hom =
    BondalThomsen.restrictLocalModuleHom
      (inf_le_right : (fan.affineToricChartι 𝕜 regular (atlas.cone first)).opensRange ⊓
        (fan.affineToricChartι 𝕜 regular (atlas.cone second)).opensRange ≤
        (fan.affineToricChartι 𝕜 regular (atlas.cone second)).opensRange)
      (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference second).hom := by
  let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)
  let face := atlas.cone first ⊓ atlas.cone second
  let firstChart := (fan.affineToricChartι 𝕜 regular (atlas.cone first)).opensRange
  let secondChart := (fan.affineToricChartι 𝕜 regular (atlas.cone second)).opensRange
  have domainEquality : (fan.affineToricChartι 𝕜 regular face).opensFunctor.obj
      (PrimeSpectrum.basicOpen (1 : affineCoordinateRing 𝕜 fan.lattice face.val)) =
      firstChart ⊓ secondChart := by
    rw [PrimeSpectrum.basicOpen_one]
    exact (fan.affineToricChartι 𝕜 regular face).image_top_eq_opensRange.trans
      (fan.chart_opensRange_intersection 𝕜 regular (atlas.cone first) (atlas.cone second))
  have transport : ∀ (domain : (fan.algebraicRealization 𝕜 regular).Opens)
      (same : domain = firstChart ⊓ secondChart) (contained : domain ≤ firstChart ⊓ secondChart),
      BondalThomsen.restrictLocalModuleHom (contained.trans inf_le_left)
        (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference first).hom =
      BondalThomsen.restrictLocalModuleHom (contained.trans inf_le_right)
        (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference second).hom →
      BondalThomsen.restrictLocalModuleHom (inf_le_left : firstChart ⊓ secondChart ≤ firstChart)
        (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference first).hom =
      BondalThomsen.restrictLocalModuleHom (inf_le_right : firstChart ⊓ secondChart ≤ secondChart)
        (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference second).hom := by
    intro domain same contained proved
    cases same
    exact proved
  exact transport _ domainEquality domainEquality.le
    (fan.canonicalNegativeRaySumRankLocalIso_faceCompatible 𝕜 complete regular reference first second)

noncomputable def toricCanonicalNegativeRaySumIsoWithReference [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin (Module.finrank ℤ Lattice)) ℤ Lattice) :
    fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice) ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular (-fan.anticanonicalRayDivisor)).obj :=
  BondalThomsen.CanonicalGlobalRaySum.glueLocalModuleIso
    (fun index => (fan.affineToricChartι 𝕜 regular
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).cone
        index)).opensRange)
    (fan.invariantDivisorCharacterAtlas 𝕜 complete regular (-fan.anticanonicalRayDivisor)).covers
    (fan.canonicalNegativeRaySumRankLocalIso 𝕜 complete regular reference)
    (fan.canonicalNegativeRaySumRankLocalIso_compatible 𝕜 complete regular reference)

noncomputable def toricCanonicalNegativeRaySumIso [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice) ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular (-fan.anticanonicalRayDivisor)).obj :=
  fan.toricCanonicalNegativeRaySumIsoWithReference 𝕜 complete regular
    (fan.canonicalDivisorChartRankBasis complete regular
      (fan.botCone (fan.completeFan_nonemptyCones complete)))

end TauCeti.Toric.Fan
