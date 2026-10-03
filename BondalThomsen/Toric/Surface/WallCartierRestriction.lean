module

public import BondalThomsen.Toric.Positivity.WallCurveDegree
public import BondalThomsen.Toric.Divisor.CartierChoiceIndependence
public import BondalThomsen.Toric.Canonical.NegativeRaySumDescent
public import BondalThomsen.LineBundle.AmpleLineBundleTensorLocalDescent

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module TopologicalSpace Opposite Multiplicative
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace BondalThomsen

theorem wallChartSections_appLE {source target sourceChart targetChart : Scheme}
    (sourceInclusion : sourceChart ⟶ source) (targetInclusion : targetChart ⟶ target)
    [IsOpenImmersion sourceInclusion] [IsOpenImmersion targetInclusion]
    (map : source ⟶ target) (chartMap : sourceChart ⟶ targetChart)
    (factorization : sourceInclusion ≫ map = chartMap ≫ targetInclusion)
    (contained : sourceInclusion.opensRange ≤ map ⁻¹ᵁ targetInclusion.opensRange)
    (sectionValue : Γ(targetChart, ⊤)) :
    map.appLE targetInclusion.opensRange sourceInclusion.opensRange contained
        ((IsOpenImmersion.ΓIsoTop targetInclusion).hom sectionValue) =
      (IsOpenImmersion.ΓIsoTop sourceInclusion).hom (chartMap.appTop sectionValue) := by
  have sourceContains : ⊤ ≤ sourceInclusion ⁻¹ᵁ sourceInclusion.opensRange := by
    rintro point _
    exact ⟨point, rfl⟩
  have targetContains : ⊤ ≤ targetInclusion ⁻¹ᵁ targetInclusion.opensRange := by
    rintro point _
    exact ⟨point, rfl⟩
  have compositions := Scheme.Hom.appLE_comp_appLE sourceInclusion map
    targetInclusion.opensRange sourceInclusion.opensRange ⊤ contained sourceContains
  have otherCompositions := Scheme.Hom.appLE_comp_appLE chartMap targetInclusion
    targetInclusion.opensRange ⊤ ⊤ targetContains (by simp)
  have topMap : chartMap.appLE ⊤ ⊤ (by simp) = chartMap.appTop :=
    chartMap.appLE_eq_app
  rw [topMap] at otherCompositions
  have factorizationSections : (sourceInclusion ≫ map).appLE
      targetInclusion.opensRange ⊤ (sourceContains.trans (sourceInclusion.preimage_mono contained)) =
    (chartMap ≫ targetInclusion).appLE targetInclusion.opensRange ⊤
      (by simpa only [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_top] using
        chartMap.preimage_mono targetContains) := by
    simp only [factorization]
  rw [← openImmersion_sectionsIso_inv sourceInclusion] at compositions
  rw [← openImmersion_sectionsIso_inv targetInclusion] at otherCompositions
  have sectionMaps := compositions.trans (factorizationSections.trans otherCompositions.symm)
  have sections := ConcreteCategory.congr_hom sectionMaps
    ((IsOpenImmersion.ΓIsoTop targetInclusion).hom sectionValue)
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at sections
  have mapped := congrArg (fun value => (IsOpenImmersion.ΓIsoTop sourceInclusion).hom value) sections
  simpa only [Iso.inv_hom_id_apply] using mapped

theorem wallCartierAtlasFrame_isFrame {scheme : Scheme} [IsIntegral scheme]
    (atlas : CartierEquationAtlas scheme) (index : atlas.Index) :
    Scheme.Modules.IsFrame atlas.invertibleSheaf.obj (atlas.chart index)
      (CanonicalNegativeRaySum.cartierAtlasFrame atlas index) := by
  intro smaller contained
  let subopen := Over.mk (homOfLE contained)
  let chartIso := atlas.chartTrivialization index
  let restriction : subopen ⟶ Over.mk (𝟙 (atlas.chart index)) :=
    Over.homMk (homOfLE contained)
  have naturality := PresheafOfModules.naturality_apply chartIso.hom.val
    restriction.op (1 : Γ(scheme, atlas.chart index))
  change chartIso.hom.val.app (op subopen)
      (scheme.presheaf.map (homOfLE contained).op (1 : Γ(scheme, atlas.chart index))) =
    atlas.invertibleSheaf.obj.res contained
      (CanonicalNegativeRaySum.cartierAtlasFrame atlas index) at naturality
  have imageOne : chartIso.hom.val.app (op subopen) (1 : Γ(scheme, smaller)) =
      atlas.invertibleSheaf.obj.res contained
        (CanonicalNegativeRaySum.cartierAtlasFrame atlas index) := by
    simpa only [map_one] using naturality
  have imageScalar : ∀ scalar : Γ(scheme, smaller),
      chartIso.hom.val.app (op subopen) scalar = scalar •
        atlas.invertibleSheaf.obj.res contained
          (CanonicalNegativeRaySum.cartierAtlasFrame atlas index) := by
    intro scalar
    calc
      chartIso.hom.val.app (op subopen) scalar =
          chartIso.hom.val.app (op subopen) (scalar • (1 : Γ(scheme, smaller))) := by
            rw [smul_eq_mul, mul_one]
      _ = scalar • chartIso.hom.val.app (op subopen) (1 : Γ(scheme, smaller)) :=
        (chartIso.hom.val.app (op subopen)).hom.map_smul _ _
      _ = _ := by rw [imageOne]
  let comparison := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso chartIso
  let component := comparison.app (op subopen)
  have componentIso : IsIso component.hom := inferInstance
  have bijective := (ConcreteCategory.isIso_iff_bijective _).mp componentIso
  change Function.Bijective (fun scalar : Γ(scheme, smaller) =>
    chartIso.hom.val.app (op subopen) scalar) at bijective
  rw [show (fun scalar : Γ(scheme, smaller) => scalar • atlas.invertibleSheaf.obj.res contained
    (CanonicalNegativeRaySum.cartierAtlasFrame atlas index)) =
      fun scalar => chartIso.hom.val.app (op subopen) scalar from
        funext (fun scalar => (imageScalar scalar).symm)]
  exact bijective

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance wallRestrictionRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray)

def wallRestrictionSourceIndex (cone : (fan.star ray).cones) : Fin (Nat.card fan.cones) :=
  (Finite.equivFin fan.cones) (fan.starConeLift ray cone)

def wallRestrictionSourceCone (cone : (fan.star ray).cones) : fan.cones :=
  fan.divisorChartCone complete regular (fan.starConeLift ray cone)

theorem wallRestrictionSourceCone_contains (cone : (fan.star ray).cones) :
    embedding ray.val ∈ (fan.wallRestrictionSourceCone complete regular ray cone).val :=
  (fan.divisorChartBasis complete regular (fan.starConeLift ray cone)).property.2.le
    (fan.starConeLift_contains ray cone)

def wallRestrictionQuotientCone (cone : (fan.star ray).cones) : (fan.star ray).cones :=
  ⟨PointedCone.map (fan.starProjection ray)
    (fan.wallRestrictionSourceCone complete regular ray cone).val,
    ⟨_, ⟨(fan.wallRestrictionSourceCone complete regular ray cone).property,
      fan.wallRestrictionSourceCone_contains complete regular ray cone⟩, rfl⟩⟩

theorem wallRestrictionQuotientCone_above (cone : (fan.star ray).cones) :
    cone.val.IsFaceOf (fan.wallRestrictionQuotientCone complete regular ray cone).val := by
  have projected := BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val)
    (fan.divisorChartBasis complete regular (fan.starConeLift ray cone)).property.2
    (fan.starConeLift_contains ray cone)
  change (PointedCone.map (fan.starProjection ray) (fan.starConeLift ray cone).val).IsFaceOf
    (fan.wallRestrictionQuotientCone complete regular ray cone).val at projected
  rwa [fan.starConeLift_projected ray cone] at projected

theorem wallRestrictionQuotientCone_covers : IsOpenCover
    (fun cone => ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
      (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange) := by
  apply IsOpenCover.mk
  apply top_unique
  intro point _
  obtain ⟨cone, localPoint, imageEquality⟩ := (fan.star ray).exists_affineToricChartι_apply_eq 𝕜
    (fan.star_isRegular complete regular ray) point
  refine Opens.mem_iSup.mpr ⟨cone, ?_⟩
  refine ⟨faceAffineToricSchemeMap 𝕜 (fan.star ray).lattice
    (fan.wallRestrictionQuotientCone_above complete regular ray cone) localPoint, ?_⟩
  exact (congrArg (fun morphism => morphism localPoint)
    ((fan.star ray).faceAffineToricSchemeMap_comp_affineToricChartι 𝕜
      (fan.star_isRegular complete regular ray)
      (fan.wallRestrictionQuotientCone_above complete regular ray cone))).trans imageEquality

def wallRestrictionSourceCharacter (cone : (fan.star ray).cones) : Lattice →+ ℤ :=
  fan.coneDivisorCharacter
    (fan.divisorChartBasis complete regular (fan.starConeLift ray cone)).val.2
    (fan.divisorChartBasis complete regular (fan.starConeLift ray cone)).property.1 divisor

theorem wallRestrictionSourceCharacter_ray (cone : (fan.star ray).cones) :
    fan.wallRestrictionSourceCharacter complete regular divisor ray cone ray.val = -divisor ray :=
  fan.coneDivisorCharacter_ray _ _ divisor ray
    (fan.wallRestrictionSourceCone_contains complete regular ray cone)

def wallRestrictionQuotientCharacter (reference cone : (fan.star ray).cones) :
    fan.StarLattice ray →+ ℤ :=
  fan.rayCharacterDescend ray
    (fan.wallRestrictionSourceCharacter complete regular divisor ray cone -
      fan.wallRestrictionSourceCharacter complete regular divisor ray reference)
    (by simp only [AddMonoidHom.sub_apply, wallRestrictionSourceCharacter_ray, sub_self])

@[simp] theorem wallRestrictionQuotientCharacter_mkQ
    (reference cone : (fan.star ray).cones) (vector : Lattice) :
    fan.wallRestrictionQuotientCharacter complete regular divisor ray reference cone
        ((Submodule.span ℤ {ray.val}).mkQ vector) =
      fan.wallRestrictionSourceCharacter complete regular divisor ray cone vector -
        fan.wallRestrictionSourceCharacter complete regular divisor ray reference vector := rfl

theorem wallRestrictionQuotientCharacter_difference
    (reference first second : (fan.star ray).cones) :
    fan.wallRestrictionQuotientCharacter complete regular divisor ray reference first -
        fan.wallRestrictionQuotientCharacter complete regular divisor ray reference second =
      fan.rayCharacterDescend ray
        (fan.wallRestrictionSourceCharacter complete regular divisor ray first -
          fan.wallRestrictionSourceCharacter complete regular divisor ray second)
        (by simp only [AddMonoidHom.sub_apply, wallRestrictionSourceCharacter_ray, sub_self]) := by
  ext quotientVector
  obtain ⟨vector, rfl⟩ := Submodule.mkQ_surjective (Submodule.span ℤ {ray.val}) quotientVector
  simp only [AddMonoidHom.sub_apply, wallRestrictionQuotientCharacter_mkQ,
    rayCharacterDescend_mkQ]
  omega

theorem wallRestrictionQuotientCharacter_dualSemigroup
    (reference first second : (fan.star ray).cones) :
    fan.wallRestrictionQuotientCharacter complete regular divisor ray reference first -
        fan.wallRestrictionQuotientCharacter complete regular divisor ray reference second ∈
      dualSemigroup (fan.star ray).lattice
        (fan.wallRestrictionQuotientCone complete regular ray first ⊓
          fan.wallRestrictionQuotientCone complete regular ray second).val := by
  have positive := (fan.coneDivisorCharacter_transition_dualSemigroup
    (fan.divisorChartBasis complete regular (fan.starConeLift ray first)).val.2
    (fan.divisorChartBasis complete regular (fan.starConeLift ray first)).property.1
    (fan.divisorChartBasis complete regular (fan.starConeLift ray second)).val.2
    (fan.divisorChartBasis complete regular (fan.starConeLift ray second)).property.1 divisor).1
  have descended := fan.rayCharacterDescend_mem_dualSemigroup ray
    ((fan.wallRestrictionSourceCone complete regular ray first ⊓
      fan.wallRestrictionSourceCone complete regular ray second).val)
    ⟨_, positive⟩ (by
      simp only [AddMonoidHom.sub_apply]
      rw [fan.coneDivisorCharacter_ray _ _ divisor ray
        (fan.wallRestrictionSourceCone_contains complete regular ray first),
        fan.coneDivisorCharacter_ray _ _ divisor ray
        (fan.wallRestrictionSourceCone_contains complete regular ray second), sub_self])
  rw [fan.wallRestrictionQuotientCharacter_difference]
  change _ ∈ dualSemigroup (fan.star ray).lattice
    (PointedCone.map (fan.starProjection ray)
      (fan.wallRestrictionSourceCone complete regular ray first).val ⊓
      PointedCone.map (fan.starProjection ray)
        (fan.wallRestrictionSourceCone complete regular ray second).val)
  erw [← BondalThomsen.rayQuotient_map_inf _ _ _
    (fan.wallRestrictionSourceCone_contains complete regular ray first)
    (fan.wallRestrictionSourceCone_contains complete regular ray second)]
  exact descended

def wallRestrictionCharacterAtlas (reference : (fan.star ray).cones) :
    CharacterEquationAtlas 𝕜 (fan.star ray) (fan.star_isRegular complete regular ray) where
  Index := (fan.star ray).cones
  cone := fan.wallRestrictionQuotientCone complete regular ray
  covers := fan.wallRestrictionQuotientCone_covers 𝕜 complete regular ray
  character := fan.wallRestrictionQuotientCharacter complete regular divisor ray reference
  positive := fan.wallRestrictionQuotientCharacter_dualSemigroup complete regular divisor ray reference
  negative := by
    intro first second
    rw [neg_sub]
    have positive := fan.wallRestrictionQuotientCharacter_dualSemigroup
      complete regular divisor ray reference second first
    simpa only [inf_comm] using positive

def wallRestrictionCartierDivisor (reference : (fan.star ray).cones) :
    letI := (fan.star ray).algebraicRealization_isIntegral 𝕜
      (fan.star_isRegular complete regular ray) (fan.star_cones_nonempty_of_isComplete complete ray)
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
      ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray)) := by
  letI := (fan.star ray).algebraicRealization_isIntegral 𝕜
    (fan.star_isRegular complete regular ray) (fan.star_cones_nonempty_of_isComplete complete ray)
  exact (((fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.star_cones_nonempty_of_isComplete complete ray)).cartierDivisor

def wallRestrictionLineBundle (reference : (fan.star ray).cones) :
    InvertibleSheaf ((fan.star ray).algebraicRealization 𝕜
      (fan.star_isRegular complete regular ray)) :=
  ((fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference).neg 𝕜).invertibleSheaf 𝕜
    (fan.star_cones_nonempty_of_isComplete complete ray)

theorem wallRestrictionSourceIndex_cone (cone : (fan.star ray).cones) :
    fan.divisorLocalCone 𝕜 complete regular (fan.wallRestrictionSourceIndex ray cone) =
      fan.wallRestrictionSourceCone complete regular ray cone := by
  simp only [divisorLocalCone, invariantDivisorCharacterAtlas, wallRestrictionSourceIndex,
    Equiv.symm_apply_apply, wallRestrictionSourceCone]

theorem wallRestrictionSourceIndex_character (cone : (fan.star ray).cones) :
    fan.divisorLocalCharacter 𝕜 complete regular divisor (fan.wallRestrictionSourceIndex ray cone) =
      fan.wallRestrictionSourceCharacter complete regular divisor ray cone := by
  exact congrArg (fun chosen : fan.cones =>
    fan.coneDivisorCharacter (fan.divisorChartBasis complete regular chosen).val.2
      (fan.divisorChartBasis complete regular chosen).property.1 divisor)
    ((Finite.equivFin fan.cones).symm_apply_apply (fan.starConeLift ray cone))

theorem wallRestrictionQuotientCone_lift (cone : (fan.star ray).cones) :
    fan.starConeLift ray (fan.wallRestrictionQuotientCone complete regular ray cone) =
      fan.wallRestrictionSourceCone complete regular ray cone :=
  fan.starConeLift_eq_of_projected ray _ _
    (fan.wallRestrictionSourceCone_contains complete regular ray cone) rfl

theorem wallRestrictionMap_preimage_sourceChart (cone : (fan.star ray).cones) :
    fan.completeStarOrbitClosureMap 𝕜 complete regular ray ⁻¹ᵁ
        (fan.affineToricChartι 𝕜 regular
          (fan.wallRestrictionSourceCone complete regular ray cone)).opensRange =
      ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
        (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange := by
  apply Opens.ext
  change (fan.starOrbitClosureMap 𝕜 regular ray (fan.star_isRegular complete regular ray)) ⁻¹'
    Set.range (fan.affineToricChartι 𝕜 regular
      (fan.wallRestrictionSourceCone complete regular ray cone)) = _
  rw [← fan.wallRestrictionQuotientCone_lift complete regular ray cone]
  exact fan.starOrbitClosureMap_preimage_lifted_chart 𝕜 regular ray _ _

def wallRestrictionAmbientFrame (cone : (fan.star ray).cones) :
    Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
      (fan.affineToricChartι 𝕜 regular
        (fan.wallRestrictionSourceCone complete regular ray cone)).opensRange) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let atlas := ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)
  exact (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.res
    (show (fan.affineToricChartι 𝕜 regular
        (fan.wallRestrictionSourceCone complete regular ray cone)).opensRange ≤
      atlas.chart (fan.wallRestrictionSourceIndex ray cone) from
        (congrArg (fun chosen => (fan.affineToricChartι 𝕜 regular chosen).opensRange)
          (fan.wallRestrictionSourceIndex_cone 𝕜 complete regular ray cone)).ge)
    (BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrame atlas
      (fan.wallRestrictionSourceIndex ray cone))

theorem wallRestrictionAmbientFrame_isFrame (cone : (fan.star ray).cones) :
    Scheme.Modules.IsFrame (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
      (fan.affineToricChartι 𝕜 regular
        (fan.wallRestrictionSourceCone complete regular ray cone)).opensRange
      (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray cone) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  have frame := BondalThomsen.wallCartierAtlasFrame_isFrame
    (((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
      (fan.completeFan_nonemptyCones complete)) (fan.wallRestrictionSourceIndex ray cone)
  intro smaller contained
  change Function.Bijective (fun scalar : Γ(fan.algebraicRealization 𝕜 regular, smaller) =>
    scalar • (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.res contained
      (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray cone))
  dsimp only [wallRestrictionAmbientFrame]
  rw [Scheme.Modules.res_res]
  exact frame smaller (contained.trans
    (congrArg (fun chosen => (fan.affineToricChartι 𝕜 regular chosen).opensRange)
      (fan.wallRestrictionSourceIndex_cone 𝕜 complete regular ray cone)).ge)

def wallRestrictionPulledFrame (cone : (fan.star ray).cones) :
    Γ((fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj,
      ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
        (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange) :=
  ((Scheme.Modules.pullback (fan.completeStarOrbitClosureMap 𝕜 complete regular ray)).obj
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj).res
    (fan.wallRestrictionMap_preimage_sourceChart 𝕜 complete regular ray cone).ge
    (BondalThomsen.amplePullbackLocalSection (fan.completeStarOrbitClosureMap 𝕜 complete regular ray)
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj _
      (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray cone))

theorem wallRestrictionPulledFrame_isFrame (cone : (fan.star ray).cones) :
    Scheme.Modules.IsFrame (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj
      ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
        (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange
      (fan.wallRestrictionPulledFrame 𝕜 complete regular divisor ray cone) := by
  have frame := BondalThomsen.amplePullbackLocalSection_isFrame
    (fan.completeStarOrbitClosureMap 𝕜 complete regular ray)
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj _ _
    (fan.wallRestrictionAmbientFrame_isFrame 𝕜 complete regular divisor ray cone)
  intro smaller contained
  change Function.Bijective (fun scalar : Γ((fan.star ray).algebraicRealization 𝕜
      (fan.star_isRegular complete regular ray), smaller) => scalar •
    ((Scheme.Modules.pullback (fan.completeStarOrbitClosureMap 𝕜 complete regular ray)).obj
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj).res contained
      (fan.wallRestrictionPulledFrame 𝕜 complete regular divisor ray cone))
  dsimp only [wallRestrictionPulledFrame]
  rw [Scheme.Modules.res_res]
  exact frame smaller (contained.trans
    (fan.wallRestrictionMap_preimage_sourceChart 𝕜 complete regular ray cone).ge)

def wallRestrictionQuotientFrame (reference cone : (fan.star ray).cones) :
    Γ((fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj,
      ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
        (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange) := by
  letI := (fan.star ray).algebraicRealization_isIntegral 𝕜
    (fan.star_isRegular complete regular ray) (fan.star_cones_nonempty_of_isComplete complete ray)
  exact BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrame
    (((fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference).neg 𝕜).cartierEquationAtlas 𝕜
      (fan.star_cones_nonempty_of_isComplete complete ray)) cone

theorem wallRestrictionQuotientFrame_isFrame (reference cone : (fan.star ray).cones) :
    Scheme.Modules.IsFrame (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj
      ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
        (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange
      (fan.wallRestrictionQuotientFrame 𝕜 complete regular divisor ray reference cone) := by
  let := (fan.star ray).algebraicRealization_isIntegral 𝕜
    (fan.star_isRegular complete regular ray) (fan.star_cones_nonempty_of_isComplete complete ray)
  exact BondalThomsen.wallCartierAtlasFrame_isFrame _ _

def wallRestrictionChartIso (reference cone : (fan.star ray).cones) :
    (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj.over
        ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
          (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange ≅
      (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj.over
        ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
          (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange := by
  let quotientMap := BondalThomsen.ampleLocalFrameHom _ _
    (fan.wallRestrictionQuotientFrame 𝕜 complete regular divisor ray reference cone)
  let pulledMap := BondalThomsen.ampleLocalFrameHom _ _
    (fan.wallRestrictionPulledFrame 𝕜 complete regular divisor ray cone)
  letI := BondalThomsen.ampleLocalFrameHom_isIso _ _ _
    (fan.wallRestrictionQuotientFrame_isFrame 𝕜 complete regular divisor ray reference cone)
  letI := BondalThomsen.ampleLocalFrameHom_isIso _ _ _
    (fan.wallRestrictionPulledFrame_isFrame 𝕜 complete regular divisor ray cone)
  exact (asIso quotientMap).symm ≪≫ asIso pulledMap

theorem wallRestrictionQuotientCharacter_agree (reference first second : (fan.star ray).cones)
    (quotientRay : (fan.star ray).Ray)
    (firstContains : fan.starEmbedding ray quotientRay.val ∈
      (fan.wallRestrictionQuotientCone complete regular ray first).val)
    (secondContains : fan.starEmbedding ray quotientRay.val ∈
      (fan.wallRestrictionQuotientCone complete regular ray second).val) :
    fan.wallRestrictionQuotientCharacter complete regular divisor ray reference first quotientRay.val =
      fan.wallRestrictionQuotientCharacter complete regular divisor ray reference second quotientRay.val := by
  have positive := fan.wallRestrictionQuotientCharacter_dualSemigroup
    complete regular divisor ray reference first second
  have negative := fan.wallRestrictionQuotientCharacter_dualSemigroup
    complete regular divisor ray reference second first
  have firstBound := (fan.star ray).dualSemigroup_rayValue_nonnegative quotientRay
    (fan.wallRestrictionQuotientCone complete regular ray first ⊓
      fan.wallRestrictionQuotientCone complete regular ray second).val
    ⟨firstContains, secondContains⟩ ⟨_, positive⟩
  have secondBound := (fan.star ray).dualSemigroup_rayValue_nonnegative quotientRay
    (fan.wallRestrictionQuotientCone complete regular ray second ⊓
      fan.wallRestrictionQuotientCone complete regular ray first).val
    ⟨secondContains, firstContains⟩ ⟨_, negative⟩
  change 0 ≤ fan.wallRestrictionQuotientCharacter complete regular divisor ray reference first
    quotientRay.val - fan.wallRestrictionQuotientCharacter complete regular divisor ray reference second
    quotientRay.val at firstBound
  change 0 ≤ fan.wallRestrictionQuotientCharacter complete regular divisor ray reference second
    quotientRay.val - fan.wallRestrictionQuotientCharacter complete regular divisor ray reference first
    quotientRay.val at secondBound
  omega

def wallRestrictionInvariantDivisor (reference : (fan.star ray).cones) :
    (fan.star ray).InvariantRayDivisor :=
  (fan.star ray).invariantDivisorOfCoefficients (fun quotientRay =>
    -fan.wallRestrictionQuotientCharacter complete regular divisor ray reference
      ⟨PointedCone.hull ℝ {fan.starEmbedding ray quotientRay.val}, quotientRay.property.2⟩
      quotientRay.val)

theorem wallRestrictionInvariantDivisor_apply (reference cone : (fan.star ray).cones)
    (quotientRay : (fan.star ray).Ray)
    (contains : fan.starEmbedding ray quotientRay.val ∈
      (fan.wallRestrictionQuotientCone complete regular ray cone).val) :
    fan.wallRestrictionInvariantDivisor complete regular divisor ray reference quotientRay =
      -fan.wallRestrictionQuotientCharacter complete regular divisor ray reference cone quotientRay.val := by
  change -fan.wallRestrictionQuotientCharacter complete regular divisor ray reference
    ⟨PointedCone.hull ℝ {fan.starEmbedding ray quotientRay.val}, quotientRay.property.2⟩
      quotientRay.val = _
  apply congrArg Neg.neg
  exact fan.wallRestrictionQuotientCharacter_agree complete regular divisor ray reference _ _ quotientRay
    ((fan.wallRestrictionQuotientCone_above complete regular ray _).le
      (PointedCone.subset_hull (Set.mem_singleton _))) contains

theorem wallRestrictionCharacterAtlas_presentsDivisor (reference : (fan.star ray).cones) :
    (fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference).PresentsDivisor 𝕜
      (fan.wallRestrictionInvariantDivisor complete regular divisor ray reference) := by
  intro cone quotientRay contains
  change fan.wallRestrictionQuotientCharacter complete regular divisor ray reference cone
    quotientRay.val = -fan.wallRestrictionInvariantDivisor complete regular divisor ray reference quotientRay
  rw [fan.wallRestrictionInvariantDivisor_apply complete regular divisor ray reference cone
    quotientRay contains, neg_neg]

def wallRestrictionLineBundleIsoInvariantDivisor (reference : (fan.star ray).cones) :
    (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj ≅
      ((fan.star ray).invariantDivisorLineBundle 𝕜
        (fan.star_isComplete_of_isComplete complete ray) (fan.star_isRegular complete regular ray)
        (fan.wallRestrictionInvariantDivisor complete regular divisor ray reference)).obj :=
  (fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference).invariantDivisorLineBundleIso 𝕜
    (fan.star_isComplete_of_isComplete complete ray) _
    (fan.wallRestrictionCharacterAtlas_presentsDivisor 𝕜 complete regular divisor ray reference)

theorem wallRestrictionOverlapCone_projected (first second : (fan.star ray).cones) :
    PointedCone.map (fan.starProjection ray)
        (fan.wallRestrictionSourceCone complete regular ray first ⊓
          fan.wallRestrictionSourceCone complete regular ray second).val =
      (fan.wallRestrictionQuotientCone complete regular ray first ⊓
        fan.wallRestrictionQuotientCone complete regular ray second).val := by
  exact BondalThomsen.rayQuotient_map_inf _ _ _
    (fan.wallRestrictionSourceCone_contains complete regular ray first)
    (fan.wallRestrictionSourceCone_contains complete regular ray second)

def wallRestrictionAmbientOverlapUnit (first second : (fan.star ray).cones) :
    (affineCoordinateRing 𝕜 fan.lattice
      (fan.wallRestrictionSourceCone complete regular ray first ⊓
        fan.wallRestrictionSourceCone complete regular ray second).val)ˣ :=
  fan.coneDivisorTransitionUnit 𝕜
    (fan.divisorChartBasis complete regular (fan.starConeLift ray first)).val.2
    (fan.divisorChartBasis complete regular (fan.starConeLift ray first)).property.1
    (fan.divisorChartBasis complete regular (fan.starConeLift ray second)).val.2
    (fan.divisorChartBasis complete regular (fan.starConeLift ray second)).property.1 divisor

theorem wallRestrictionOverlapUnit_pullback (reference first second : (fan.star ray).cones) :
    (RingEquiv.cast (R := fun chosen => affineCoordinateRing 𝕜 (fan.star ray).lattice chosen)
      (fan.wallRestrictionOverlapCone_projected complete regular ray first second))
      ((Units.map (fan.rayFaceCoordinateRingMap 𝕜 ray
        (fan.wallRestrictionSourceCone complete regular ray first ⊓
          fan.wallRestrictionSourceCone complete regular ray second).val
        ⟨fan.wallRestrictionSourceCone_contains complete regular ray first,
          fan.wallRestrictionSourceCone_contains complete regular ray second⟩).toMonoidHom
        (fan.wallRestrictionAmbientOverlapUnit 𝕜 complete regular divisor ray first second)) :
          affineCoordinateRing 𝕜 (fan.star ray).lattice
            (PointedCone.map (fan.starProjection ray)
              (fan.wallRestrictionSourceCone complete regular ray first ⊓
                fan.wallRestrictionSourceCone complete regular ray second).val)) =
      (toricMonomialUnit 𝕜 (fan.star ray).lattice _
        (fan.wallRestrictionQuotientCharacter complete regular divisor ray reference first -
          fan.wallRestrictionQuotientCharacter complete regular divisor ray reference second)
        (fan.wallRestrictionQuotientCharacter_dualSemigroup complete regular divisor ray reference first second)
        (by
          rw [neg_sub]
          simpa only [inf_comm] using fan.wallRestrictionQuotientCharacter_dualSemigroup
            complete regular divisor ray reference second first) :
        affineCoordinateRing 𝕜 (fan.star ray).lattice
          (fan.wallRestrictionQuotientCone complete regular ray first ⊓
            fan.wallRestrictionQuotientCone complete regular ray second).val) := by
  have positive := (fan.coneDivisorCharacter_transition_dualSemigroup
    (fan.divisorChartBasis complete regular (fan.starConeLift ray first)).val.2
    (fan.divisorChartBasis complete regular (fan.starConeLift ray first)).property.1
    (fan.divisorChartBasis complete regular (fan.starConeLift ray second)).val.2
    (fan.divisorChartBasis complete regular (fan.starConeLift ray second)).property.1 divisor).1
  have vanishes : (fan.wallRestrictionSourceCharacter complete regular divisor ray first -
      fan.wallRestrictionSourceCharacter complete regular divisor ray second) ray.val = 0 := by
    simp only [AddMonoidHom.sub_apply, wallRestrictionSourceCharacter_ray, sub_self]
  have monomial := fan.rayFaceCoordinateRingMap_single_of_zero 𝕜 ray
    (fan.wallRestrictionSourceCone complete regular ray first ⊓
      fan.wallRestrictionSourceCone complete regular ray second).val
    ⟨fan.wallRestrictionSourceCone_contains complete regular ray first,
      fan.wallRestrictionSourceCone_contains complete regular ray second⟩ ⟨_, positive⟩ vanishes
  change (RingEquiv.cast _)
    ((fan.rayFaceCoordinateRingMap 𝕜 ray _ _) (MonoidAlgebra.single
      (ofAdd (⟨_, positive⟩ : dualSemigroup fan.lattice _)) 1)) = _
  refine (congrArg (RingEquiv.cast
    (R := fun chosen => affineCoordinateRing 𝕜 (fan.star ray).lattice chosen)
    (fan.wallRestrictionOverlapCone_projected complete regular ray first second)) monomial).trans ?_
  have transport : ∀ (targetCone : PointedCone ℝ (fan.StarAmbient ray))
      (equality : PointedCone.map (fan.starProjection ray)
        (fan.wallRestrictionSourceCone complete regular ray first ⊓
          fan.wallRestrictionSourceCone complete regular ray second).val = targetCone)
      (member : fan.wallRestrictionQuotientCharacter complete regular divisor ray reference first -
        fan.wallRestrictionQuotientCharacter complete regular divisor ray reference second ∈
          dualSemigroup (fan.star ray).lattice targetCone),
      (RingEquiv.cast (R := fun chosen => affineCoordinateRing 𝕜 (fan.star ray).lattice chosen) equality)
          (MonoidAlgebra.single (ofAdd (fan.rayFaceQuotientCharacter ray _ ⟨_, positive⟩ vanishes)) 1) =
        MonoidAlgebra.single (ofAdd (⟨_, member⟩ : dualSemigroup (fan.star ray).lattice targetCone)) 1 := by
    intro targetCone equality member
    subst targetCone
    change MonoidAlgebra.single _ 1 = MonoidAlgebra.single _ 1
    congr 2
    apply Subtype.ext
    exact (fan.wallRestrictionQuotientCharacter_difference complete regular divisor ray reference first second).symm
  exact transport _ _ _

end TauCeti.Toric.Fan
