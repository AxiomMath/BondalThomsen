module

public import BondalThomsen.Toric.Surface.WallCartierRestriction
public import BondalThomsen.ProjectiveBundle.GlobalRelativeQuotient
public import BondalThomsen.Toric.Projective.GlobalSheafIso

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

theorem wallAppLE_transport_target {source target : Scheme}
    (map : source ⟶ target) (first second : target.Opens) (equal : first = second)
    (domain : source.Opens) (inFirst : domain ≤ map ⁻¹ᵁ first)
    (inSecond : domain ≤ map ⁻¹ᵁ second) (sectionValue : Γ(target, first)) :
    map.appLE second domain inSecond
        (target.presheaf.map (eqToHom equal.symm).op sectionValue) =
      map.appLE first domain inFirst sectionValue := by
  cases equal
  simp

theorem wallOpenSectionTransport_comp (scheme : Scheme) (first middle last : scheme.Opens)
    (firstEquality : first = middle) (secondEquality : middle = last)
    (sectionValue : Γ(scheme, first)) :
    scheme.presheaf.map (eqToHom secondEquality.symm).op
        (scheme.presheaf.map (eqToHom firstEquality.symm).op sectionValue) =
      scheme.presheaf.map (eqToHom (firstEquality.trans secondEquality).symm).op sectionValue := by
  subst middle
  subst last
  simp

theorem wallAppLE_transport_source {source target : Scheme}
    (map : source ⟶ target) (targetOpen : target.Opens) (first second : source.Opens)
    (equal : first = second) (inFirst : first ≤ map ⁻¹ᵁ targetOpen)
    (inSecond : second ≤ map ⁻¹ᵁ targetOpen) (sectionValue : Γ(target, targetOpen)) :
    map.appLE targetOpen second inSecond sectionValue =
      source.presheaf.map (eqToHom equal.symm).op
        (map.appLE targetOpen first inFirst sectionValue) := by
  cases equal
  simp [Scheme.Hom.appLE]

theorem wallPullbackLocalSection_coefficient {source target : Scheme}
    (map : source ⟶ target) (sheaf : target.Modules)
    (openSet : target.Opens) (first second : Γ(sheaf, openSet))
    (scalar : Γ(target, openSet)) (relation : second = scalar • first)
    (domain : source.Opens) (contained : domain ≤ map ⁻¹ᵁ openSet) :
    ((Scheme.Modules.pullback map).obj sheaf).res contained
        (amplePullbackLocalSection map sheaf openSet second) =
      map.appLE openSet domain contained scalar •
        ((Scheme.Modules.pullback map).obj sheaf).res contained
          (amplePullbackLocalSection map sheaf openSet first) := by
  rw [relation]
  unfold amplePullbackLocalSection
  rw [Scheme.Modules.Hom.app_smul]
  change ((Scheme.Modules.pullback map).obj sheaf).presheaf.map (homOfLE contained).op
    (map.app openSet scalar • _) = _
  rw [Scheme.Modules.map_smul]
  rfl

theorem wallPullbackLocalSection_restriction {source target : Scheme}
    (map : source ⟶ target) (sheaf : target.Modules)
    {smaller larger : target.Opens} (contained : smaller ≤ larger)
    (sectionValue : Γ(sheaf, larger)) (domain : source.Opens)
    (inSmaller : domain ≤ map ⁻¹ᵁ smaller) :
    ((Scheme.Modules.pullback map).obj sheaf).res
        (inSmaller.trans (map.preimage_mono contained))
        (amplePullbackLocalSection map sheaf larger sectionValue) =
      ((Scheme.Modules.pullback map).obj sheaf).res inSmaller
        (amplePullbackLocalSection map sheaf smaller (sheaf.res contained sectionValue)) := by
  rw [← amplePullbackLocalSection_res, Scheme.Modules.res_res]

theorem wallFrameTransition_restrict {scheme : Scheme} (sheaf : scheme.Modules)
    (first second : scheme.Opens) (firstFrame : Γ(sheaf, first))
    (secondFrame : Γ(sheaf, second)) (scalar : Γ(scheme, first ⊓ second))
    (relation : sheaf.res inf_le_right secondFrame = scalar • sheaf.res inf_le_left firstFrame)
    (smaller : scheme.Opens) (contained : smaller ≤ first ⊓ second) :
    sheaf.res (contained.trans inf_le_right) secondFrame =
      scheme.presheaf.map (homOfLE contained).op scalar •
        sheaf.res (contained.trans inf_le_left) firstFrame := by
  have restricted := congrArg (sheaf.res contained) relation
  change sheaf.presheaf.map (homOfLE contained).op _ =
    sheaf.presheaf.map (homOfLE contained).op _ at restricted
  rw [Scheme.Modules.map_smul] at restricted
  change sheaf.res contained (sheaf.res inf_le_right secondFrame) =
    _ • sheaf.res contained (sheaf.res inf_le_left firstFrame) at restricted
  rw [Scheme.Modules.res_res, Scheme.Modules.res_res] at restricted
  exact restricted

theorem wallLocalFrameHom_one {scheme : Scheme} (sheaf : scheme.Modules)
    (openSet : scheme.Opens) (frame : Γ(sheaf, openSet))
    (smaller : scheme.Opens) (contained : smaller ≤ openSet) :
    (ampleLocalFrameHom sheaf openSet frame).val.app (op (Over.mk (homOfLE contained)))
      (1 : Γ(scheme, smaller)) = sheaf.res contained frame := by
  rw [ampleLocalFrameHom_app, one_smul]
  rfl

theorem wallLocalFrameComparison_frame {scheme : Scheme}
    (source target : scheme.Modules) (openSet : scheme.Opens)
    (sourceFrame : Γ(source, openSet)) (targetFrame : Γ(target, openSet))
    (sourceIsFrame : Scheme.Modules.IsFrame source openSet sourceFrame)
    (targetIsFrame : Scheme.Modules.IsFrame target openSet targetFrame)
    (smaller : scheme.Opens) (contained : smaller ≤ openSet) :
    letI := ampleLocalFrameHom_isIso source openSet sourceFrame sourceIsFrame
    letI := ampleLocalFrameHom_isIso target openSet targetFrame targetIsFrame
    (((asIso (ampleLocalFrameHom source openSet sourceFrame)).symm ≪≫
        asIso (ampleLocalFrameHom target openSet targetFrame)).hom.val.app
          (op (Over.mk (homOfLE contained)))) (source.res contained sourceFrame) =
      target.res contained targetFrame := by
  let := ampleLocalFrameHom_isIso source openSet sourceFrame sourceIsFrame
  let := ampleLocalFrameHom_isIso target openSet targetFrame targetIsFrame
  let subopen : Over openSet := Over.mk (homOfLE contained)
  have inverseComponent := congrArg (fun morphism :
      SheafOfModules.unit (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over openSet)) ⟶
        SheafOfModules.unit (TauCeti.SheafOfModules.ringCatSheaf (scheme.sheaf.over openSet)) =>
      morphism.val.app (op subopen) (1 : Γ(scheme, smaller)))
    (asIso (ampleLocalFrameHom source openSet sourceFrame)).hom_inv_id
  simp only [asIso_hom, asIso_inv, SheafOfModules.comp_val, SheafOfModules.id_val,
    PresheafOfModules.comp_app, PresheafOfModules.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at inverseComponent
  change (inv (ampleLocalFrameHom source openSet sourceFrame)).val.app
    (op (Over.mk (homOfLE contained)))
      ((ampleLocalFrameHom source openSet sourceFrame).val.app
        (op (Over.mk (homOfLE contained))) (1 : Γ(scheme, smaller))) =
      (1 : Γ(scheme, smaller)) at inverseComponent
  rw [wallLocalFrameHom_one] at inverseComponent
  change (ampleLocalFrameHom target openSet targetFrame).val.app
    (op (Over.mk (homOfLE contained)))
      ((inv (ampleLocalFrameHom source openSet sourceFrame)).val.app
        (op (Over.mk (homOfLE contained))) (source.res contained sourceFrame)) = _
  exact (congrArg (fun scalar : Γ(scheme, smaller) =>
    (ampleLocalFrameHom target openSet targetFrame).val.app
      (op (Over.mk (homOfLE contained))) scalar) inverseComponent).trans
    (wallLocalFrameHom_one _ _ _ _ _)

theorem wallCartierFrame_transition_on {scheme : Scheme} [IsIntegral scheme]
    (atlas : CartierEquationAtlas scheme) (first second : atlas.Index)
    (domain : scheme.Opens) [Nonempty domain]
    (inFirst : domain ≤ atlas.chart first) (inSecond : domain ≤ atlas.chart second)
    (unit : Γ(scheme, domain)ˣ)
    (equation : TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField scheme domain unit *
      atlas.equation second = atlas.equation first) :
    atlas.invertibleSheaf.obj.res inSecond (CanonicalNegativeRaySum.cartierAtlasFrame atlas second) =
      unit.val • atlas.invertibleSheaf.obj.res inFirst
        (CanonicalNegativeRaySum.cartierAtlasFrame atlas first) := by
  open TauCeti.AlgebraicGeometry.Scheme in
    apply CartierDivisor.sheafι_app_injective atlas.cartierDivisor domain
    apply (rationalFunctionsEquiv domain).injective
    have firstValue := CanonicalNegativeRaySum.cartierAtlasFrame_restriction_rational
      atlas first domain inFirst
    have secondValue := CanonicalNegativeRaySum.cartierAtlasFrame_restriction_rational
      atlas second domain inSecond
    have scalarEquation := congrArg Units.val equation
    change scheme.germToFunctionField domain unit.val * (atlas.equation second).val =
      (atlas.equation first).val at scalarEquation
    change rationalFunctionsEquiv domain
        (atlas.cartierDivisor.sheafι.val.app (op domain)
          (CanonicalNegativeRaySum.cartierAtlasFrameRestriction atlas second domain inSecond)) =
      rationalFunctionsEquiv domain
        (atlas.cartierDivisor.sheafι.val.app (op domain)
          (unit.val • CanonicalNegativeRaySum.cartierAtlasFrameRestriction atlas first domain inFirst))
    rw [(atlas.cartierDivisor.sheafι.val.app (op domain)).hom.map_smul,
      (rationalFunctionsEquiv domain).map_smul, firstValue, secondValue]
    change (atlas.equation second)⁻¹.val =
      scheme.germToFunctionField domain unit.val * (atlas.equation first)⁻¹.val
    apply (Units.eq_mul_inv_iff_mul_eq (atlas.equation first)).mpr
    calc
      (atlas.equation second)⁻¹.val * (atlas.equation first).val =
          (atlas.equation second)⁻¹.val *
            (scheme.germToFunctionField domain unit.val * (atlas.equation second).val) :=
        congrArg _ scalarEquation.symm
      _ = scheme.germToFunctionField domain unit.val := by
        rw [mul_left_comm, Units.inv_mul, mul_one]

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance wallDescentRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray)

variable {𝕜} in
local instance wallDescentBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def wallDescentSourceOpen (cone : (fan.star ray).cones) : (fan.algebraicRealization 𝕜 regular).Opens :=
  (fan.affineToricChartι 𝕜 regular (fan.wallRestrictionSourceCone complete regular ray cone)).opensRange

def wallDescentQuotientOpen (cone : (fan.star ray).cones) :
    ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray)).Opens :=
  ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
    (fan.wallRestrictionQuotientCone complete regular ray cone)).opensRange

theorem wallDescent_preimage_overlap (first second : (fan.star ray).cones) :
    fan.completeStarOrbitClosureMap 𝕜 complete regular ray ⁻¹ᵁ
        (fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentSourceOpen 𝕜 complete regular ray second) =
      fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
        fan.wallDescentQuotientOpen 𝕜 complete regular ray second := by
  rw [Scheme.Hom.preimage_inf, wallDescentSourceOpen, wallDescentSourceOpen,
    fan.wallRestrictionMap_preimage_sourceChart 𝕜, fan.wallRestrictionMap_preimage_sourceChart 𝕜]
  rfl

theorem wallDescentChartIso_frame (reference cone : (fan.star ray).cones)
    (smaller : ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray)).Opens)
    (contained : smaller ≤ fan.wallDescentQuotientOpen 𝕜 complete regular ray cone) :
    (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference cone).hom.val.app
        (op (Over.mk (homOfLE contained)))
        ((fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj.res contained
          (fan.wallRestrictionQuotientFrame 𝕜 complete regular divisor ray reference cone)) =
      (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj.res contained
        (fan.wallRestrictionPulledFrame 𝕜 complete regular divisor ray cone) := by
  exact BondalThomsen.wallLocalFrameComparison_frame _ _ _ _ _
    (fan.wallRestrictionQuotientFrame_isFrame 𝕜 complete regular divisor ray reference cone)
    (fan.wallRestrictionPulledFrame_isFrame 𝕜 complete regular divisor ray cone) _ _

def wallDescentProjectedCone (cone : fan.cones) (contains : embedding ray.val ∈ cone.val) :
    (fan.star ray).cones :=
  ⟨PointedCone.map (fan.starProjection ray) cone.val, ⟨cone.val, ⟨cone.property, contains⟩, rfl⟩⟩

omit [FiniteDimensional ℝ Ambient] in
theorem wallDescentProjectedCone_lift (cone : fan.cones)
    (contains : embedding ray.val ∈ cone.val) :
    fan.starConeLift ray (fan.wallDescentProjectedCone ray cone contains) = cone :=
  fan.starConeLift_eq_of_projected ray _ cone contains rfl

theorem wallDescentProjectedChart_factorization (cone : fan.cones)
    (contains : embedding ray.val ∈ cone.val) :
    (fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
        (fan.wallDescentProjectedCone ray cone contains) ≫
        fan.completeStarOrbitClosureMap 𝕜 complete regular ray =
      fan.rayFaceAffineSchemeMap 𝕜 ray cone.val contains ≫ fan.affineToricChartι 𝕜 regular cone := by
  let quotientCone := fan.wallDescentProjectedCone ray cone contains
  have factorization := fan.affineToricChartι_comp_starOrbitClosureMap 𝕜 regular ray
    (fan.star_isRegular complete regular ray) quotientCone
  have transport : ∀ (original : fan.cones) (originalContains : embedding ray.val ∈ original.val)
      (projected : PointedCone.map (fan.starProjection ray) original.val = quotientCone.val),
      fan.rayFaceChartMap 𝕜 ray quotientCone ≫
          fan.affineToricChartι 𝕜 regular (fan.starConeLift ray quotientCone) =
        (eqToHom (congrArg (affineToricScheme 𝕜 (fan.star ray).lattice) projected.symm) ≫
          fan.rayFaceAffineSchemeMap 𝕜 ray original.val originalContains) ≫
            fan.affineToricChartι 𝕜 regular original := by
    intro original originalContains projected
    have equality := fan.starConeLift_eq_of_projected ray quotientCone original originalContains projected
    subst original
    rfl
  exact factorization.trans (by simpa only [eqToHom_refl, Category.id_comp] using
    (transport cone contains rfl))

theorem wallDescentProjectedChart_preimage (cone : fan.cones)
    (contains : embedding ray.val ∈ cone.val) :
    fan.completeStarOrbitClosureMap 𝕜 complete regular ray ⁻¹ᵁ
        (fan.affineToricChartι 𝕜 regular cone).opensRange =
      ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
        (fan.wallDescentProjectedCone ray cone contains)).opensRange := by
  apply Opens.ext
  change (fan.starOrbitClosureMap 𝕜 regular ray (fan.star_isRegular complete regular ray)) ⁻¹'
    Set.range (fan.affineToricChartι 𝕜 regular cone) = _
  have equality := fan.starOrbitClosureMap_preimage_lifted_chart 𝕜 regular ray
    (fan.star_isRegular complete regular ray) (fan.wallDescentProjectedCone ray cone contains)
  rw [fan.wallDescentProjectedCone_lift ray cone contains] at equality
  exact equality

theorem wallDescentProjectedChart_appLE (cone : fan.cones)
    (contains : embedding ray.val ∈ cone.val) (coordinate : affineCoordinateRing 𝕜 fan.lattice cone.val) :
    (fan.completeStarOrbitClosureMap 𝕜 complete regular ray).appLE
        (fan.affineToricChartι 𝕜 regular cone).opensRange
        ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray)
          (fan.wallDescentProjectedCone ray cone contains)).opensRange
        (fan.wallDescentProjectedChart_preimage 𝕜 complete regular ray cone contains).ge
        (fan.chartCoordinateSectionsEquiv 𝕜 regular cone coordinate) =
      (fan.star ray).chartCoordinateSectionsEquiv 𝕜 (fan.star_isRegular complete regular ray)
        (fan.wallDescentProjectedCone ray cone contains)
        (fan.rayFaceCoordinateRingMap 𝕜 ray cone.val contains coordinate) := by
  let sourceInclusion := (fan.star ray).affineToricChartι 𝕜
    (fan.star_isRegular complete regular ray) (fan.wallDescentProjectedCone ray cone contains)
  let targetInclusion := fan.affineToricChartι 𝕜 regular cone
  let chartMap := fan.rayFaceAffineSchemeMap 𝕜 ray cone.val contains
  have chartSections := BondalThomsen.wallChartSections_appLE sourceInclusion targetInclusion
    (fan.completeStarOrbitClosureMap 𝕜 complete regular ray) chartMap
    (fan.wallDescentProjectedChart_factorization 𝕜 complete regular ray cone contains)
    (fan.wallDescentProjectedChart_preimage 𝕜 complete regular ray cone contains).ge
    ((Scheme.ΓSpecIso _).inv coordinate)
  have naturality := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (fan.rayFaceCoordinateRingMap 𝕜 ray cone.val contains).toRingHom)
  have affineSections := (ConcreteCategory.congr_hom naturality coordinate).symm
  simp only [ConcreteCategory.comp_apply] at affineSections
  exact chartSections.trans (congrArg (fun value =>
    (IsOpenImmersion.ΓIsoTop sourceInclusion).hom value) affineSections)

theorem wallDescentChartCoordinate_cast (first second : (fan.star ray).cones)
    (equality : first = second) (coordinate : affineCoordinateRing 𝕜 (fan.star ray).lattice first.val) :
    ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray)).presheaf.map
        (eqToHom (congrArg (fun chosen : (fan.star ray).cones =>
          ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray) chosen).opensRange)
          equality).symm).op
        ((fan.star ray).chartCoordinateSectionsEquiv 𝕜 (fan.star_isRegular complete regular ray) first coordinate) =
      (fan.star ray).chartCoordinateSectionsEquiv 𝕜 (fan.star_isRegular complete regular ray) second
        ((RingEquiv.cast (R := fun chosen => affineCoordinateRing 𝕜 (fan.star ray).lattice chosen)
          (congrArg Subtype.val equality)) coordinate) := by
  subst second
  simp

theorem wallDescentOverlapProjectedCone (first second : (fan.star ray).cones) :
    fan.wallDescentProjectedCone ray
        (fan.wallRestrictionSourceCone complete regular ray first ⊓
          fan.wallRestrictionSourceCone complete regular ray second)
        ⟨fan.wallRestrictionSourceCone_contains complete regular ray first,
          fan.wallRestrictionSourceCone_contains complete regular ray second⟩ =
      fan.wallRestrictionQuotientCone complete regular ray first ⊓
        fan.wallRestrictionQuotientCone complete regular ray second := by
  apply Subtype.ext
  exact fan.wallRestrictionOverlapCone_projected complete regular ray first second

def wallDescentAmbientTransition (first second : (fan.star ray).cones) :
    Γ(fan.algebraicRealization 𝕜 regular,
      fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
        fan.wallDescentSourceOpen 𝕜 complete regular ray second)ˣ :=
  Units.map ((fan.algebraicRealization 𝕜 regular).presheaf.map
    (eqToHom (fan.chart_opensRange_intersection 𝕜 regular
      (fan.wallRestrictionSourceCone complete regular ray first)
      (fan.wallRestrictionSourceCone complete regular ray second)).symm).op).hom.toMonoidHom
    (Units.map (fan.chartCoordinateSectionsEquiv 𝕜 regular
      (fan.wallRestrictionSourceCone complete regular ray first ⊓
        fan.wallRestrictionSourceCone complete regular ray second)).toMonoidHom
      (fan.wallRestrictionAmbientOverlapUnit 𝕜 complete regular divisor ray first second))

def wallDescentQuotientTransition (reference first second : (fan.star ray).cones) :
    Γ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray),
      fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
        fan.wallDescentQuotientOpen 𝕜 complete regular ray second)ˣ :=
  (fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference).transition 𝕜 first second

theorem wallDescentTransition_pullback (reference first second : (fan.star ray).cones) :
    (fan.completeStarOrbitClosureMap 𝕜 complete regular ray).appLE
        (fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentSourceOpen 𝕜 complete regular ray second)
        (fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentQuotientOpen 𝕜 complete regular ray second)
        (fan.wallDescent_preimage_overlap 𝕜 complete regular ray first second).ge
        (fan.wallDescentAmbientTransition 𝕜 complete regular divisor ray first second) =
      (fan.wallDescentQuotientTransition 𝕜 complete regular divisor ray reference first second) := by
  let ambientCone := fan.wallRestrictionSourceCone complete regular ray first ⊓
    fan.wallRestrictionSourceCone complete regular ray second
  let contains : embedding ray.val ∈ ambientCone.val :=
    ⟨fan.wallRestrictionSourceCone_contains complete regular ray first,
      fan.wallRestrictionSourceCone_contains complete regular ray second⟩
  let projectedCone := fan.wallDescentProjectedCone ray ambientCone contains
  let quotientCone := fan.wallRestrictionQuotientCone complete regular ray first ⊓
    fan.wallRestrictionQuotientCone complete regular ray second
  have coneEquality : projectedCone = quotientCone :=
    fan.wallDescentOverlapProjectedCone complete regular ray first second
  let ambientOpen := (fan.affineToricChartι 𝕜 regular ambientCone).opensRange
  let projectedOpen := ((fan.star ray).affineToricChartι 𝕜
    (fan.star_isRegular complete regular ray) projectedCone).opensRange
  let quotientOpen := ((fan.star ray).affineToricChartι 𝕜
    (fan.star_isRegular complete regular ray) quotientCone).opensRange
  let targetOverlap := fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
    fan.wallDescentSourceOpen 𝕜 complete regular ray second
  let sourceOverlap := fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
    fan.wallDescentQuotientOpen 𝕜 complete regular ray second
  have targetEquality : ambientOpen = targetOverlap :=
    fan.chart_opensRange_intersection 𝕜 regular _ _
  have projectedEquality : projectedOpen = quotientOpen := congrArg
    (fun chosen : (fan.star ray).cones =>
      ((fan.star ray).affineToricChartι 𝕜 (fan.star_isRegular complete regular ray) chosen).opensRange)
    coneEquality
  have sourceEquality : quotientOpen = sourceOverlap :=
    (fan.star ray).chart_opensRange_intersection 𝕜 (fan.star_isRegular complete regular ray) _ _
  have projectedContained : projectedOpen ≤
      fan.completeStarOrbitClosureMap 𝕜 complete regular ray ⁻¹ᵁ ambientOpen :=
    (fan.wallDescentProjectedChart_preimage 𝕜 complete regular ray ambientCone contains).ge
  have sourceContained : sourceOverlap ≤
      fan.completeStarOrbitClosureMap 𝕜 complete regular ray ⁻¹ᵁ ambientOpen := by
    rw [targetEquality]
    exact (fan.wallDescent_preimage_overlap 𝕜 complete regular ray first second).ge
  let coordinate : affineCoordinateRing 𝕜 fan.lattice ambientCone.val :=
    fan.wallRestrictionAmbientOverlapUnit 𝕜 complete regular divisor ray first second
  have pullback := fan.wallDescentProjectedChart_appLE 𝕜 complete regular ray ambientCone contains coordinate
  have transportSource := BondalThomsen.wallAppLE_transport_source
    (fan.completeStarOrbitClosureMap 𝕜 complete regular ray) ambientOpen projectedOpen sourceOverlap
    (projectedEquality.trans sourceEquality) projectedContained sourceContained
    (fan.chartCoordinateSectionsEquiv 𝕜 regular ambientCone coordinate)
  have transportTarget := BondalThomsen.wallAppLE_transport_target
    (fan.completeStarOrbitClosureMap 𝕜 complete regular ray) ambientOpen targetOverlap targetEquality
    sourceOverlap sourceContained (fan.wallDescent_preimage_overlap 𝕜 complete regular ray first second).ge
    (fan.chartCoordinateSectionsEquiv 𝕜 regular ambientCone coordinate)
  change (fan.completeStarOrbitClosureMap 𝕜 complete regular ray).appLE targetOverlap sourceOverlap _
    ((fan.algebraicRealization 𝕜 regular).presheaf.map (eqToHom targetEquality.symm).op
      (fan.chartCoordinateSectionsEquiv 𝕜 regular ambientCone coordinate)) = _
  rw [transportTarget, transportSource, pullback]
  have castSections := fan.wallDescentChartCoordinate_cast 𝕜 complete regular ray projectedCone quotientCone
    coneEquality (fan.rayFaceCoordinateRingMap 𝕜 ray ambientCone.val contains coordinate)
  have mappedCast := congrArg (fun sectionValue =>
    ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray)).presheaf.map
      (eqToHom sourceEquality.symm).op sectionValue) castSections
  have composed := BondalThomsen.wallOpenSectionTransport_comp
    ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray))
    projectedOpen quotientOpen sourceOverlap projectedEquality sourceEquality
    ((fan.star ray).chartCoordinateSectionsEquiv 𝕜 (fan.star_isRegular complete regular ray)
      projectedCone (fan.rayFaceCoordinateRingMap 𝕜 ray ambientCone.val contains coordinate))
  refine composed.symm.trans (mappedCast.trans ?_)
  have coordinateEquality := fan.wallRestrictionOverlapUnit_pullback 𝕜 complete regular divisor ray
    reference first second
  exact congrArg (fun quotientCoordinate =>
    ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray)).presheaf.map
      (eqToHom sourceEquality.symm).op
      ((fan.star ray).chartCoordinateSectionsEquiv 𝕜 (fan.star_isRegular complete regular ray)
        quotientCone quotientCoordinate)) coordinateEquality

omit [FiniteDimensional ℝ Ambient] in
theorem wallDescentCharacterAtlas_neg_transition {fan : Fan embedding} {regular : fan.IsRegular}
    (atlas : CharacterEquationAtlas 𝕜 fan regular) (first second : atlas.Index) :
    (atlas.neg 𝕜).transition 𝕜 first second = (atlas.transition 𝕜 first second)⁻¹ := by
  unfold CharacterEquationAtlas.transition CharacterEquationAtlas.neg
  rw [← map_inv, ← map_inv]
  congr 2
  have characterEquality : -atlas.character first - -atlas.character second =
      -(atlas.character first - atlas.character second) := by abel
  apply Units.ext
  change MonoidAlgebra.single (ofAdd (⟨_, _⟩ : dualSemigroup fan.lattice _)) 1 = _
  change MonoidAlgebra.single _ 1 = MonoidAlgebra.single _ 1
  congr 2
  exact Subtype.ext characterEquality

theorem wallDescentQuotientFrame_transition (reference first second : (fan.star ray).cones) :
    (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj.res
        (inf_le_right : fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentQuotientOpen 𝕜 complete regular ray second ≤
            fan.wallDescentQuotientOpen 𝕜 complete regular ray second)
        (fan.wallRestrictionQuotientFrame 𝕜 complete regular divisor ray reference second) =
      ((fan.wallDescentQuotientTransition 𝕜 complete regular divisor ray reference first second)⁻¹).val •
        (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj.res
          (inf_le_left : fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
            fan.wallDescentQuotientOpen 𝕜 complete regular ray second ≤
              fan.wallDescentQuotientOpen 𝕜 complete regular ray first)
          (fan.wallRestrictionQuotientFrame 𝕜 complete regular divisor ray reference first) := by
  let := (fan.star ray).algebraicRealization_isIntegral 𝕜
    (fan.star_isRegular complete regular ray) (fan.star_cones_nonempty_of_isComplete complete ray)
  have transition := BondalThomsen.CanonicalNegativeRaySum.cartierAtlasFrame_transition
    (((fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference).neg 𝕜).cartierEquationAtlas 𝕜
      (fan.star_cones_nonempty_of_isComplete complete ray)) first second
  have unitEquality := wallDescentCharacterAtlas_neg_transition 𝕜
    (fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference) first second
  change ((fan.wallRestrictionCharacterAtlas 𝕜 complete regular divisor ray reference).neg 𝕜).transition 𝕜
      first second = _ at unitEquality
  simp only [CharacterEquationAtlas.cartierEquationAtlas] at transition
  rw [unitEquality] at transition
  exact transition

theorem wallDescentAmbientFrame_transition (first second : (fan.star ray).cones) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.res
        (inf_le_right : fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentSourceOpen 𝕜 complete regular ray second ≤
            fan.wallDescentSourceOpen 𝕜 complete regular ray second)
        (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray second) =
      (fan.wallDescentAmbientTransition 𝕜 complete regular divisor ray first second)⁻¹.val •
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.res
          (inf_le_left : fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
            fan.wallDescentSourceOpen 𝕜 complete regular ray second ≤
              fan.wallDescentSourceOpen 𝕜 complete regular ray first)
          (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray first) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let atlas := ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)
  let firstIndex := fan.wallRestrictionSourceIndex ray first
  let secondIndex := fan.wallRestrictionSourceIndex ray second
  let domain := fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
    fan.wallDescentSourceOpen 𝕜 complete regular ray second
  let common := fan.wallRestrictionSourceCone complete regular ray first ⊓
    fan.wallRestrictionSourceCone complete regular ray second
  let := fan.chartOpen_nonempty 𝕜 regular common
  let : Nonempty domain := by
    change Nonempty ↥((fan.affineToricChartι 𝕜 regular
      (fan.wallRestrictionSourceCone complete regular ray first)).opensRange ⊓
      (fan.affineToricChartι 𝕜 regular
        (fan.wallRestrictionSourceCone complete regular ray second)).opensRange)
    rw [← fan.chart_opensRange_intersection 𝕜 regular
      (fan.wallRestrictionSourceCone complete regular ray first)
      (fan.wallRestrictionSourceCone complete regular ray second)]
    exact fan.chartOpen_nonempty 𝕜 regular _
  let : Nonempty ((fan.affineToricChartι 𝕜 regular
      (fan.wallRestrictionSourceCone complete regular ray first)).opensRange ⊓
      (fan.affineToricChartι 𝕜 regular
        (fan.wallRestrictionSourceCone complete regular ray second)).opensRange :
      (fan.algebraicRealization 𝕜 regular).Opens) := by
    rw [← fan.chart_opensRange_intersection 𝕜 regular]
    exact fan.chartOpen_nonempty 𝕜 regular _
  have firstOpen : atlas.chart firstIndex = fan.wallDescentSourceOpen 𝕜 complete regular ray first :=
    congrArg (fun cone => (fan.affineToricChartι 𝕜 regular cone).opensRange)
      (fan.wallRestrictionSourceIndex_cone 𝕜 complete regular ray first)
  have secondOpen : atlas.chart secondIndex = fan.wallDescentSourceOpen 𝕜 complete regular ray second :=
    congrArg (fun cone => (fan.affineToricChartι 𝕜 regular cone).opensRange)
      (fan.wallRestrictionSourceIndex_cone 𝕜 complete regular ray second)
  have transitionGerm : TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField
      (fan.algebraicRealization 𝕜 regular) domain
      (fan.wallDescentAmbientTransition 𝕜 complete regular divisor ray first second) =
      fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (fan.wallRestrictionSourceCharacter complete regular divisor ray first -
          fan.wallRestrictionSourceCharacter complete regular divisor ray second) := by
    unfold wallDescentAmbientTransition
    dsimp only [domain, wallDescentSourceOpen]
    rw [BondalThomsen.regularUnitGerm_eqToHom (fan.chart_opensRange_intersection 𝕜 regular
      (fan.wallRestrictionSourceCone complete regular ray first)
      (fan.wallRestrictionSourceCone complete regular ray second)),
      fan.chartCoordinateGerm_regularUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)]
    exact fan.chartCoordinateGerm_monomialUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
      common _ _ _
  have equations : TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField
      (fan.algebraicRealization 𝕜 regular) domain
      (fan.wallDescentAmbientTransition 𝕜 complete regular divisor ray first second)⁻¹ *
        atlas.equation secondIndex = atlas.equation firstIndex := by
    rw [map_inv, transitionGerm, ← fan.rationalCharacterUnit_neg 𝕜]
    change fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
      (-(fan.wallRestrictionSourceCharacter complete regular divisor ray first -
        fan.wallRestrictionSourceCharacter complete regular divisor ray second)) *
        fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-fan.divisorLocalCharacter 𝕜 complete regular divisor secondIndex) =
        fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-fan.divisorLocalCharacter 𝕜 complete regular divisor firstIndex)
    rw [fan.wallRestrictionSourceIndex_character 𝕜 complete regular divisor ray second,
      fan.wallRestrictionSourceIndex_character 𝕜 complete regular divisor ray first,
      ← fan.rationalCharacterUnit_add 𝕜]
    congr 1
    abel
  have relation := BondalThomsen.wallCartierFrame_transition_on atlas firstIndex secondIndex domain
    (show domain ≤ atlas.chart firstIndex from inf_le_left.trans firstOpen.ge)
    (show domain ≤ atlas.chart secondIndex from inf_le_right.trans secondOpen.ge)
    (fan.wallDescentAmbientTransition 𝕜 complete regular divisor ray first second)⁻¹ equations
  change (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.res _ _ =
    _ • (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.res _ _ at relation
  dsimp only [wallRestrictionAmbientFrame]
  rw [Scheme.Modules.res_res, Scheme.Modules.res_res]
  exact relation

theorem wallDescentInverseTransition_pullback (reference first second : (fan.star ray).cones) :
    (fan.completeStarOrbitClosureMap 𝕜 complete regular ray).appLE
        (fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentSourceOpen 𝕜 complete regular ray second)
        (fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentQuotientOpen 𝕜 complete regular ray second)
        (fan.wallDescent_preimage_overlap 𝕜 complete regular ray first second).ge
        ((fan.wallDescentAmbientTransition 𝕜 complete regular divisor ray first second)⁻¹).val =
      ((fan.wallDescentQuotientTransition 𝕜 complete regular divisor ray reference first second)⁻¹).val := by
  have unitEquality : Units.map
      ((fan.completeStarOrbitClosureMap 𝕜 complete regular ray).appLE
        (fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentSourceOpen 𝕜 complete regular ray second)
        (fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentQuotientOpen 𝕜 complete regular ray second)
        (fan.wallDescent_preimage_overlap 𝕜 complete regular ray first second).ge).hom.toMonoidHom
      (fan.wallDescentAmbientTransition 𝕜 complete regular divisor ray first second) =
        fan.wallDescentQuotientTransition 𝕜 complete regular divisor ray reference first second := by
    apply Units.ext
    exact fan.wallDescentTransition_pullback 𝕜 complete regular divisor ray reference first second
  have inverseEquality := congrArg (fun unit => unit⁻¹) unitEquality
  rw [← map_inv] at inverseEquality
  exact congrArg Units.val inverseEquality

theorem wallDescentPulledFrame_transition (reference first second : (fan.star ray).cones) :
    (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj.res
        (inf_le_right : fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentQuotientOpen 𝕜 complete regular ray second ≤
            fan.wallDescentQuotientOpen 𝕜 complete regular ray second)
        (fan.wallRestrictionPulledFrame 𝕜 complete regular divisor ray second) =
      ((fan.wallDescentQuotientTransition 𝕜 complete regular divisor ray reference first second)⁻¹).val •
        (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
          (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj.res
          (inf_le_left : fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
            fan.wallDescentQuotientOpen 𝕜 complete regular ray second ≤
              fan.wallDescentQuotientOpen 𝕜 complete regular ray first)
          (fan.wallRestrictionPulledFrame 𝕜 complete regular divisor ray first) := by
  let map := fan.completeStarOrbitClosureMap 𝕜 complete regular ray
  let sheaf := (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
  let domain := fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
    fan.wallDescentQuotientOpen 𝕜 complete regular ray second
  let ambientOverlap := fan.wallDescentSourceOpen 𝕜 complete regular ray first ⊓
    fan.wallDescentSourceOpen 𝕜 complete regular ray second
  have inOverlap : domain ≤ map ⁻¹ᵁ ambientOverlap :=
    (fan.wallDescent_preimage_overlap 𝕜 complete regular ray first second).ge
  have firstRestriction := BondalThomsen.wallPullbackLocalSection_restriction map sheaf
    (inf_le_left : ambientOverlap ≤ fan.wallDescentSourceOpen 𝕜 complete regular ray first)
    (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray first) domain inOverlap
  have secondRestriction := BondalThomsen.wallPullbackLocalSection_restriction map sheaf
    (inf_le_right : ambientOverlap ≤ fan.wallDescentSourceOpen 𝕜 complete regular ray second)
    (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray second) domain inOverlap
  have coefficient := BondalThomsen.wallPullbackLocalSection_coefficient map sheaf ambientOverlap
    (sheaf.res inf_le_left (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray first))
    (sheaf.res inf_le_right (fan.wallRestrictionAmbientFrame 𝕜 complete regular divisor ray second))
    ((fan.wallDescentAmbientTransition 𝕜 complete regular divisor ray first second)⁻¹).val
    (fan.wallDescentAmbientFrame_transition 𝕜 complete regular divisor ray first second) domain inOverlap
  rw [fan.wallDescentInverseTransition_pullback 𝕜 complete regular divisor ray reference first second]
    at coefficient
  change ((Scheme.Modules.pullback map).obj sheaf).res _ _ =
    _ • ((Scheme.Modules.pullback map).obj sheaf).res _ _
  dsimp only [wallRestrictionPulledFrame]
  rw [Scheme.Modules.res_res, Scheme.Modules.res_res]
  exact secondRestriction.trans (coefficient.trans
    (congrArg (fun sectionValue =>
      ((fan.wallDescentQuotientTransition 𝕜 complete regular divisor ray reference first second)⁻¹).val •
        sectionValue) firstRestriction.symm))

theorem wallDescentChartIso_overlap (reference first second : (fan.star ray).cones) :
    BondalThomsen.restrictLocalModuleHom (inf_le_left :
        fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentQuotientOpen 𝕜 complete regular ray second ≤
            fan.wallDescentQuotientOpen 𝕜 complete regular ray first)
        (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference first).hom =
      BondalThomsen.restrictLocalModuleHom inf_le_right
        (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference second).hom := by
  let source := (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj
  let target := (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext subopen
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro sectionValue
  cases subopen with
  | op subopen =>
    let smaller := subopen.left
    have inOverlap : smaller ≤ fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
        fan.wallDescentQuotientOpen 𝕜 complete regular ray second := subopen.hom.le
    let scalar := ((fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray)).presheaf.map
      (homOfLE inOverlap).op
      ((fan.wallDescentQuotientTransition 𝕜 complete regular divisor ray reference first second)⁻¹).val
    have sourceRelation := BondalThomsen.wallFrameTransition_restrict source
      (fan.wallDescentQuotientOpen 𝕜 complete regular ray first)
      (fan.wallDescentQuotientOpen 𝕜 complete regular ray second)
      (fan.wallRestrictionQuotientFrame 𝕜 complete regular divisor ray reference first)
      (fan.wallRestrictionQuotientFrame 𝕜 complete regular divisor ray reference second) _
      (fan.wallDescentQuotientFrame_transition 𝕜 complete regular divisor ray reference first second)
      smaller inOverlap
    have targetRelation := BondalThomsen.wallFrameTransition_restrict target
      (fan.wallDescentQuotientOpen 𝕜 complete regular ray first)
      (fan.wallDescentQuotientOpen 𝕜 complete regular ray second)
      (fan.wallRestrictionPulledFrame 𝕜 complete regular divisor ray first)
      (fan.wallRestrictionPulledFrame 𝕜 complete regular divisor ray second) _
      (fan.wallDescentPulledFrame_transition 𝕜 complete regular divisor ray reference first second)
      smaller inOverlap
    dsimp only [source] at sourceRelation
    dsimp only [target] at targetRelation
    obtain ⟨coefficient, presentation⟩ :=
      (fan.wallRestrictionQuotientFrame_isFrame 𝕜 complete regular divisor ray reference second
        smaller (inOverlap.trans inf_le_right)).2 sectionValue
    change (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference first).hom.val.app
        (op (Over.mk (homOfLE (inOverlap.trans inf_le_left)))) sectionValue =
      (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference second).hom.val.app
        (op (Over.mk (homOfLE (inOverlap.trans inf_le_right)))) sectionValue
    rw [← presentation]
    rw [((fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference first).hom.val.app
      (op (Over.mk (homOfLE (inOverlap.trans inf_le_left))))).hom.map_smul,
      ((fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference second).hom.val.app
      (op (Over.mk (homOfLE (inOverlap.trans inf_le_right))))).hom.map_smul]
    apply congrArg (fun sectionValue => coefficient • sectionValue)
    let firstMap := (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference first).hom.val.app
      (op (Over.mk (homOfLE (inOverlap.trans inf_le_left))))
    let secondMap := (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference second).hom.val.app
      (op (Over.mk (homOfLE (inOverlap.trans inf_le_right))))
    exact (congrArg (fun sectionValue => firstMap sectionValue) sourceRelation).trans
      ((firstMap.hom.map_smul scalar _).trans
        ((congrArg (fun sectionValue => scalar • sectionValue)
          (fan.wallDescentChartIso_frame 𝕜 complete regular divisor ray reference first smaller
            (inOverlap.trans inf_le_left))).trans
          (targetRelation.symm.trans
            (fan.wallDescentChartIso_frame 𝕜 complete regular divisor ray reference second smaller
              (inOverlap.trans inf_le_right)).symm)))

theorem wallDescentQuotientOpen_cover :
    IsOpenCover (fan.wallDescentQuotientOpen 𝕜 complete regular ray) := by
  exact fan.wallRestrictionQuotientCone_covers 𝕜 complete regular ray

theorem wallDescentChartIso_inverse_overlap (reference first second : (fan.star ray).cones) :
    BondalThomsen.restrictLocalModuleHom (inf_le_left :
        fan.wallDescentQuotientOpen 𝕜 complete regular ray first ⊓
          fan.wallDescentQuotientOpen 𝕜 complete regular ray second ≤
            fan.wallDescentQuotientOpen 𝕜 complete regular ray first)
        (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference first).inv =
      BondalThomsen.restrictLocalModuleHom inf_le_right
        (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference second).inv := by
  rw [BondalThomsen.restrictLocalModuleHom_inverse, BondalThomsen.restrictLocalModuleHom_inverse]
  simp only [fan.wallDescentChartIso_overlap 𝕜 complete regular divisor ray reference first second]

def wallRestrictionGlobalSheafHom (reference : (fan.star ray).cones) :
    (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj ⟶
      (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj :=
  BondalThomsen.LocalModuleGluing.glue (fan.wallDescentQuotientOpen 𝕜 complete regular ray)
    (fan.wallDescentQuotientOpen_cover 𝕜 complete regular ray)
    (fun cone => (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference cone).hom)
    (fan.wallDescentChartIso_overlap 𝕜 complete regular divisor ray reference)

def wallRestrictionGlobalSheafInv (reference : (fan.star ray).cones) :
    (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj ⟶
      (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj :=
  BondalThomsen.LocalModuleGluing.glue (fan.wallDescentQuotientOpen 𝕜 complete regular ray)
    (fan.wallDescentQuotientOpen_cover 𝕜 complete regular ray)
    (fun cone => (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference cone).inv)
    (fan.wallDescentChartIso_inverse_overlap 𝕜 complete regular divisor ray reference)

theorem wallRestrictionGlobalSheafHom_over (reference cone : (fan.star ray).cones) :
    (fan.wallRestrictionGlobalSheafHom 𝕜 complete regular divisor ray reference).over
        (fan.wallDescentQuotientOpen 𝕜 complete regular ray cone) =
      (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference cone).hom :=
  BondalThomsen.LocalModuleGluing.glue_over _ _ _ _ cone

theorem wallRestrictionGlobalSheafInv_over (reference cone : (fan.star ray).cones) :
    (fan.wallRestrictionGlobalSheafInv 𝕜 complete regular divisor ray reference).over
        (fan.wallDescentQuotientOpen 𝕜 complete regular ray cone) =
      (fan.wallRestrictionChartIso 𝕜 complete regular divisor ray reference cone).inv :=
  BondalThomsen.LocalModuleGluing.glue_over _ _ _ _ cone

def wallRestrictionGlobalSheafIso (reference : (fan.star ray).cones) :
    (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj ≅
      (fan.surfaceWallRestrictedLineBundle 𝕜 complete regular ray
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor)).obj where
  hom := fan.wallRestrictionGlobalSheafHom 𝕜 complete regular divisor ray reference
  inv := fan.wallRestrictionGlobalSheafInv 𝕜 complete regular divisor ray reference
  hom_inv_id := by
    apply BondalThomsen.LocalModuleGluing.hom_ext (fan.wallDescentQuotientOpen 𝕜 complete regular ray)
      (fan.wallDescentQuotientOpen_cover 𝕜 complete regular ray)
    intro cone
    change (fan.wallRestrictionGlobalSheafHom 𝕜 complete regular divisor ray reference).over _ ≫
      (fan.wallRestrictionGlobalSheafInv 𝕜 complete regular divisor ray reference).over _ = 𝟙 _
    rw [fan.wallRestrictionGlobalSheafHom_over 𝕜, fan.wallRestrictionGlobalSheafInv_over 𝕜,
      Iso.hom_inv_id]
  inv_hom_id := by
    apply BondalThomsen.LocalModuleGluing.hom_ext (fan.wallDescentQuotientOpen 𝕜 complete regular ray)
      (fan.wallDescentQuotientOpen_cover 𝕜 complete regular ray)
    intro cone
    change (fan.wallRestrictionGlobalSheafInv 𝕜 complete regular divisor ray reference).over _ ≫
      (fan.wallRestrictionGlobalSheafHom 𝕜 complete regular divisor ray reference).over _ = 𝟙 _
    rw [fan.wallRestrictionGlobalSheafInv_over 𝕜, fan.wallRestrictionGlobalSheafHom_over 𝕜,
      Iso.inv_hom_id]

theorem surfaceWallQuotient_isNef_of_isNef (reference : (fan.star ray).cones)
    (nef : AlgebraicGeometry.IsNef (baseField := 𝕜)
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) :
    AlgebraicGeometry.IsNef (baseField := 𝕜)
      (fan.wallRestrictionLineBundle 𝕜 complete regular divisor ray reference).obj := by
  exact AlgebraicGeometry.IsNef.of_iso
    (fan.wallRestrictionGlobalSheafIso 𝕜 complete regular divisor ray reference).symm
    (fan.surfaceWallRestrictedLineBundle_isNef 𝕜 complete regular ray _ nef)

end TauCeti.Toric.Fan
