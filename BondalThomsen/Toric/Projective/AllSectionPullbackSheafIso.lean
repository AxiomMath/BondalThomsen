module

public import BondalThomsen.Toric.Projective.GlobalSheafIso
public import BondalThomsen.Toric.Divisor.DivisorMonomialGlobalEmbedding

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] BondalThomsen.restrictLocalModuleHom_isIso

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)

noncomputable def allSectionProjectiveDegreeOnePullbackSheaf :
    (fan.algebraicRealization 𝕜 regular).Modules :=
  BondalThomsen.polynomialProjDegreeOnePullbackSheaf 𝕜 (fan.globalDivisorSectionExponents divisor)
    (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)

noncomputable def allSectionProjectivePullbackCoordinateHom
    (exponent : fan.globalDivisorSectionExponents divisor) :
    SheafOfModules.unit (fan.algebraicRealization 𝕜 regular).ringCatSheaf ⟶
      fan.allSectionProjectiveDegreeOnePullbackSheaf 𝕜 complete regular divisor support :=
  BondalThomsen.polynomialProjDegreeOnePullbackCoordinateHom 𝕜 (fan.globalDivisorSectionExponents divisor)
    (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support) exponent

noncomputable def allSectionProjectiveSourceCoordinateHom
    (exponent : fan.globalDivisorSectionExponents divisor) :
    SheafOfModules.unit (fan.algebraicRealization 𝕜 regular).ringCatSheaf ⟶
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj :=
  BondalThomsen.moduleGlobalSectionHom _ (fan.allDivisorMonomialSheafBasis 𝕜 complete regular divisor exponent)

theorem allSectionProjectiveDenominator_actualGlobalSection
    (chart : Fin (Nat.card fan.cones)) :
    fan.allDivisorMonomialSheafBasis 𝕜 complete regular divisor
        (fan.allSectionProjectiveDenominator complete regular divisor support chart) =
      fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support chart := by
  change fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor
      (fan.globalDivisorLaurentSectionBasis 𝕜 divisor
        (fan.allSectionProjectiveDenominator complete regular divisor support chart)) = _
  unfold invariantDivisorSheafGlobalChartGenerator
  congr 1
  apply Subtype.ext
  rw [fan.globalDivisorLaurentSectionBasis_val 𝕜]
  rfl

theorem allSectionProjectiveSourceCoordinateHom_denominator
    (chart : Fin (Nat.card fan.cones)) :
    fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor
        (fan.allSectionProjectiveDenominator complete regular divisor support chart) =
      fan.divisorProjectiveSourceCoordinateHom 𝕜 complete regular divisor support chart := by
  unfold allSectionProjectiveSourceCoordinateHom divisorProjectiveSourceCoordinateHom
  rw [fan.allSectionProjectiveDenominator_actualGlobalSection 𝕜 complete regular divisor support chart]

noncomputable def allSectionProjectiveChartRingMap
    (chart : Fin (Nat.card fan.cones)) :
    HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
      (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart)) →+*
        affineCoordinateRing 𝕜 fan.lattice (fan.divisorLocalCone 𝕜 complete regular chart).val :=
  BondalThomsen.projectiveAwayEvaluation 𝕜 (algebraMap 𝕜 _)
    (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart)
    (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart)) 1
    (by simpa using fan.allSectionProjectiveRatio_denominator 𝕜 complete regular divisor support chart)

theorem allSectionProjectiveChartRingMap_coordinate
    (chart : Fin (Nat.card fan.cones)) (exponent : fan.globalDivisorSectionExponents divisor) :
    fan.allSectionProjectiveChartRingMap 𝕜 complete regular divisor support chart
      (HomogeneousLocalization.Away.mk
        (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
        (MvPolynomial.isHomogeneous_X 𝕜
          (fan.allSectionProjectiveDenominator complete regular divisor support chart)) 1
        (MvPolynomial.X exponent) (by simpa using MvPolynomial.isHomogeneous_X 𝕜 exponent)) =
      fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent := by
  unfold allSectionProjectiveChartRingMap
  rw [BondalThomsen.projectiveAwayEvaluation_mk]
  simp only [MvPolynomial.eval₂Hom_X', inv_one, Units.val_one, one_pow, mul_one]

theorem allSectionProjectiveMonomialMap_chart_coordinateMap
    (chart : Fin (Nat.card fan.cones)) :
    fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart) ≫
        fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support =
      Spec.map (CommRingCat.ofHom
        (fan.allSectionProjectiveChartRingMap 𝕜 complete regular divisor support chart)) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
        (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart))
        (MvPolynomial.isHomogeneous_X 𝕜 _) (by decide) := by
  rw [fan.allSectionProjectiveMonomialMap_chart 𝕜]
  rfl

theorem allSectionProjectivePullbackDenominatorHom_affine_isIso
    (chart : Fin (Nat.card fan.cones)) :
    IsIso (BondalThomsen.modulePullbackSectionHom
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart))
        (fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor support
          (fan.allSectionProjectiveDenominator complete regular divisor support chart))) := by
  let inclusion := fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
  let source_map := fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support
  let coordinate_hom := BondalThomsen.polynomialProjDegreeOneCoordinateHom 𝕜
    (fan.globalDivisorSectionExponents divisor)
      (fan.allSectionProjectiveDenominator complete regular divisor support chart)
  have composite_iso : IsIso (BondalThomsen.modulePullbackSectionHom (inclusion ≫ source_map)
      coordinate_hom) := by
    rw [fan.allSectionProjectiveMonomialMap_chart_coordinateMap 𝕜 complete regular divisor support chart]
    exact BondalThomsen.modulePullbackSectionHom_comp_isIso _ _ coordinate_hom
      (BondalThomsen.polynomialProjDegreeOneCoordinateHom_pullbackChart_isIso 𝕜 _ _)
  have transported := BondalThomsen.modulePullbackSectionHom_comp inclusion source_map coordinate_hom
  change IsIso (BondalThomsen.modulePullbackSectionHom inclusion
    (BondalThomsen.modulePullbackSectionHom source_map coordinate_hom))
  rw [← transported] at composite_iso
  exact (isIso_comp_right_iff _
    ((Scheme.Modules.pullbackComp inclusion source_map).hom.app
      (BondalThomsen.polynomialProjDegreeOneSheaf 𝕜 (fan.globalDivisorSectionExponents divisor)))).mp composite_iso

theorem allSectionProjectivePullbackDenominatorHom_over_isIso
    (chart : Fin (Nat.card fan.cones)) :
    IsIso ((fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor support
      (fan.allSectionProjectiveDenominator complete regular divisor support chart)).over
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange) :=
  BondalThomsen.modulePullbackSectionHom_over_isIso _ _
    (fan.allSectionProjectivePullbackDenominatorHom_affine_isIso 𝕜 complete regular divisor support chart)

noncomputable def allSectionProjectivePullbackDenominatorFrame
    (chart : Fin (Nat.card fan.cones)) :
    SheafOfModules.unit ((fan.algebraicRealization 𝕜 regular).ringCatSheaf.over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange) ≅
    (fan.allSectionProjectiveDegreeOnePullbackSheaf 𝕜 complete regular divisor support).over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange := by
  letI := fan.allSectionProjectivePullbackDenominatorHom_over_isIso 𝕜 complete regular divisor support chart
  exact asIso ((fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor support
    (fan.allSectionProjectiveDenominator complete regular divisor support chart)).over _)

noncomputable def allSectionProjectiveCanonicalPullbackChartIso
    (chart : Fin (Nat.card fan.cones)) :
    (fan.allSectionProjectiveDegreeOnePullbackSheaf 𝕜 complete regular divisor support).over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange ≅
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange :=
  (fan.allSectionProjectivePullbackDenominatorFrame 𝕜 complete regular divisor support chart).symm ≪≫
    fan.divisorProjectiveSourceCoordinateFrame 𝕜 complete regular divisor support chart

theorem allSectionProjectiveCanonicalPullbackChartIso_denominator
    (chart : Fin (Nat.card fan.cones)) :
    (fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor support
        (fan.allSectionProjectiveDenominator complete regular divisor support chart)).over
          (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange ≫
      (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support chart).hom =
    (fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor
      (fan.allSectionProjectiveDenominator complete regular divisor support chart)).over
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange := by
  rw [fan.allSectionProjectiveSourceCoordinateHom_denominator 𝕜]
  change (fan.allSectionProjectivePullbackDenominatorFrame 𝕜 complete regular divisor support chart).hom ≫
    ((fan.allSectionProjectivePullbackDenominatorFrame 𝕜 complete regular divisor support chart).inv ≫
      (fan.divisorProjectiveSourceCoordinateFrame 𝕜 complete regular divisor support chart).hom) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

theorem allSectionProjectiveSourceChart_le_preimage_coordinateOpen
    (chart : Fin (Nat.card fan.cones)) :
    (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange ≤
      (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support) ⁻¹ᵁ
        (BondalThomsen.polynomialDegreeOneCoordinateOpen 𝕜) (fan.globalDivisorSectionExponents divisor)
          (fan.allSectionProjectiveDenominator complete regular divisor support chart) := by
  rintro point ⟨local_point, rfl⟩
  have chart_equality := congrArg (fun morphism => morphism local_point)
    (fan.allSectionProjectiveMonomialMap_chart_coordinateMap 𝕜 complete regular divisor support chart)
  change (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
    ((fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)) local_point) = _
      at chart_equality
  change (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
    ((fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)) local_point) ∈
      BondalThomsen.polynomialDegreeOneCoordinateOpen 𝕜 (fan.globalDivisorSectionExponents divisor)
        (fan.allSectionProjectiveDenominator complete regular divisor support chart)
  rw [chart_equality]
  change _ ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
    (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart))
  rw [← Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X 𝕜 _) (by decide)]
  exact ⟨_, rfl⟩

theorem allSectionProjectiveChartRingMap_actualApp
    (chart : Fin (Nat.card fan.cones)) :
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
        (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart)) ≫
      (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support).appLE
        (BondalThomsen.polynomialDegreeOneCoordinateOpen 𝕜 (fan.globalDivisorSectionExponents divisor)
          (fan.allSectionProjectiveDenominator complete regular divisor support chart))
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange
        (fan.allSectionProjectiveSourceChart_le_preimage_coordinateOpen 𝕜 complete regular divisor support chart) =
    CommRingCat.ofHom (fan.allSectionProjectiveChartRingMap 𝕜 complete regular divisor support chart) ≫
      (Scheme.ΓSpecIso _).inv ≫
        (IsOpenImmersion.ΓIsoTop
          (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart))).hom := by
  let inclusion := fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
  let source_map := fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support
  let target_open := BondalThomsen.polynomialDegreeOneCoordinateOpen 𝕜 (fan.globalDivisorSectionExponents divisor)
    (fan.allSectionProjectiveDenominator complete regular divisor support chart)
  let ring_map := CommRingCat.ofHom
    (fan.allSectionProjectiveChartRingMap 𝕜 complete regular divisor support chart)
  let target_chart := Proj.awayι (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
    (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart))
    (MvPolynomial.isHomogeneous_X 𝕜 _) (by decide)
  have target_contains : ⊤ ≤ target_chart ⁻¹ᵁ target_open := by
    intro point member
    change _ ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
      (MvPolynomial.X (fan.allSectionProjectiveDenominator complete regular divisor support chart))
    rw [← Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X 𝕜 _) (by decide)]
    exact ⟨point, rfl⟩
  apply (cancel_mono (IsOpenImmersion.ΓIsoTop inclusion).inv).mp
  simp only [Category.assoc]
  rw [BondalThomsen.openImmersion_sectionsIso_inv]
  rw [Scheme.Hom.appLE_comp_appLE inclusion source_map]
  dsimp only [inclusion, source_map]
  simp only [fan.allSectionProjectiveMonomialMap_chart_coordinateMap 𝕜 complete regular divisor support chart]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map ring_map) target_chart target_open ⊤ ⊤
    target_contains (by simp)]
  have affine_app : (Spec.map ring_map).appLE ⊤ ⊤ (by simp) = (Spec.map ring_map).appTop :=
    (Spec.map ring_map).appLE_eq_app
  rw [affine_app, ← Category.assoc, BondalThomsen.polynomialProjAwayToSection_comp_chartApp]
  rw [← BondalThomsen.openImmersion_sectionsIso_inv]
  simp only [Iso.hom_inv_id, Category.comp_id]
  exact (Scheme.ΓSpecIso_inv_naturality ring_map).symm

theorem allSectionProjectiveChartRatio_actualApp
    (chart : Fin (Nat.card fan.cones)) (exponent : fan.globalDivisorSectionExponents divisor) :
    (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support).appLE
        (BondalThomsen.polynomialDegreeOneCoordinateOpen 𝕜 (fan.globalDivisorSectionExponents divisor)
          (fan.allSectionProjectiveDenominator complete regular divisor support chart))
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange
        (fan.allSectionProjectiveSourceChart_le_preimage_coordinateOpen 𝕜 complete regular divisor support chart)
        (BondalThomsen.polynomialDegreeOneChartRatio 𝕜 (fan.globalDivisorSectionExponents divisor)
          (fan.allSectionProjectiveDenominator complete regular divisor support chart) exponent le_rfl) =
      fan.chartCoordinateSectionsEquiv 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
        (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent) := by
  rw [BondalThomsen.polynomialDegreeOneChartRatio_eq_awayToSection]
  have evaluation := ConcreteCategory.congr_hom
    (fan.allSectionProjectiveChartRingMap_actualApp 𝕜 complete regular divisor support chart)
      (HomogeneousLocalization.Away.mk
        (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
        (MvPolynomial.isHomogeneous_X 𝕜
          (fan.allSectionProjectiveDenominator complete regular divisor support chart)) 1
        (MvPolynomial.X exponent) (by simpa using MvPolynomial.isHomogeneous_X 𝕜 exponent))
  change _ = fan.chartCoordinateSectionsEquiv 𝕜 regular
    (fan.divisorLocalCone 𝕜 complete regular chart)
      (fan.allSectionProjectiveChartRingMap 𝕜 complete regular divisor support chart _) at evaluation
  rw [fan.allSectionProjectiveChartRingMap_coordinate 𝕜] at evaluation
  exact evaluation

theorem allSectionProjectiveChartRatio_actualApp_restrict
    (chart : Fin (Nat.card fan.cones)) (exponent : fan.globalDivisorSectionExponents divisor)
    (open_set : (fan.algebraicRealization 𝕜 regular).Opens)
    (contained : open_set ≤
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange) :
    (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support).appLE
        (BondalThomsen.polynomialDegreeOneCoordinateOpen 𝕜 (fan.globalDivisorSectionExponents divisor)
          (fan.allSectionProjectiveDenominator complete regular divisor support chart)) open_set
        (contained.trans
          (fan.allSectionProjectiveSourceChart_le_preimage_coordinateOpen 𝕜 complete regular divisor support chart))
        (BondalThomsen.polynomialDegreeOneChartRatio 𝕜 (fan.globalDivisorSectionExponents divisor)
          (fan.allSectionProjectiveDenominator complete regular divisor support chart) exponent le_rfl) =
      (fan.algebraicRealization 𝕜 regular).presheaf.map (homOfLE contained).op
        (fan.chartCoordinateSectionsEquiv 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
          (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent)) := by
  rw [← fan.allSectionProjectiveChartRatio_actualApp 𝕜 complete regular divisor support chart exponent]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_map _ _ (homOfLE contained).op) _).symm

omit support in
theorem allSectionProjectiveRatio_actualCoefficientSection
    (chart : Fin (Nat.card fan.cones)) (exponent : fan.globalDivisorSectionExponents divisor) :
    fan.invariantDivisorSheafChartCoefficientAddEquiv 𝕜 complete regular divisor chart
        (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent) =
      fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange
        (fan.allDivisorMonomialSheafBasis 𝕜 complete regular divisor exponent) :=
  fan.invariantDivisorSheafChartCoefficient_global 𝕜 complete regular divisor chart
    (fan.globalDivisorLaurentSectionBasis 𝕜 divisor exponent)

theorem allSectionProjectiveSourceCoordinateHom_coefficient
    (chart : Fin (Nat.card fan.cones)) (exponent : fan.globalDivisorSectionExponents divisor) :
    Scheme.Modules.Hom.app (fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor exponent)
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange
          (1 : Γ(fan.algebraicRealization 𝕜 regular,
            (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange)) =
      fan.chartCoordinateSectionsEquiv 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
        (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent) •
      Scheme.Modules.Hom.app (fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor
        (fan.allSectionProjectiveDenominator complete regular divisor support chart))
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange
          (1 : Γ(fan.algebraicRealization 𝕜 regular,
            (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange)) := by
  simp only [allSectionProjectiveSourceCoordinateHom, BondalThomsen.moduleGlobalSectionHom_app, one_smul]
  change fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor _
      (fan.allDivisorMonomialSheafBasis 𝕜 complete regular divisor exponent) =
    _ • fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor _
      (fan.allDivisorMonomialSheafBasis 𝕜 complete regular divisor
        (fan.allSectionProjectiveDenominator complete regular divisor support chart))
  rw [← fan.allSectionProjectiveRatio_actualCoefficientSection 𝕜 complete regular divisor chart exponent,
    ← fan.allSectionProjectiveRatio_actualCoefficientSection 𝕜 complete regular divisor chart
      (fan.allSectionProjectiveDenominator complete regular divisor support chart),
    fan.allSectionProjectiveRatio_denominator 𝕜 complete regular divisor support chart]
  simpa only [mul_one] using fan.invariantDivisorSheafChartCoefficient_smul 𝕜 complete regular divisor
    chart (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent) 1

theorem allSectionProjectiveCanonicalPullbackChartIso_allCoordinates
    (chart : Fin (Nat.card fan.cones)) (exponent : fan.globalDivisorSectionExponents divisor) :
    (fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor support exponent).over
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange ≫
      (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support chart).hom =
    (fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor exponent).over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange := by
  apply SheafOfModules.hom_ext
  ext local_open : 2
  apply (LinearMap.ringLmapEquivSelf _ ℤ _).injective
  let open_set := local_open.unop.left
  let contained := local_open.unop.hom.le
  let denominator := fan.allSectionProjectiveDenominator complete regular divisor support chart
  let scalar := (fan.algebraicRealization 𝕜 regular).presheaf.map (homOfLE contained).op
    (fan.chartCoordinateSectionsEquiv 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
      (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent))
  have pullback_relation := BondalThomsen.modulePullbackSectionHom_coefficient
    (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)
    (BondalThomsen.polynomialProjDegreeOneCoordinateHom 𝕜 (fan.globalDivisorSectionExponents divisor) denominator)
    (BondalThomsen.polynomialProjDegreeOneCoordinateHom 𝕜 (fan.globalDivisorSectionExponents divisor) exponent)
    (BondalThomsen.polynomialDegreeOneCoordinateOpen 𝕜 (fan.globalDivisorSectionExponents divisor) denominator) open_set
    (contained.trans
      (fan.allSectionProjectiveSourceChart_le_preimage_coordinateOpen 𝕜 complete regular divisor support chart))
    (BondalThomsen.polynomialDegreeOneChartRatio 𝕜 (fan.globalDivisorSectionExponents divisor) denominator exponent le_rfl)
    (BondalThomsen.polynomialProjDegreeOneCoordinateHom_coefficient 𝕜 _ denominator exponent)
  rw [fan.allSectionProjectiveChartRatio_actualApp_restrict 𝕜 complete regular divisor support
    chart exponent open_set contained] at pullback_relation
  change Scheme.Modules.Hom.app (fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor support
      exponent) open_set (1 : Γ(fan.algebraicRealization 𝕜 regular, open_set)) =
    scalar • Scheme.Modules.Hom.app (fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor support
      denominator) open_set (1 : Γ(fan.algebraicRealization 𝕜 regular, open_set)) at pullback_relation
  have source_relation := BondalThomsen.moduleSectionHom_coefficient_restrict
    (fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor denominator)
    (fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor exponent)
    (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange open_set contained
    (fan.chartCoordinateSectionsEquiv 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
      (fan.allSectionProjectiveRatio 𝕜 complete regular divisor chart exponent))
    (fan.allSectionProjectiveSourceCoordinateHom_coefficient 𝕜 complete regular divisor support chart exponent)
  have diagonal := congrArg (fun morphism => morphism.val.app local_open
    (1 : Γ(fan.algebraicRealization 𝕜 regular, open_set)))
    (fan.allSectionProjectiveCanonicalPullbackChartIso_denominator 𝕜 complete regular divisor support chart)
  change (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support chart).hom.val.app
      local_open (Scheme.Modules.Hom.app (fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor
        support exponent) open_set (1 : Γ(fan.algebraicRealization 𝕜 regular, open_set))) =
    Scheme.Modules.Hom.app (fan.allSectionProjectiveSourceCoordinateHom 𝕜 complete regular divisor exponent)
      open_set (1 : Γ(fan.algebraicRealization 𝕜 regular, open_set))
  rw [pullback_relation, source_relation]
  rw [((fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support chart).hom.val.app
    local_open).hom.map_smul]
  exact congrArg (fun section_value => scalar • section_value) diagonal

theorem allSectionProjectiveCanonicalPullbackChartIso_overlap
    (first second : Fin (Nat.card fan.cones)) :
    BondalThomsen.restrictLocalModuleHom (inf_le_left :
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular first)).opensRange ⊓
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular second)).opensRange ≤
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular first)).opensRange)
        (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support first).hom =
    BondalThomsen.restrictLocalModuleHom inf_le_right
      (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support second).hom := by
  let common := (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular first)).opensRange ⊓
    (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular second)).opensRange
  let denominator := fan.allSectionProjectiveDenominator complete regular divisor support first
  let coordinate_hom := fan.allSectionProjectivePullbackCoordinateHom 𝕜 complete regular divisor support denominator
  have coordinate_iso : IsIso (coordinate_hom.over common) := by
    rw [← BondalThomsen.restrictLocalModuleHom_global (inf_le_left : common ≤ _) coordinate_hom]
    let := fan.allSectionProjectivePullbackDenominatorHom_over_isIso 𝕜 complete regular divisor support first
    exact BondalThomsen.restrictLocalModuleHom_isIso _ _
  let := coordinate_iso
  apply (cancel_epi (coordinate_hom.over common)).mp
  have first_equality := congrArg (BondalThomsen.restrictLocalModuleHom (inf_le_left : common ≤ _))
    (fan.allSectionProjectiveCanonicalPullbackChartIso_allCoordinates 𝕜 complete regular divisor support
      first denominator)
  have second_equality := congrArg (BondalThomsen.restrictLocalModuleHom (inf_le_right : common ≤ _))
    (fan.allSectionProjectiveCanonicalPullbackChartIso_allCoordinates 𝕜 complete regular divisor support
      second denominator)
  simp only [BondalThomsen.restrictLocalModuleHom_map_comp,
    BondalThomsen.restrictLocalModuleHom_global] at first_equality second_equality
  exact first_equality.trans second_equality.symm

theorem allSectionProjectiveCanonicalPullbackChartIso_inverse_overlap
    (first second : Fin (Nat.card fan.cones)) :
    BondalThomsen.restrictLocalModuleHom (inf_le_left :
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular first)).opensRange ⊓
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular second)).opensRange ≤
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular first)).opensRange)
        (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support first).inv =
    BondalThomsen.restrictLocalModuleHom inf_le_right
      (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support second).inv := by
  rw [BondalThomsen.restrictLocalModuleHom_inverse, BondalThomsen.restrictLocalModuleHom_inverse]
  simp only [fan.allSectionProjectiveCanonicalPullbackChartIso_overlap 𝕜 complete regular divisor support first second]

noncomputable def allSectionProjectiveCanonicalPullbackSheafHom :
    fan.allSectionProjectiveDegreeOnePullbackSheaf 𝕜 complete regular divisor support ⟶
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj :=
  BondalThomsen.LocalModuleGluing.glue
    (fun chart => (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange)
    (fan.divisorProjectiveDegreeOneSourceChart_cover 𝕜 complete regular)
    (fun chart => (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support chart).hom)
    (fan.allSectionProjectiveCanonicalPullbackChartIso_overlap 𝕜 complete regular divisor support)

noncomputable def allSectionProjectiveCanonicalPullbackSheafInv :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ⟶
      fan.allSectionProjectiveDegreeOnePullbackSheaf 𝕜 complete regular divisor support :=
  BondalThomsen.LocalModuleGluing.glue
    (fun chart => (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange)
    (fan.divisorProjectiveDegreeOneSourceChart_cover 𝕜 complete regular)
    (fun chart => (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support chart).inv)
    (fan.allSectionProjectiveCanonicalPullbackChartIso_inverse_overlap 𝕜 complete regular divisor support)

theorem allSectionProjectiveCanonicalPullbackSheafHom_over
    (chart : Fin (Nat.card fan.cones)) :
    (fan.allSectionProjectiveCanonicalPullbackSheafHom 𝕜 complete regular divisor support).over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange =
      (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support chart).hom :=
  BondalThomsen.LocalModuleGluing.glue_over _ _ _ _ chart

theorem allSectionProjectiveCanonicalPullbackSheafInv_over
    (chart : Fin (Nat.card fan.cones)) :
    (fan.allSectionProjectiveCanonicalPullbackSheafInv 𝕜 complete regular divisor support).over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange =
      (fan.allSectionProjectiveCanonicalPullbackChartIso 𝕜 complete regular divisor support chart).inv :=
  BondalThomsen.LocalModuleGluing.glue_over _ _ _ _ chart

noncomputable def allSectionProjectiveCanonicalPullbackSheafIso :
    fan.allSectionProjectiveDegreeOnePullbackSheaf 𝕜 complete regular divisor support ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj where
  hom := fan.allSectionProjectiveCanonicalPullbackSheafHom 𝕜 complete regular divisor support
  inv := fan.allSectionProjectiveCanonicalPullbackSheafInv 𝕜 complete regular divisor support
  hom_inv_id := by
    apply BondalThomsen.LocalModuleGluing.hom_ext
      (fun chart => (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange)
      (fan.divisorProjectiveDegreeOneSourceChart_cover 𝕜 complete regular)
    intro chart
    change (fan.allSectionProjectiveCanonicalPullbackSheafHom 𝕜 complete regular divisor support).over _ ≫
      (fan.allSectionProjectiveCanonicalPullbackSheafInv 𝕜 complete regular divisor support).over _ = 𝟙 _
    rw [fan.allSectionProjectiveCanonicalPullbackSheafHom_over 𝕜,
      fan.allSectionProjectiveCanonicalPullbackSheafInv_over 𝕜, Iso.hom_inv_id]
  inv_hom_id := by
    apply BondalThomsen.LocalModuleGluing.hom_ext
      (fun chart => (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange)
      (fan.divisorProjectiveDegreeOneSourceChart_cover 𝕜 complete regular)
    intro chart
    change (fan.allSectionProjectiveCanonicalPullbackSheafInv 𝕜 complete regular divisor support).over _ ≫
      (fan.allSectionProjectiveCanonicalPullbackSheafHom 𝕜 complete regular divisor support).over _ = 𝟙 _
    rw [fan.allSectionProjectiveCanonicalPullbackSheafInv_over 𝕜,
      fan.allSectionProjectiveCanonicalPullbackSheafHom_over 𝕜, Iso.inv_hom_id]

noncomputable def allSectionProjectiveMonomialMap_pullback_degreeOneIso :
    (Scheme.Modules.pullback (fan.allSectionProjectiveMonomialMap 𝕜 complete regular divisor support)).obj
      (BondalThomsen.polynomialProjDegreeOneSheaf 𝕜 (fan.globalDivisorSectionExponents divisor)) ≅
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj :=
  fan.allSectionProjectiveCanonicalPullbackSheafIso 𝕜 complete regular divisor support

end TauCeti.Toric.Fan
