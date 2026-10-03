module

public import BondalThomsen.Toric.Projective.AllSectionPullbackSheafIso
public import BondalThomsen.Ports.MiyaokaMori.AmpleLineBundle
public import BondalThomsen.Ports.MiyaokaMori.InvertibleSheafTensorPowerCompatibility
public import BondalThomsen.LineBundle.AmpleLineBundleClassCriterion
public import BondalThomsen.Toric.Positivity.VeryAmpleLineBundle

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace BondalThomsen

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] polynomialProjDegreeOnePullbackSheaf_isInvertible

variable (Index : Type)

theorem polynomialDegreeOneChartRatio_basicOpen (chart coordinate : Index) :
    (polynomialDegreeOneProj 𝕜 Index).basicOpen
        (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) =
      polynomialDegreeOneCoordinateOpen 𝕜 Index chart ⊓
        polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate := by
  apply TopologicalSpace.Opens.ext
  ext point
  constructor
  · intro member
    have chart_member := (polynomialDegreeOneProj 𝕜 Index).basicOpen_le
      (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) member
    refine ⟨chart_member, ?_⟩
    have unit := ((polynomialDegreeOneProj 𝕜 Index).mem_basicOpen
      (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) point chart_member).mp member
    have unit_ratio := unit.map
      (Proj.stalkIso' (MvPolynomial.homogeneousSubmodule Index 𝕜) point)
    erw [Proj.stalkIso'_germ] at unit_ratio
    have unit_value := (HomogeneousLocalization.isUnit_iff_isUnit_val
      (MvPolynomial.homogeneousSubmodule Index 𝕜) point.asHomogeneousIdeal.toIdeal _).mpr unit_ratio
    have unit_coordinate := unit_value.mul
      (polynomialDegreeOneCoordinate_isUnit 𝕜 Index point chart chart_member)
    rw [polynomialDegreeOneChartRatio_mul_coordinate 𝕜 Index chart coordinate le_rfl
      ⟨point, chart_member⟩] at unit_coordinate
    exact (IsLocalization.AtPrime.isUnit_to_map_iff
      (polynomialDegreeOnePointLocalization 𝕜 Index point) point.asHomogeneousIdeal.toIdeal
      (MvPolynomial.X coordinate)).mp unit_coordinate
  · rintro ⟨chart_member, coordinate_member⟩
    change point ∈ (polynomialDegreeOneProj 𝕜 Index).basicOpen
      (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl)
    rw [(polynomialDegreeOneProj 𝕜 Index).mem_basicOpen
      (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) point chart_member]
    apply (isUnit_map_iff (Proj.stalkIso'
      (MvPolynomial.homogeneousSubmodule Index 𝕜) point) _).mp
    erw [Proj.stalkIso'_germ]
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
    change IsUnit (Localization.mk (MvPolynomial.X coordinate)
      ⟨MvPolynomial.X chart, chart_member⟩)
    rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact coordinate_member

def polynomialProjDegreeOnePullbackGlobalCoordinate {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) (coordinate : Index) :
    Γ(polynomialProjDegreeOnePullbackSheaf 𝕜 Index map, ⊤) :=
  Scheme.Modules.Hom.app (polynomialProjDegreeOnePullbackCoordinateHom 𝕜 Index map coordinate) ⊤
    (1 : Γ(source, ⊤))

theorem moduleGlobalSectionHom_app_one_restrict {scheme : Scheme} {sheaf : scheme.Modules}
    (section_map : SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf) (open_set : scheme.Opens) :
    sheaf.res le_top (Scheme.Modules.Hom.app section_map ⊤ (1 : Γ(scheme, ⊤))) =
      Scheme.Modules.Hom.app section_map open_set (1 : Γ(scheme, open_set)) := by
  have naturality := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf scheme).map section_map).naturality
      (homOfLE (show open_set ≤ ⊤ from le_top)).op)
      (1 : Γ(scheme, ⊤))
  change Scheme.Modules.Hom.app section_map open_set
    (scheme.presheaf.map (homOfLE le_top).op (1 : Γ(scheme, ⊤))) =
      sheaf.res le_top (Scheme.Modules.Hom.app section_map ⊤ (1 : Γ(scheme, ⊤))) at naturality
  rw [map_one] at naturality
  exact naturality.symm

theorem moduleGlobalSectionHom_isFrame_of_over_isIso {scheme : Scheme}
    {sheaf : scheme.Modules}
    (section_map : SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf)
    (open_set : scheme.Opens) (local_iso : IsIso (section_map.over open_set)) :
    Scheme.Modules.IsFrame sheaf open_set
      (Scheme.Modules.Hom.app section_map open_set (1 : Γ(scheme, open_set))) := by
  intro smaller inclusion
  let := local_iso
  let local_open : Over open_set := Over.mk (homOfLE inclusion)
  let forgetful := SheafOfModules.forget (scheme.ringCatSheaf.over open_set) ⋙
    PresheafOfModules.toPresheaf (scheme.ringCatSheaf.over open_set).obj
  have component_iso : IsIso ((forgetful.map (section_map.over open_set)).app (op local_open)) :=
    inferInstance
  have bijective := ConcreteCategory.bijective_of_isIso
    ((forgetful.map (section_map.over open_set)).app (op local_open))
  change Function.Bijective (fun scalar : Γ(scheme, smaller) =>
    Scheme.Modules.Hom.app section_map smaller scalar) at bijective
  have formula : ∀ scalar : Γ(scheme, smaller),
      Scheme.Modules.Hom.app section_map smaller scalar =
        scalar • sheaf.res inclusion
          (Scheme.Modules.Hom.app section_map open_set (1 : Γ(scheme, open_set))) := by
    intro scalar
    have naturality := ConcreteCategory.congr_hom
      (((Scheme.Modules.toPresheaf scheme).map section_map).naturality (homOfLE inclusion).op)
        (1 : Γ(scheme, open_set))
    change Scheme.Modules.Hom.app section_map smaller
      (scheme.presheaf.map (homOfLE inclusion).op (1 : Γ(scheme, open_set))) =
        sheaf.res inclusion
          (Scheme.Modules.Hom.app section_map open_set (1 : Γ(scheme, open_set))) at naturality
    rw [map_one] at naturality
    rw [← naturality]
    simpa only [smul_eq_mul, mul_one] using
      Scheme.Modules.Hom.app_smul section_map scalar (1 : Γ(scheme, smaller))
  rw [← funext formula]
  exact bijective

theorem polynomialProjDegreeOnePullbackCoordinateHom_over_isIso {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) (coordinate : Index) :
    IsIso ((polynomialProjDegreeOnePullbackCoordinateHom 𝕜 Index map coordinate).over
      (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate)) := by
  let target_open := polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate
  let source_open := map ⁻¹ᵁ target_open
  let inclusion := source_open.ι
  let restricted := map.resLE target_open source_open le_rfl
  let section_map := polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate
  have target_iso : IsIso (modulePullbackSectionHom target_open.ι section_map) := by
    rw [modulePullbackSectionHom_restrict]
    let := polynomialProjDegreeOneCoordinateHom_restrict_isIso 𝕜 Index coordinate
    infer_instance
  have composite_iso := modulePullbackSectionHom_comp_isIso restricted target_open.ι section_map target_iso
  rw [Scheme.Hom.resLE_comp_ι] at composite_iso
  have composite_formula := modulePullbackSectionHom_comp inclusion map section_map
  rw [← composite_formula] at composite_iso
  have source_iso := (isIso_comp_right_iff _
    ((Scheme.Modules.pullbackComp inclusion map).hom.app
      (polynomialProjDegreeOneSheaf 𝕜 Index))).mp composite_iso
  have over_iso := modulePullbackSectionHom_over_isIso inclusion
    (modulePullbackSectionHom map section_map) source_iso
  change IsIso ((polynomialProjDegreeOnePullbackCoordinateHom 𝕜 Index map coordinate).over
    source_open.ι.opensRange) at over_iso
  rw [Scheme.Opens.opensRange_ι] at over_iso
  exact over_iso

theorem polynomialProjDegreeOnePullbackGlobalCoordinate_isFrame {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) (coordinate : Index) :
    Scheme.Modules.IsFrame (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map)
      (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate)
      ((polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).res le_top
        (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate)) := by
  rw [polynomialProjDegreeOnePullbackGlobalCoordinate, moduleGlobalSectionHom_app_one_restrict]
  exact moduleGlobalSectionHom_isFrame_of_over_isIso _ _
    (polynomialProjDegreeOnePullbackCoordinateHom_over_isIso 𝕜 Index map coordinate)

theorem polynomialProjDegreeOnePullbackGlobalCoordinate_frameCoefficient {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) (chart coordinate : Index) :
    (polynomialProjDegreeOnePullbackGlobalCoordinate_isFrame 𝕜 Index map chart).coord le_rfl
      ((polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).res le_top
        (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate)) =
      map.app (polynomialDegreeOneCoordinateOpen 𝕜 Index chart)
        (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) := by
  let frame := polynomialProjDegreeOnePullbackGlobalCoordinate_isFrame 𝕜 Index map chart
  have relation := modulePullbackSectionHom_coefficient map
    (polynomialProjDegreeOneCoordinateHom 𝕜 Index chart)
    (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)
    (polynomialDegreeOneCoordinateOpen 𝕜 Index chart)
    (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index chart) le_rfl
    (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl)
    (polynomialProjDegreeOneCoordinateHom_coefficient 𝕜 Index chart coordinate)
  have coefficient := frame.coord_smul_frame le_rfl
    ((polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).res le_top
      (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate))
  rw [Scheme.Modules.res_self] at coefficient
  apply (frame _ le_rfl).injective
  rw [Scheme.Modules.res_self]
  dsimp only
  change frame.coord le_rfl
      ((polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).res le_top
        (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate)) •
      (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).res le_top
        (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map chart) = _
  rw [coefficient]
  rw [polynomialProjDegreeOnePullbackGlobalCoordinate, moduleGlobalSectionHom_app_one_restrict]
  rw [polynomialProjDegreeOnePullbackGlobalCoordinate, moduleGlobalSectionHom_app_one_restrict]
  simpa only [Scheme.Hom.appLE_eq_app, polynomialProjDegreeOnePullbackCoordinateHom,
    polynomialProjDegreeOnePullbackSheaf] using relation

theorem polynomialProjDegreeOnePullbackGlobalCoordinate_nonvanishingLocus {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) (coordinate : Index) :
    (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).nonvanishingLocus
        (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate) =
      map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate := by
  let := polynomialProjDegreeOnePullbackSheaf_isInvertible 𝕜 Index map
  have chartwise : ∀ chart : Index,
      (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index chart) ⊓
          (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).nonvanishingLocus
            (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate) =
        (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index chart) ⊓
          (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate) := by
    intro chart
    rw [(polynomialProjDegreeOnePullbackGlobalCoordinate_isFrame 𝕜 Index map chart).inf_nonvanishingLocus_eq_basicOpen,
      polynomialProjDegreeOnePullbackGlobalCoordinate_frameCoefficient,
      ← Scheme.preimage_basicOpen, polynomialDegreeOneChartRatio_basicOpen,
      Scheme.Hom.preimage_inf]
  apply TopologicalSpace.Opens.ext
  ext point
  change point ∈ (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).nonvanishingLocus
    (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate) ↔
      point ∈ map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate
  obtain ⟨chart, chart_member⟩ :=
    (polynomialProjDegreeOnePullbackCoordinateOpen_cover 𝕜 Index map).exists_mem point
  have local_equivalence : point ∈
      (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index chart) ⊓
        (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map).nonvanishingLocus
          (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate) ↔
      point ∈ (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index chart) ⊓
        (map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate) :=
    (chartwise chart) ▸ Iff.rfl
  simpa only [TopologicalSpace.Opens.mem_inf, chart_member, true_and] using local_equivalence

theorem polynomialProjDegreeOnePullbackSheaf_isAmpleAt {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) [IsAffineHom map] (point : source) :
    AlgebraicGeometry.IsAmpleAt (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map) point := by
  let := polynomialProjDegreeOnePullbackSheaf_isInvertible 𝕜 Index map
  obtain ⟨coordinate, contains⟩ :=
    (polynomialProjDegreeOnePullbackCoordinateOpen_cover 𝕜 Index map).exists_mem point
  let comparison := Scheme.Modules.tensorPowOneIso (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map)
  let section_value := comparison.inv.app ⊤
    (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate)
  have locus : (Scheme.Modules.tensorPow (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map) 1).nonvanishingLocus
      section_value = map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate := by
    exact (Scheme.Modules.nonvanishingLocus_iso comparison.symm
      (polynomialProjDegreeOnePullbackGlobalCoordinate 𝕜 Index map coordinate)).trans
        (polynomialProjDegreeOnePullbackGlobalCoordinate_nonvanishingLocus 𝕜 Index map coordinate)
  refine ⟨1, Nat.zero_lt_one, section_value, locus.symm ▸ contains, ?_⟩
  rw [locus]
  exact (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X 𝕜 coordinate) (by decide)).preimage map

theorem polynomialDegreeOneProj_compactSpace [Finite Index] :
    CompactSpace (polynomialDegreeOneProj 𝕜 Index) := by
  let := polynomialProjStructureMap_isProper 𝕜 Index
  exact (quasiCompact_iff_compactSpace (polynomialProjStructureMap 𝕜 Index)).mp inferInstance

theorem polynomialProjDegreeOnePullbackSheaf_isAmple_of_closedImmersion [Finite Index]
    {source : Scheme} (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) [IsClosedImmersion map] :
    AlgebraicGeometry.IsAmple (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map) := by
  let := polynomialDegreeOneProj_compactSpace 𝕜 Index
  exact ⟨(IsClosedImmersion.isClosedEmbedding map).compactSpace,
    polynomialProjDegreeOnePullbackSheaf_isAmpleAt 𝕜 Index map⟩

theorem isAmple_of_polynomialProj_closedImmersion {source : Scheme}
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf source)
    [Finite Index] (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) [IsClosedImmersion map]
    (comparison : (Scheme.Modules.pullback map).obj (polynomialProjDegreeOneSheaf 𝕜 Index) ≅ bundle.obj) :
    AlgebraicGeometry.IsAmple bundle.obj := by
  let := polynomialProjDegreeOnePullbackSheaf_isInvertible 𝕜 Index map
  exact (polynomialProjDegreeOnePullbackSheaf_isAmple_of_closedImmersion 𝕜 Index map).of_iso comparison

universe schemeUniverse

def invertibleSheafTensorPowerIterateIso {scheme : Scheme.{schemeUniverse}}
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) (first second : ℕ) :
    Scheme.Modules.tensorPow (invertibleSheafTensorPower bundle first).obj second ≅
      Scheme.Modules.tensorPow bundle.obj (first * second) :=
  (MiyaokaMori.invertibleSheafTensorPowerIso (invertibleSheafTensorPower bundle first) second).symm ≪≫
    (TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mp (by
      rw [invertibleSheafTensorPower_class, invertibleSheafTensorPower_class,
        invertibleSheafTensorPower_class, pow_mul])).some ≪≫
      MiyaokaMori.invertibleSheafTensorPowerIso bundle (first * second)

theorem isAmple_of_positive_tensorPower {scheme : Scheme.{schemeUniverse}}
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) (exponent : ℕ)
    (positive : 0 < exponent)
    (amplePower : AlgebraicGeometry.IsAmple (invertibleSheafTensorPower bundle exponent).obj) :
    AlgebraicGeometry.IsAmple bundle.obj := by
  refine ⟨amplePower.1, fun point => ?_⟩
  obtain ⟨power, power_positive, section_value, contains, affine⟩ := amplePower.2 point
  let comparison := invertibleSheafTensorPowerIterateIso bundle exponent power
  refine ⟨exponent * power, Nat.mul_pos positive power_positive,
    comparison.hom.app ⊤ section_value, ?_, ?_⟩
  · exact (Scheme.Modules.mem_nonvanishingLocus_iso comparison section_value point).mpr contains
  · exact (Scheme.Modules.nonvanishingLocus_iso comparison section_value).symm ▸ affine

theorem isAmple_of_positive_powerClass {scheme : Scheme.{schemeUniverse}}
    (bundle powerBundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) (exponent : ℕ)
    (positive : 0 < exponent)
    (powerClass : TauCeti.AlgebraicGeometry.LineBundleClass.mk powerBundle =
      TauCeti.AlgebraicGeometry.LineBundleClass.mk bundle ^ exponent)
    (amplePower : AlgebraicGeometry.IsAmple powerBundle.obj) :
    AlgebraicGeometry.IsAmple bundle.obj := by
  apply isAmple_of_positive_tensorPower bundle exponent positive
  apply (isAmple_iff_of_lineBundleClass_eq
    (powerClass.trans (invertibleSheafTensorPower_class bundle exponent).symm)).mp
  exact amplePower

theorem VeryAmpleOverField.isAmple_of_isProper {scheme : Scheme}
    {structureMap : scheme ⟶ Spec (CommRingCat.of 𝕜)} [IsProper structureMap]
    {bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme}
    (veryAmple : VeryAmpleOverField 𝕜 structureMap bundle) :
    AlgebraicGeometry.IsAmple bundle.obj := by
  obtain ⟨Index, finite, embedding, immersion, overBase, ⟨comparison⟩⟩ := veryAmple
  let := finite
  let := immersion
  let := polynomialProjStructureMap_isProper 𝕜 Index
  have composite_proper : IsProper (embedding ≫ polynomialProjStructureMap 𝕜 Index) := by
    rw [overBase]
    infer_instance
  let := composite_proper
  let := IsProper.of_comp embedding (polynomialProjStructureMap 𝕜 Index)
  let := IsClosedImmersion.of_isPreimmersion embedding
    (Scheme.Hom.isClosedMap embedding).isClosed_range
  exact isAmple_of_polynomialProj_closedImmersion 𝕜 Index bundle embedding comparison

theorem HasVeryAmplePowerOverField.isAmple_of_isProper {scheme : Scheme}
    {structureMap : scheme ⟶ Spec (CommRingCat.of 𝕜)} [IsProper structureMap]
    {bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme}
    (veryAmplePower : HasVeryAmplePowerOverField 𝕜 structureMap bundle) :
    AlgebraicGeometry.IsAmple bundle.obj := by
  obtain ⟨exponent, positive, powerBundle, powerClass, veryAmple⟩ := veryAmplePower
  exact isAmple_of_positive_powerClass bundle powerBundle exponent positive powerClass
    (veryAmple.isAmple_of_isProper 𝕜)

end BondalThomsen
