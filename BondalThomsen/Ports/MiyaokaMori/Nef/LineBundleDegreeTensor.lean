module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LineBundleDegreeIndependence
public import BondalThomsen.LineBundle.AmpleLineBundleTensorLocalDescent

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Divisors
open AlgebraicGeometry.Intersection BondalThomsen
open scoped Classical

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

instance lineBundleDegreeTensor_isInvertible {scheme : Scheme.{0}}
    (firstBundle secondBundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme secondBundle] :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme
      (Scheme.Modules.tensor firstBundle secondBundle) :=
  TauCeti.SheafOfModules.IsInvertible.tensorProduct (R := scheme.sheaf)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.IsFrame

variable {scheme : Scheme.{0}} {firstBundle secondBundle : scheme.Modules}
  {region : scheme.Opens} {firstGenerator : Γ(firstBundle, region)}
  {secondGenerator : Γ(secondBundle, region)}

theorem coord_tensorSection
    (firstFrame : IsFrame firstBundle region firstGenerator)
    (secondFrame : IsFrame secondBundle region secondGenerator)
    {smaller : scheme.Opens} (subset : smaller ≤ region)
    (firstValue : Γ(firstBundle, smaller)) (secondValue : Γ(secondBundle, smaller)) :
    (ampleTensorSection_isFrame_of_localFrames firstBundle secondBundle region
      firstGenerator secondGenerator firstFrame secondFrame).coord subset
      (ampleTensorSection firstBundle secondBundle smaller firstValue secondValue) =
      firstFrame.coord subset firstValue * secondFrame.coord subset secondValue := by
  apply IsFrame.coord_unique
  rw [ampleTensorSection_res, mul_smul, ← ampleTensorSection_smul_right,
    ← ampleTensorSection_smul_left, firstFrame.coord_smul_frame, secondFrame.coord_smul_frame]

theorem genericCoordinate_tensorSection [IsIntegral scheme] [Nonempty region]
    (firstFrame : IsFrame firstBundle region firstGenerator)
    (secondFrame : IsFrame secondBundle region secondGenerator)
    {smaller : scheme.Opens} (subset : smaller ≤ region) [Nonempty smaller]
    (firstValue : Γ(firstBundle, smaller)) (secondValue : Γ(secondBundle, smaller)) :
    (ampleTensorSection_isFrame_of_localFrames firstBundle secondBundle region
      firstGenerator secondGenerator firstFrame secondFrame).genericCoordinate
        ((Scheme.Modules.tensor firstBundle secondBundle).presheaf.germ smaller
          (genericPoint scheme) (IsFrame.genericPoint_mem_region smaller)
          (ampleTensorSection firstBundle secondBundle smaller firstValue secondValue)) =
      firstFrame.genericCoordinate (firstBundle.presheaf.germ smaller
        (genericPoint scheme) (IsFrame.genericPoint_mem_region smaller) firstValue) *
      secondFrame.genericCoordinate (secondBundle.presheaf.germ smaller
        (genericPoint scheme) (IsFrame.genericPoint_mem_region smaller) secondValue) := by
  rw [IsFrame.genericCoordinate_germ, firstFrame.genericCoordinate_germ subset,
    secondFrame.genericCoordinate_germ subset, coord_tensorSection, map_mul]

end AlgebraicGeometry.Scheme.Modules.IsFrame

namespace AlgebraicGeometry.Divisors

theorem LineRationalSectionPresentation.coefficient_eq_ord_genericCoordinate
    {scheme : Scheme.{0}} [IsIntegral scheme] [IsLocallyNoetherian scheme]
    {bundle : scheme.Modules} {rationalSection : bundle.presheaf.stalk (genericPoint scheme)}
    (presentation : LineRationalSectionPresentation bundle rationalSection)
    {region : scheme.Opens} {generator : Γ(bundle, region)}
    (frame : IsFrame bundle region generator) (point : scheme) (contains : point ∈ region) :
    letI : Nonempty region := ⟨⟨point, contains⟩⟩
    presentation.cartier.coefficient point = scheme.ord (frame.genericCoordinate rationalSection) point := by
  let : Nonempty region := ⟨⟨point, contains⟩⟩
  let chart := presentation.cartier.indexAt point
  have chartContains := presentation.cartier.indexAt_mem point
  let : Nonempty (presentation.cartier.opens chart) := ⟨⟨point, chartContains⟩⟩
  let overlap := presentation.cartier.opens chart ⊓ region
  let : Nonempty overlap := ⟨⟨point, chartContains, contains⟩⟩
  obtain ⟨unitSection, transition⟩ := (presentation.frame chart).genericCoordinate_transition frame
  have unitNonzero : scheme.germToFunctionField overlap unitSection ≠ 0 := by
    intro zero
    exact unitSection.ne_zero (scheme.germToFunctionField_injective overlap
      (zero.trans (map_zero _).symm))
  rw [presentation.cartier.coefficient_eq_ord_of_mem point chart chartContains,
    presentation.equation_eq chart inferInstance, transition rationalSection,
    Scheme.ord_mul unitNonzero (frame.genericCoordinate_ne_zero rationalSection presentation.section_ne_zero),
    Scheme.ord_of_isUnit unitSection.isUnit (show point ∈ overlap from ⟨chartContains, contains⟩), zero_add]

theorem exists_tensor_rationalSection_coordinates
    {scheme : Scheme.{0}} [IsIntegral scheme] {firstBundle secondBundle : scheme.Modules}
    (firstSection : firstBundle.presheaf.stalk (genericPoint scheme))
    (secondSection : secondBundle.presheaf.stalk (genericPoint scheme)) :
    ∃ tensorSection : (Scheme.Modules.tensor firstBundle secondBundle).presheaf.stalk
        (genericPoint scheme),
      ∀ region : scheme.Opens, ∀ nonempty : Nonempty region,
        ∀ firstGenerator : Γ(firstBundle, region), ∀ secondGenerator : Γ(secondBundle, region),
        ∀ firstFrame : IsFrame firstBundle region firstGenerator,
        ∀ secondFrame : IsFrame secondBundle region secondGenerator,
        letI := nonempty
        (ampleTensorSection_isFrame_of_localFrames firstBundle secondBundle region
          firstGenerator secondGenerator firstFrame secondFrame).genericCoordinate tensorSection =
          firstFrame.genericCoordinate firstSection * secondFrame.genericCoordinate secondSection := by
  obtain ⟨firstRegion, firstContains, firstValue, firstEquality⟩ :=
    firstBundle.presheaf.exists_germ_eq firstSection
  obtain ⟨commonRegion, commonSubset, commonContains, secondValue, secondEquality⟩ :=
    secondBundle.presheaf.exists_le_germ_eq secondSection firstContains
  let firstCommon := firstBundle.res commonSubset firstValue
  have firstCommonEquality : firstBundle.presheaf.germ commonRegion (genericPoint scheme)
      commonContains firstCommon = firstSection := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact firstEquality
  let tensorSection := (Scheme.Modules.tensor firstBundle secondBundle).presheaf.germ commonRegion
    (genericPoint scheme) commonContains
    (ampleTensorSection firstBundle secondBundle commonRegion firstCommon secondValue)
  refine ⟨tensorSection, ?_⟩
  intro region nonempty firstGenerator secondGenerator firstFrame secondFrame
  let := nonempty
  let overlap := commonRegion ⊓ region
  have overlapContains : genericPoint scheme ∈ overlap :=
    ⟨commonContains, IsFrame.genericPoint_mem_region region⟩
  let : Nonempty overlap := ⟨⟨genericPoint scheme, overlapContains⟩⟩
  have tensorEquality : tensorSection =
      (Scheme.Modules.tensor firstBundle secondBundle).presheaf.germ overlap (genericPoint scheme)
        overlapContains (ampleTensorSection firstBundle secondBundle overlap
          (firstBundle.res inf_le_left firstCommon) (secondBundle.res inf_le_left secondValue)) := by
    rw [← ampleTensorSection_res, TopCat.Presheaf.germ_res_apply]
  have firstOverlapEquality : firstBundle.presheaf.germ overlap (genericPoint scheme)
      overlapContains (firstBundle.res inf_le_left firstCommon) = firstSection := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact firstCommonEquality
  have secondOverlapEquality : secondBundle.presheaf.germ overlap (genericPoint scheme)
      overlapContains (secondBundle.res inf_le_left secondValue) = secondSection := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact secondEquality
  rw [tensorEquality, IsFrame.genericCoordinate_tensorSection firstFrame secondFrame
    (inf_le_right : overlap ≤ region), firstOverlapEquality, secondOverlapEquality]

theorem exists_tensor_rationalSectionPresentation
    {scheme : Scheme.{0}} [IsIntegral scheme] [IsNoetherian scheme]
    {firstBundle secondBundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme secondBundle]
    {firstSection : firstBundle.presheaf.stalk (genericPoint scheme)}
    {secondSection : secondBundle.presheaf.stalk (genericPoint scheme)}
    (first : LineRationalSectionPresentation firstBundle firstSection)
    (second : LineRationalSectionPresentation secondBundle secondSection) :
    ∃ tensorSection : (Scheme.Modules.tensor firstBundle secondBundle).presheaf.stalk
        (genericPoint scheme),
      ∃ presentation : LineRationalSectionPresentation
        (Scheme.Modules.tensor firstBundle secondBundle) tensorSection,
        ∀ point : scheme, presentation.cartier.coefficient point =
          first.cartier.coefficient point + second.cartier.coefficient point := by
  obtain ⟨tensorSection, coordinates⟩ := exists_tensor_rationalSection_coordinates firstSection secondSection
  have tensorNonzero : tensorSection ≠ 0 := by
    let firstChart := first.cartier.indexAt (genericPoint scheme)
    let secondChart := second.cartier.indexAt (genericPoint scheme)
    let region := first.cartier.opens firstChart ⊓ second.cartier.opens secondChart
    have regionContains : genericPoint scheme ∈ region :=
      ⟨first.cartier.indexAt_mem _, second.cartier.indexAt_mem _⟩
    let : Nonempty region := ⟨⟨genericPoint scheme, regionContains⟩⟩
    let firstFrame := (first.frame firstChart).restrict (inf_le_left : region ≤ _)
    let secondFrame := (second.frame secondChart).restrict (inf_le_right : region ≤ _)
    have coordinateEquation := coordinates region inferInstance _ _ firstFrame secondFrame
    have productNonzero := mul_ne_zero
      (firstFrame.genericCoordinate_ne_zero firstSection first.section_ne_zero)
      (secondFrame.genericCoordinate_ne_zero secondSection second.section_ne_zero)
    intro zero
    rw [zero, map_zero] at coordinateEquation
    exact productNonzero coordinateEquation.symm
  obtain ⟨presentation⟩ := LineRationalSectionPresentation.exists_of_nonzero
    (Scheme.Modules.tensor firstBundle secondBundle) tensorSection tensorNonzero
  refine ⟨tensorSection, presentation, ?_⟩
  intro point
  let firstChart := first.cartier.indexAt point
  let secondChart := second.cartier.indexAt point
  let region := first.cartier.opens firstChart ⊓ second.cartier.opens secondChart
  have regionContains : point ∈ region :=
    ⟨first.cartier.indexAt_mem _, second.cartier.indexAt_mem _⟩
  let : Nonempty region := ⟨⟨point, regionContains⟩⟩
  let firstFrame := (first.frame firstChart).restrict (inf_le_left : region ≤ _)
  let secondFrame := (second.frame secondChart).restrict (inf_le_right : region ≤ _)
  let productFrame := ampleTensorSection_isFrame_of_localFrames firstBundle secondBundle region
    _ _ firstFrame secondFrame
  rw [presentation.coefficient_eq_ord_genericCoordinate productFrame point regionContains,
    coordinates region inferInstance _ _ firstFrame secondFrame,
    Scheme.ord_mul (firstFrame.genericCoordinate_ne_zero firstSection first.section_ne_zero)
      (secondFrame.genericCoordinate_ne_zero secondSection second.section_ne_zero),
    first.coefficient_eq_ord_genericCoordinate firstFrame point regionContains,
    second.coefficient_eq_ord_genericCoordinate secondFrame point regionContains]

end AlgebraicGeometry.Divisors

namespace AlgebraicGeometry.Intersection

variable {baseField : Type} [Field baseField] {scheme : Scheme.{0}}
  [IsIntegral scheme] [IsNoetherian scheme]

theorem lineBundleDegree_tensor
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (firstBundle secondBundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme secondBundle] :
    lineBundleDegree structureMap dimensionBound (Scheme.Modules.tensor firstBundle secondBundle) =
      lineBundleDegree structureMap dimensionBound firstBundle +
        lineBundleDegree structureMap dimensionBound secondBundle := by
  have : CompactSpace scheme := QuasiCompact.compactSpace_of_compactSpace structureMap
  obtain ⟨firstSection, ⟨first⟩⟩ := LineRationalSectionPresentation.exists_section_and_presentation firstBundle
  obtain ⟨secondSection, ⟨second⟩⟩ := LineRationalSectionPresentation.exists_section_and_presentation secondBundle
  obtain ⟨tensorSection, presentation, coefficients⟩ := exists_tensor_rationalSectionPresentation first second
  rw [lineBundleDegree_eq_of_presentation structureMap dimensionBound presentation,
    lineBundleDegree_eq_of_presentation structureMap dimensionBound first,
    lineBundleDegree_eq_of_presentation structureMap dimensionBound second]
  have cycleEquality : presentation.cartier.zeroCycle dimensionBound =
      DimensionCycle.add (first.cartier.zeroCycle dimensionBound) (second.cartier.zeroCycle dimensionBound) := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    exact coefficients
  unfold CartierLocalData.degreeOver
  rw [cycleEquality, rawZeroCycleDegree_add]

theorem lineBundleDegree_unit
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) :
    lineBundleDegree structureMap dimensionBound (SheafOfModules.unit scheme.ringCatSheaf) = 0 := by
  let unitBundle : scheme.Modules := SheafOfModules.unit scheme.ringCatSheaf
  let comparison : Scheme.Modules.tensor unitBundle unitBundle ≅ unitBundle :=
    Scheme.Modules.isoOfSheafIso scheme
      (TauCeti.SheafOfModules.tensorProductUnitIsoLeft scheme.sheaf unitBundle)
  have additive := lineBundleDegree_tensor structureMap dimensionBound unitBundle unitBundle
  rw [lineBundleDegree_eq_of_iso structureMap dimensionBound comparison] at additive
  linarith

theorem lineBundleDegree_tensorPow
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] (exponent : ℕ) :
    lineBundleDegree structureMap dimensionBound (Scheme.Modules.tensorPow bundle exponent) =
      (exponent : ℤ) * lineBundleDegree structureMap dimensionBound bundle := by
  induction exponent with
  | zero =>
      change lineBundleDegree structureMap dimensionBound
        (SheafOfModules.unit scheme.ringCatSheaf) = _
      rw [lineBundleDegree_unit]
      simp
  | succ exponent inductionHypothesis =>
      change lineBundleDegree structureMap dimensionBound
        (Scheme.Modules.tensor (Scheme.Modules.tensorPow bundle exponent) bundle) = _
      rw [lineBundleDegree_tensor, inductionHypothesis]
      push_cast
      ring

end AlgebraicGeometry.Intersection

namespace IntegralCurve

variable {baseField : Type} [Field baseField] {scheme : Scheme.{0}}
  [scheme.Over (Spec (CommRingCat.of baseField))]

theorem lineBundleDegree_tensor (curve : IntegralCurve baseField scheme)
    (firstBundle secondBundle : curve.carrier.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible curve.carrier firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible curve.carrier secondBundle] :
    curve.lineBundleDegree (Scheme.Modules.tensor firstBundle secondBundle) =
      curve.lineBundleDegree firstBundle + curve.lineBundleDegree secondBundle :=
  Intersection.lineBundleDegree_tensor (curve.carrier ↘ Spec (CommRingCat.of baseField))
    curve.dim_eq_one.le firstBundle secondBundle

theorem lineBundleDegree_tensorPow (curve : IntegralCurve baseField scheme)
    (bundle : curve.carrier.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible curve.carrier bundle] (exponent : ℕ) :
    curve.lineBundleDegree (Scheme.Modules.tensorPow bundle exponent) =
      (exponent : ℤ) * curve.lineBundleDegree bundle :=
  Intersection.lineBundleDegree_tensorPow (curve.carrier ↘ Spec (CommRingCat.of baseField))
    curve.dim_eq_one.le bundle exponent

theorem lineBundleDegree_pullback_tensor (curve : IntegralCurve baseField scheme)
    (firstBundle secondBundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme secondBundle] :
    curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj
        (Scheme.Modules.tensor firstBundle secondBundle)) =
      curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj firstBundle) +
        curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj secondBundle) := by
  rw [curve.lineBundleDegree_eq_of_iso
    (ampleInvertibleTensorPullbackIso curve.ι firstBundle secondBundle), curve.lineBundleDegree_tensor]

theorem lineBundleDegree_pullback_tensorPow (curve : IntegralCurve baseField scheme)
    (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] (exponent : ℕ) :
    curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj
        (Scheme.Modules.tensorPow bundle exponent)) =
      (exponent : ℤ) * curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj bundle) := by
  rw [curve.lineBundleDegree_eq_of_iso
    (ampleInvertibleTensorPowerPullbackIso curve.ι bundle exponent), curve.lineBundleDegree_tensorPow]

end IntegralCurve

namespace AlgebraicGeometry

variable {baseField : Type} [Field baseField] {scheme : Scheme.{0}}
  [scheme.Over (Spec (CommRingCat.of baseField))]

theorem IsNef.tensor {firstBundle secondBundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme secondBundle]
    (first : IsNef (baseField := baseField) firstBundle)
    (second : IsNef (baseField := baseField) secondBundle) :
    IsNef (baseField := baseField) (Scheme.Modules.tensor firstBundle secondBundle) := by
  intro curve
  rw [curve.lineBundleDegree_pullback_tensor]
  exact add_nonneg (first curve) (second curve)

theorem IsNef.tensorPow {bundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    (nef : IsNef (baseField := baseField) bundle) (exponent : ℕ) :
    IsNef (baseField := baseField) (Scheme.Modules.tensorPow bundle exponent) := by
  intro curve
  rw [curve.lineBundleDegree_pullback_tensorPow]
  exact mul_nonneg (Nat.cast_nonneg exponent) (nef curve)

theorem isNef_tensorPow_iff (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    {exponent : ℕ} (positive : 0 < exponent) :
    IsNef (baseField := baseField) (Scheme.Modules.tensorPow bundle exponent) ↔
      IsNef (baseField := baseField) bundle := by
  constructor
  · intro nef curve
    have nonnegative := nef curve
    rw [curve.lineBundleDegree_pullback_tensorPow] at nonnegative
    exact (mul_nonneg_iff_of_pos_left
      (show (0 : ℤ) < exponent from by exact_mod_cast positive)).mp nonnegative
  · exact fun nef => nef.tensorPow exponent

theorem IsNef.of_tensorPow {bundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    {exponent : ℕ} (positive : 0 < exponent)
    (nef : IsNef (baseField := baseField) (Scheme.Modules.tensorPow bundle exponent)) :
    IsNef (baseField := baseField) bundle :=
  (isNef_tensorPow_iff bundle positive).mp nef

end AlgebraicGeometry
