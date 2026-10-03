module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LineRationalSectionPresentation
public import BondalThomsen.Ports.MiyaokaMori.Nef.PrincipalCurveDegreeZero
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Pullback

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Divisors
open AlgebraicGeometry.Intersection
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.IsFrame

variable {scheme : Scheme.{u}} {firstBundle secondBundle : scheme.Modules}
  {region : scheme.Opens} {generator : Γ(firstBundle, region)}

theorem mapIso (frame : IsFrame firstBundle region generator)
    (comparison : firstBundle ≅ secondBundle) :
    IsFrame secondBundle region (comparison.hom.app region generator) := by
  intro smaller subset
  have restrictionEquality : secondBundle.res subset (comparison.hom.app region generator) =
      comparison.hom.app smaller (firstBundle.res subset generator) :=
    (comparison.hom.mapPresheaf.naturality_apply (homOfLE subset).op generator).symm
  rw [restrictionEquality]
  have scalarEquality : (fun scalar : Γ(scheme, smaller) =>
      scalar • comparison.hom.app smaller (firstBundle.res subset generator)) =
      (fun sectionValue => comparison.hom.app smaller sectionValue) ∘
        (fun scalar : Γ(scheme, smaller) => scalar • firstBundle.res subset generator) := by
    funext scalar
    exact (Hom.app_smul comparison.hom scalar _).symm
  rw [scalarEquality]
  exact (ConcreteCategory.bijective_of_isIso (comparison.hom.app smaller)).comp (frame smaller subset)

theorem genericCoordinate_mapIso [IsIntegral scheme] [Nonempty region]
    (frame : IsFrame firstBundle region generator) (comparison : firstBundle ≅ secondBundle)
    (rationalSection : firstBundle.presheaf.stalk (genericPoint scheme)) :
    (frame.mapIso comparison).genericCoordinate
      (moduleStalkMap scheme (genericPoint scheme) comparison.hom rationalSection) =
      frame.genericCoordinate rationalSection := by
  apply (frame.mapIso comparison).genericCoordinate_unique
  have representation := congrArg (moduleStalkMap scheme (genericPoint scheme) comparison.hom)
    (frame.genericCoordinate_smul_generator rationalSection)
  rw [LinearMap.map_smul, IsFrame.genericGenerator, moduleStalkMap_germ] at representation
  exact representation

end AlgebraicGeometry.Scheme.Modules.IsFrame

namespace AlgebraicGeometry.Divisors.LineRationalSectionPresentation

def mapIso {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]
    {firstBundle secondBundle : scheme.Modules}
    {rationalSection : firstBundle.presheaf.stalk (genericPoint scheme)}
    (presentation : LineRationalSectionPresentation firstBundle rationalSection)
    (comparison : firstBundle ≅ secondBundle) :
    LineRationalSectionPresentation secondBundle
      (moduleStalkMap scheme (genericPoint scheme) comparison.hom rationalSection) where
  section_ne_zero := by
    exact (((moduleStalkFunctor scheme (genericPoint scheme)).mapIso comparison).toLinearEquiv.map_eq_zero_iff).not.mpr
      presentation.section_ne_zero
  cartier := presentation.cartier
  finite_index := presentation.finite_index
  generator := fun chart => comparison.hom.app (presentation.cartier.opens chart) (presentation.generator chart)
  frame := fun chart => (presentation.frame chart).mapIso comparison
  equation_eq := by
    intro chart nonempty
    let := nonempty
    rw [(presentation.frame chart).genericCoordinate_mapIso comparison rationalSection]
    exact presentation.equation_eq chart nonempty

theorem degreeOver_eq_of_change_section
    {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    [IsIntegral scheme] [IsNoetherian scheme] {bundle : scheme.Modules}
    {firstSection secondSection : bundle.presheaf.stalk (genericPoint scheme)}
    (first : LineRationalSectionPresentation bundle firstSection)
    (second : LineRationalSectionPresentation bundle secondSection)
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) :
    first.cartier.degreeOver structureMap dimensionBound =
      second.cartier.degreeOver structureMap dimensionBound := by
  obtain ⟨rational, _, difference⟩ := change_section_degreeOver first second structureMap dimensionBound
  have principalZero := rawZeroCycleDegree_principal_eq_zero structureMap dimensionBound rational
  change (principalCartierData rational).degreeOver structureMap dimensionBound = 0 at principalZero
  rw [principalZero] at difference
  exact sub_eq_zero.mp difference

theorem regular_of_globalSection
    {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]
    {bundle : scheme.Modules} (sectionValue : Γ(bundle, ⊤))
    (presentation : LineRationalSectionPresentation bundle
      (bundle.presheaf.germ ⊤ (genericPoint scheme) trivial sectionValue)) :
    presentation.cartier.IsRegular := by
  intro chart nonempty
  let := nonempty
  let region := presentation.cartier.opens chart
  refine ⟨(presentation.frame chart).coord le_rfl (bundle.res le_top sectionValue), ?_⟩
  rw [presentation.equation_eq chart nonempty]
  have germEquality : bundle.presheaf.germ ⊤ (genericPoint scheme) trivial sectionValue =
      bundle.presheaf.germ region (genericPoint scheme) (IsFrame.genericPoint_mem_region region)
        (bundle.res le_top sectionValue) :=
    (TopCat.Presheaf.germ_res_apply bundle.presheaf (homOfLE le_top)
      (genericPoint scheme) (IsFrame.genericPoint_mem_region region) sectionValue).symm
  exact ((presentation.frame chart).genericCoordinate_germ le_rfl
    (bundle.res le_top sectionValue)).symm.trans
      (congrArg (presentation.frame chart).genericCoordinate germEquality.symm)

end AlgebraicGeometry.Divisors.LineRationalSectionPresentation

namespace AlgebraicGeometry.Intersection

variable {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
  [IsIntegral scheme] [IsNoetherian scheme]

def HasLineBundleDegree (structureMap : scheme ⟶ Spec (CommRingCat.of baseField))
    [IsProper structureMap] (dimensionBound : topologicalKrullDim scheme ≤ 1)
    (bundle : scheme.Modules) (degreeValue : ℤ) : Prop :=
  ∃ rationalSection : bundle.presheaf.stalk (genericPoint scheme),
    ∃ presentation : LineRationalSectionPresentation bundle rationalSection,
      presentation.cartier.degreeOver structureMap dimensionBound = degreeValue

theorem hasLineBundleDegree_of_presentation
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) {bundle : scheme.Modules}
    {rationalSection : bundle.presheaf.stalk (genericPoint scheme)}
    (presentation : LineRationalSectionPresentation bundle rationalSection) :
    HasLineBundleDegree structureMap dimensionBound bundle
      (presentation.cartier.degreeOver structureMap dimensionBound) :=
  ⟨rationalSection, presentation, rfl⟩

theorem exists_lineBundleDegree
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] :
    ∃ degreeValue : ℤ, HasLineBundleDegree structureMap dimensionBound bundle degreeValue := by
  have : CompactSpace scheme := QuasiCompact.compactSpace_of_compactSpace structureMap
  obtain ⟨rationalSection, ⟨presentation⟩⟩ :=
    LineRationalSectionPresentation.exists_section_and_presentation bundle
  exact ⟨_, hasLineBundleDegree_of_presentation structureMap dimensionBound presentation⟩

theorem lineBundleDegree_value_unique
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) {bundle : scheme.Modules}
    {firstDegree secondDegree : ℤ}
    (first : HasLineBundleDegree structureMap dimensionBound bundle firstDegree)
    (second : HasLineBundleDegree structureMap dimensionBound bundle secondDegree) :
    firstDegree = secondDegree := by
  obtain ⟨_, firstPresentation, firstEquality⟩ := first
  obtain ⟨_, secondPresentation, secondEquality⟩ := second
  exact firstEquality.symm.trans
    ((firstPresentation.degreeOver_eq_of_change_section secondPresentation structureMap dimensionBound).trans
      secondEquality)

def lineBundleDegree
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] : ℤ :=
  Classical.choose (exists_lineBundleDegree structureMap dimensionBound bundle)

theorem hasLineBundleDegree_lineBundleDegree
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] :
    HasLineBundleDegree structureMap dimensionBound bundle
      (lineBundleDegree structureMap dimensionBound bundle) :=
  Classical.choose_spec (exists_lineBundleDegree structureMap dimensionBound bundle)

theorem lineBundleDegree_eq_of_presentation
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) {bundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    {rationalSection : bundle.presheaf.stalk (genericPoint scheme)}
    (presentation : LineRationalSectionPresentation bundle rationalSection) :
    lineBundleDegree structureMap dimensionBound bundle =
      presentation.cartier.degreeOver structureMap dimensionBound :=
  lineBundleDegree_value_unique structureMap dimensionBound
    (hasLineBundleDegree_lineBundleDegree structureMap dimensionBound bundle)
    (hasLineBundleDegree_of_presentation structureMap dimensionBound presentation)

theorem hasLineBundleDegree_iso_iff
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1)
    {firstBundle secondBundle : scheme.Modules} (comparison : firstBundle ≅ secondBundle)
    (degreeValue : ℤ) :
    HasLineBundleDegree structureMap dimensionBound firstBundle degreeValue ↔
      HasLineBundleDegree structureMap dimensionBound secondBundle degreeValue := by
  constructor
  · rintro ⟨rationalSection, presentation, degreeEquality⟩
    exact ⟨_, presentation.mapIso comparison, degreeEquality⟩
  · rintro ⟨rationalSection, presentation, degreeEquality⟩
    exact ⟨_, presentation.mapIso comparison.symm, degreeEquality⟩

theorem lineBundleDegree_eq_of_iso
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1)
    {firstBundle secondBundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme secondBundle]
    (comparison : firstBundle ≅ secondBundle) :
    lineBundleDegree structureMap dimensionBound firstBundle =
      lineBundleDegree structureMap dimensionBound secondBundle :=
  lineBundleDegree_value_unique structureMap dimensionBound
    ((hasLineBundleDegree_iso_iff structureMap dimensionBound comparison _).mp
      (hasLineBundleDegree_lineBundleDegree structureMap dimensionBound firstBundle))
    (hasLineBundleDegree_lineBundleDegree structureMap dimensionBound secondBundle)

theorem lineBundleDegree_nonneg_of_regular_presentation
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) {bundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    {rationalSection : bundle.presheaf.stalk (genericPoint scheme)}
    (presentation : LineRationalSectionPresentation bundle rationalSection)
    (regular : presentation.cartier.IsRegular) :
    0 ≤ lineBundleDegree structureMap dimensionBound bundle := by
  rw [lineBundleDegree_eq_of_presentation structureMap dimensionBound presentation]
  exact presentation.cartier.degreeOver_nonneg_of_regular structureMap dimensionBound regular

theorem lineBundleDegree_nonneg_of_nonzero_globalSection
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    (sectionValue : Γ(bundle, ⊤)) (nonzero : sectionValue ≠ 0) :
    0 ≤ lineBundleDegree structureMap dimensionBound bundle := by
  have : CompactSpace scheme := QuasiCompact.compactSpace_of_compactSpace structureMap
  have genericNonzero : bundle.presheaf.germ ⊤ (genericPoint scheme) trivial sectionValue ≠ 0 := by
    simpa only [map_zero] using
      (TauCeti.AlgebraicGeometry.InvertibleSheaf.germ_injective_of_isIntegral
        ⟨bundle, inferInstance⟩ (U := ⊤) (genericPoint scheme) trivial).ne nonzero
  obtain ⟨presentation⟩ := LineRationalSectionPresentation.exists_of_nonzero bundle
    (bundle.presheaf.germ ⊤ (genericPoint scheme) trivial sectionValue) genericNonzero
  exact lineBundleDegree_nonneg_of_regular_presentation structureMap dimensionBound presentation
    (presentation.regular_of_globalSection sectionValue)

end AlgebraicGeometry.Intersection

namespace IntegralCurve

variable {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
  [scheme.Over (Spec (CommRingCat.of baseField))]

def lineBundleDegree (curve : IntegralCurve baseField scheme) (bundle : curve.carrier.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible curve.carrier bundle] : ℤ :=
  Intersection.lineBundleDegree (curve.carrier ↘ Spec (CommRingCat.of baseField))
    curve.dim_eq_one.le bundle

theorem lineBundleDegree_eq_of_iso (curve : IntegralCurve baseField scheme)
    {firstBundle secondBundle : curve.carrier.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible curve.carrier firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible curve.carrier secondBundle]
    (comparison : firstBundle ≅ secondBundle) :
    curve.lineBundleDegree firstBundle = curve.lineBundleDegree secondBundle :=
  Intersection.lineBundleDegree_eq_of_iso (curve.carrier ↘ Spec (CommRingCat.of baseField))
    curve.dim_eq_one.le comparison

end IntegralCurve

namespace AlgebraicGeometry

variable {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
  [scheme.Over (Spec (CommRingCat.of baseField))]

def IsNef (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] : Prop :=
  ∀ curve : IntegralCurve baseField scheme,
    0 ≤ curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj bundle)

theorem IsNef.of_iso {firstBundle secondBundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme secondBundle]
    (comparison : firstBundle ≅ secondBundle) (nef : IsNef (baseField := baseField) firstBundle) :
    IsNef (baseField := baseField) secondBundle := by
  intro curve
  rw [← curve.lineBundleDegree_eq_of_iso ((Scheme.Modules.pullback curve.ι).mapIso comparison)]
  exact nef curve

theorem isNef_iff_of_iso {firstBundle secondBundle : scheme.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme firstBundle]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme secondBundle]
    (comparison : firstBundle ≅ secondBundle) :
    IsNef (baseField := baseField) firstBundle ↔ IsNef (baseField := baseField) secondBundle :=
  ⟨IsNef.of_iso comparison, IsNef.of_iso comparison.symm⟩

theorem isNef_of_nonzero_globalSection_on_every_curve_pullback (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    (sections : ∀ curve : IntegralCurve baseField scheme,
      ∃ sectionValue : Γ((Scheme.Modules.pullback curve.ι).obj bundle, ⊤), sectionValue ≠ 0) :
    IsNef (baseField := baseField) bundle := by
  intro curve
  obtain ⟨sectionValue, nonzero⟩ := sections curve
  exact Intersection.lineBundleDegree_nonneg_of_nonzero_globalSection
    (curve.carrier ↘ Spec (CommRingCat.of baseField)) curve.dim_eq_one.le
    ((Scheme.Modules.pullback curve.ι).obj bundle) sectionValue nonzero

end AlgebraicGeometry
