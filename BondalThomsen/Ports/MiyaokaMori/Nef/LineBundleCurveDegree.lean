module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LineSectionCartierPresentation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Intersection
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry.Divisors

section Coordinates

variable {scheme : Scheme.{u}} [IsIntegral scheme] {bundle : scheme.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]

def frameRationalCoordinate {region : scheme.Opens} {generator : Γ(bundle, region)}
    (frame : IsFrame bundle region generator) [Nonempty region]
    (sectionValue : Γ(bundle, ⊤)) : scheme.functionField :=
  scheme.germToFunctionField region (frame.coord le_rfl (bundle.res le_top sectionValue))

theorem frameRationalCoordinate_ne_zero {region : scheme.Opens} {generator : Γ(bundle, region)}
    (frame : IsFrame bundle region generator) [Nonempty region]
    (sectionValue : Γ(bundle, ⊤)) (nonzero : sectionValue ≠ 0) :
    frameRationalCoordinate frame sectionValue ≠ 0 := by
  intro zero
  exact frame.coord_globalSection_ne_zero sectionValue nonzero
    (scheme.germToFunctionField_injective region (zero.trans (map_zero _).symm))

omit [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] in
theorem frameRationalCoordinate_transition {firstRegion secondRegion : scheme.Opens}
    {firstGenerator : Γ(bundle, firstRegion)} {secondGenerator : Γ(bundle, secondRegion)}
    (firstFrame : IsFrame bundle firstRegion firstGenerator)
    (secondFrame : IsFrame bundle secondRegion secondGenerator)
    [Nonempty firstRegion] [Nonempty secondRegion] [Nonempty ↑(firstRegion ⊓ secondRegion)] :
    ∃ unit : Γ(scheme, firstRegion ⊓ secondRegion)ˣ, ∀ sectionValue : Γ(bundle, ⊤),
      frameRationalCoordinate firstFrame sectionValue =
        scheme.germToFunctionField (firstRegion ⊓ secondRegion) unit *
          frameRationalCoordinate secondFrame sectionValue := by
  let overlap := firstRegion ⊓ secondRegion
  let firstOverlap := firstFrame.restrict (inf_le_left : overlap ≤ firstRegion)
  let secondOverlap := secondFrame.restrict (inf_le_right : overlap ≤ secondRegion)
  obtain ⟨unit, generatorEquation⟩ := firstOverlap.unit_transition secondOverlap
  refine ⟨unit, fun sectionValue => ?_⟩
  let restricted := bundle.res (le_top : overlap ≤ ⊤) sectionValue
  have coordinateEquation : firstOverlap.coord le_rfl restricted =
      (unit : Γ(scheme, overlap)) * secondOverlap.coord le_rfl restricted := by
    apply firstOverlap.coord_unique
    simp only [res_self]
    rw [mul_comm, mul_smul, generatorEquation]
    simpa only [res_self] using secondOverlap.coord_smul_frame le_rfl restricted
  have firstRestriction : frameRationalCoordinate firstFrame sectionValue =
      scheme.germToFunctionField overlap (firstOverlap.coord le_rfl restricted) := by
    have coordinateRestriction := firstFrame.coord_map (inf_le_left : overlap ≤ firstRegion)
      le_rfl (bundle.res le_top sectionValue)
    simp only [res_res] at coordinateRestriction
    rw [firstFrame.coord_restrict inf_le_left restricted, coordinateRestriction]
    exact (scheme.presheaf.germ_res_apply (homOfLE inf_le_left)
      (genericPoint scheme) (by
        obtain ⟨point, contains⟩ := (inferInstance : Nonempty overlap)
        exact (genericPoint_specializes point).mem_open overlap.isOpen contains) _).symm
  have secondRestriction : frameRationalCoordinate secondFrame sectionValue =
      scheme.germToFunctionField overlap (secondOverlap.coord le_rfl restricted) := by
    have coordinateRestriction := secondFrame.coord_map (inf_le_right : overlap ≤ secondRegion)
      le_rfl (bundle.res le_top sectionValue)
    simp only [res_res] at coordinateRestriction
    rw [secondFrame.coord_restrict inf_le_right restricted, coordinateRestriction]
    exact (scheme.presheaf.germ_res_apply (homOfLE inf_le_right)
      (genericPoint scheme) (by
        obtain ⟨point, contains⟩ := (inferInstance : Nonempty overlap)
        exact (genericPoint_specializes point).mem_open overlap.isOpen contains) _).symm
  rw [firstRestriction, secondRestriction, coordinateEquation, map_mul]

omit [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] in
theorem frameRationalCoordinate_ratio_eq {firstRegion secondRegion : scheme.Opens}
    {firstGenerator : Γ(bundle, firstRegion)} {secondGenerator : Γ(bundle, secondRegion)}
    (firstFrame : IsFrame bundle firstRegion firstGenerator)
    (secondFrame : IsFrame bundle secondRegion secondGenerator)
    [Nonempty firstRegion] [Nonempty secondRegion]
    (firstSection secondSection : Γ(bundle, ⊤)) :
    frameRationalCoordinate firstFrame firstSection /
        frameRationalCoordinate firstFrame secondSection =
      frameRationalCoordinate secondFrame firstSection /
        frameRationalCoordinate secondFrame secondSection := by
  let : Nonempty ↑(firstRegion ⊓ secondRegion) := ⟨⟨genericPoint scheme, by
    constructor
    · obtain ⟨point, contains⟩ := (inferInstance : Nonempty firstRegion)
      exact (genericPoint_specializes point).mem_open firstRegion.isOpen contains
    · obtain ⟨point, contains⟩ := (inferInstance : Nonempty secondRegion)
      exact (genericPoint_specializes point).mem_open secondRegion.isOpen contains⟩⟩
  obtain ⟨unit, transition⟩ := frameRationalCoordinate_transition firstFrame secondFrame
  have unitNonzero : scheme.germToFunctionField (firstRegion ⊓ secondRegion) unit ≠ 0 := by
    intro zero
    exact unit.ne_zero (scheme.germToFunctionField_injective (firstRegion ⊓ secondRegion)
      (zero.trans (map_zero _).symm))
  rw [transition firstSection, transition secondSection, mul_div_mul_left _ _ unitNonzero]

end Coordinates

namespace LineSectionCartierPresentation

section Local

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]
  {bundle : scheme.Modules} [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
  {firstSection secondSection : Γ(bundle, ⊤)}

theorem change_section (first : LineSectionCartierPresentation bundle firstSection)
    (second : LineSectionCartierPresentation bundle secondSection) :
    ∃ rational : scheme.functionFieldˣ,
      (∀ chart (nonempty : Nonempty (second.cartier.opens chart)),
        letI : Nonempty (second.cartier.opens chart) := nonempty
        frameRationalCoordinate (second.frame chart) firstSection =
          (rational : scheme.functionField) * second.cartier.equation chart) ∧
      ∀ point : scheme, first.cartier.coefficient point =
        second.cartier.coefficient point + scheme.ord (rational : scheme.functionField) point := by
  let selected := second.cartier.indexAt (genericPoint scheme)
  let : Nonempty (second.cartier.opens selected) :=
    ⟨⟨genericPoint scheme, second.cartier.indexAt_mem (genericPoint scheme)⟩⟩
  let numerator := frameRationalCoordinate (second.frame selected) firstSection
  let denominator := frameRationalCoordinate (second.frame selected) secondSection
  have numeratorNonzero : numerator ≠ 0 :=
    frameRationalCoordinate_ne_zero _ firstSection first.section_ne_zero
  have denominatorNonzero : denominator ≠ 0 :=
    frameRationalCoordinate_ne_zero _ secondSection second.section_ne_zero
  let rational : scheme.functionFieldˣ :=
    Units.mk0 (numerator / denominator) (div_ne_zero numeratorNonzero denominatorNonzero)
  have coordinateEquation : ∀ chart (nonempty : Nonempty (second.cartier.opens chart)),
      letI : Nonempty (second.cartier.opens chart) := nonempty
      frameRationalCoordinate (second.frame chart) firstSection =
        (rational : scheme.functionField) * second.cartier.equation chart := by
    intro chart nonempty
    let : Nonempty (second.cartier.opens chart) := nonempty
    have ratioEquation := frameRationalCoordinate_ratio_eq (second.frame chart)
      (second.frame selected) firstSection secondSection
    have equationNonzero := frameRationalCoordinate_ne_zero (second.frame chart)
      secondSection second.section_ne_zero
    rw [second.equation_eq chart nonempty]
    exact (div_eq_iff equationNonzero).mp ratioEquation
  let changed : LineSectionCartierPresentation bundle firstSection :=
    { section_ne_zero := first.section_ne_zero
      cartier :=
        { index := second.cartier.index
          opens := second.cartier.opens
          cover := second.cartier.cover
          locallyFinite := second.cartier.locallyFinite
          equation := fun chart => (rational : scheme.functionField) * second.cartier.equation chart
          equation_ne_zero := fun chart => mul_ne_zero rational.ne_zero
            (second.cartier.equation_ne_zero chart)
          ratio_unit := by
            intro firstChart secondChart nonempty
            obtain ⟨unit, unitProof, ratioEquation⟩ :=
              second.cartier.ratio_unit firstChart secondChart nonempty
            refine ⟨unit, unitProof, ?_⟩
            exact ratioEquation.trans
              (mul_div_mul_left _ _ rational.ne_zero).symm }
      generator := second.generator
      frame := second.frame
      equation_eq := fun chart nonempty => (coordinateEquation chart nonempty).symm }
  refine ⟨rational, coordinateEquation, fun point => ?_⟩
  rw [congrFun (coefficient_eq first changed) point]
  by_cases coheightOne : Order.coheight point = 1
  · rw [changed.cartier.coefficient_eq_ord point coheightOne,
      second.cartier.coefficient_eq_ord point coheightOne]
    change scheme.ord ((rational : scheme.functionField) *
        second.cartier.equation (second.cartier.indexAt point)) point = _
    rw [Scheme.ord_mul rational.ne_zero (second.cartier.equation_ne_zero _), add_comm]
  · rw [changed.cartier.coefficient_eq_zero_of_coheight_ne_one point coheightOne,
      second.cartier.coefficient_eq_zero_of_coheight_ne_one point coheightOne,
      Scheme.ord_eq_zero_of_coheight_neq_one coheightOne, add_zero]

end Local

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsNoetherian scheme]
  {bundle : scheme.Modules} [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
  {firstSection secondSection : Γ(bundle, ⊤)}

theorem change_section_zeroCycle (first : LineSectionCartierPresentation bundle firstSection)
    (second : LineSectionCartierPresentation bundle secondSection)
    (dimensionBound : topologicalKrullDim scheme ≤ 1) :
    ∃ rational : scheme.functionFieldˣ, first.cartier.zeroCycle dimensionBound =
      DimensionCycle.add (second.cartier.zeroCycle dimensionBound)
        ((principalCartierData rational).zeroCycle dimensionBound) := by
  obtain ⟨rational, _, coefficients⟩ := change_section first second
  refine ⟨rational, ?_⟩
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro point
  change first.cartier.coefficient point = second.cartier.coefficient point +
    (principalCartierData rational).coefficient point
  rw [principalCartierData_coefficient]
  exact coefficients point

theorem change_section_degreeOver {baseField : Type u} [Field baseField]
    (first : LineSectionCartierPresentation bundle firstSection)
    (second : LineSectionCartierPresentation bundle secondSection)
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) :
    ∃ rational : scheme.functionFieldˣ, first.degreeOver structureMap dimensionBound =
      second.degreeOver structureMap dimensionBound +
        (principalCartierData rational).degreeOver structureMap dimensionBound := by
  obtain ⟨rational, cycles⟩ := change_section_zeroCycle first second dimensionBound
  refine ⟨rational, ?_⟩
  unfold degreeOver CartierLocalData.degreeOver
  rw [cycles, rawZeroCycleDegree_add]

end LineSectionCartierPresentation

end AlgebraicGeometry.Divisors

