module

public import BondalThomsen.Ports.MiyaokaMori.Nef.GenericFrameCoordinates
public import BondalThomsen.Ports.MiyaokaMori.Nef.LineBundleCurveDegree

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

structure LineRationalSectionPresentation {scheme : Scheme.{u}} [IsIntegral scheme]
    [IsLocallyNoetherian scheme] (bundle : scheme.Modules)
    (rationalSection : bundle.presheaf.stalk (genericPoint scheme)) where
  section_ne_zero : rationalSection ≠ 0
  cartier : CartierLocalData scheme
  finite_index : Finite cartier.index
  generator : ∀ chart, Γ(bundle, cartier.opens chart)
  frame : ∀ chart, IsFrame bundle (cartier.opens chart) (generator chart)
  equation_eq : ∀ chart (nonempty : Nonempty (cartier.opens chart)),
    letI : Nonempty (cartier.opens chart) := nonempty
    cartier.equation chart = (frame chart).genericCoordinate rationalSection

namespace LineRationalSectionPresentation

section Local

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]

def ofFiniteFrames (bundle : scheme.Modules) {index : Type u} [Finite index]
    (regions : index → scheme.Opens) (nonempty : ∀ chart, Nonempty (regions chart))
    (cover : ⋃ chart, (regions chart : Set scheme) = Set.univ)
    (generators : ∀ chart, Γ(bundle, regions chart))
    (frames : ∀ chart, IsFrame bundle (regions chart) (generators chart))
    (rationalSection : bundle.presheaf.stalk (genericPoint scheme))
    (nonzero : rationalSection ≠ 0) : LineRationalSectionPresentation bundle rationalSection where
  section_ne_zero := nonzero
  cartier :=
    { index := index
      opens := regions
      cover := cover
      locallyFinite := locallyFinite_of_finite _
      equation := fun chart =>
        @IsFrame.genericCoordinate scheme _ bundle (regions chart) (generators chart)
          (frames chart) (nonempty chart) rationalSection
      equation_ne_zero := by
        intro chart
        let : Nonempty (regions chart) := nonempty chart
        exact (frames chart).genericCoordinate_ne_zero rationalSection nonzero
      ratio_unit := by
        intro first second overlapNonempty
        let : Nonempty (regions first) := nonempty first
        let : Nonempty (regions second) := nonempty second
        let : Nonempty ↑(regions first ⊓ regions second) := overlapNonempty
        obtain ⟨unit, transition⟩ := (frames first).genericCoordinate_transition (frames second)
        refine ⟨unit, unit.isUnit, ?_⟩
        rw [transition rationalSection,
          mul_div_cancel_right₀ _ ((frames second).genericCoordinate_ne_zero rationalSection nonzero)] }
  finite_index := inferInstance
  generator := generators
  frame := frames
  equation_eq := fun _ _ => rfl

theorem exists_of_nonzero [CompactSpace scheme] (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
    (rationalSection : bundle.presheaf.stalk (genericPoint scheme)) (nonzero : rationalSection ≠ 0) :
    Nonempty (LineRationalSectionPresentation bundle rationalSection) := by
  choose regions contains generators frames using fun point : scheme => exists_frame bundle point
  have cover : ⋃ point, (regions point : Set scheme) = Set.univ :=
    Set.eq_univ_of_forall fun point => Set.mem_iUnion.mpr ⟨point, contains point⟩
  obtain ⟨points, finiteCover⟩ := isCompact_univ.elim_finite_subcover
    (fun point => (regions point : Set scheme)) (fun point => (regions point).isOpen) cover.ge
  let indices := {point : scheme // point ∈ points}
  have restrictedCover : ⋃ point : indices, (regions point.1 : Set scheme) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro point
    obtain ⟨chart, member, chartContains⟩ := Set.mem_iUnion₂.mp (finiteCover (Set.mem_univ point))
    exact Set.mem_iUnion.mpr ⟨⟨chart, member⟩, chartContains⟩
  exact ⟨ofFiniteFrames bundle (fun point : indices => regions point.1)
    (fun point => ⟨⟨point.1, contains point.1⟩⟩) restrictedCover
    (fun point => generators point.1) (fun point => frames point.1) rationalSection nonzero⟩

theorem exists_section_and_presentation [CompactSpace scheme] (bundle : scheme.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] :
    ∃ rationalSection : bundle.presheaf.stalk (genericPoint scheme),
      Nonempty (LineRationalSectionPresentation bundle rationalSection) := by
  obtain ⟨rationalSection, nonzero⟩ := exists_nonzero_genericSection bundle
  exact ⟨rationalSection, exists_of_nonzero bundle rationalSection nonzero⟩

variable {bundle : scheme.Modules}

theorem coefficient_eq {rationalSection : bundle.presheaf.stalk (genericPoint scheme)}
    (first second : LineRationalSectionPresentation bundle rationalSection) :
    first.cartier.coefficient = second.cartier.coefficient := by
  apply CartierLocalData.coefficient_eq_of_unit_related_local_equations
  intro point
  let firstChart := first.cartier.indexAt point
  let secondChart := second.cartier.indexAt point
  have firstContains := first.cartier.indexAt_mem point
  have secondContains := second.cartier.indexAt_mem point
  refine ⟨firstChart, secondChart, firstContains, secondContains, ?_⟩
  intro overlapNonempty
  let : Nonempty (first.cartier.opens firstChart) := ⟨⟨point, firstContains⟩⟩
  let : Nonempty (second.cartier.opens secondChart) := ⟨⟨point, secondContains⟩⟩
  let : Nonempty ↑(first.cartier.opens firstChart ⊓ second.cartier.opens secondChart) := overlapNonempty
  obtain ⟨unit, transition⟩ := (first.frame firstChart).genericCoordinate_transition (second.frame secondChart)
  refine ⟨unit, unit.isUnit, ?_⟩
  rw [first.equation_eq firstChart inferInstance, second.equation_eq secondChart inferInstance,
    transition rationalSection,
    mul_div_cancel_right₀ _ ((second.frame secondChart).genericCoordinate_ne_zero
      rationalSection second.section_ne_zero)]

theorem change_section {firstSection secondSection : bundle.presheaf.stalk (genericPoint scheme)}
    (first : LineRationalSectionPresentation bundle firstSection)
    (second : LineRationalSectionPresentation bundle secondSection) :
    ∃ rational : scheme.functionFieldˣ, firstSection = (rational : scheme.functionField) • secondSection ∧
      ∀ point : scheme, first.cartier.coefficient point =
        second.cartier.coefficient point + scheme.ord (rational : scheme.functionField) point := by
  let selected := second.cartier.indexAt (genericPoint scheme)
  let : Nonempty (second.cartier.opens selected) :=
    ⟨⟨genericPoint scheme, second.cartier.indexAt_mem (genericPoint scheme)⟩⟩
  let coordinates := (second.frame selected).genericCoordinate
  let rational : scheme.functionFieldˣ := Units.mk0 (coordinates firstSection / coordinates secondSection)
    (div_ne_zero ((second.frame selected).genericCoordinate_ne_zero firstSection first.section_ne_zero)
      ((second.frame selected).genericCoordinate_ne_zero secondSection second.section_ne_zero))
  have sectionEquation : firstSection = (rational : scheme.functionField) • secondSection := by
    apply coordinates.injective
    rw [_root_.map_smul, smul_eq_mul]
    exact (div_mul_cancel₀ _ ((second.frame selected).genericCoordinate_ne_zero
      secondSection second.section_ne_zero)).symm
  let changed : LineRationalSectionPresentation bundle firstSection :=
    { section_ne_zero := first.section_ne_zero
      cartier :=
        { index := second.cartier.index
          opens := second.cartier.opens
          cover := second.cartier.cover
          locallyFinite := second.cartier.locallyFinite
          equation := fun chart => (rational : scheme.functionField) * second.cartier.equation chart
          equation_ne_zero := fun chart => mul_ne_zero rational.ne_zero (second.cartier.equation_ne_zero chart)
          ratio_unit := by
            intro firstChart secondChart nonempty
            obtain ⟨unit, unitProof, equation⟩ := second.cartier.ratio_unit firstChart secondChart nonempty
            exact ⟨unit, unitProof, equation.trans (mul_div_mul_left _ _ rational.ne_zero).symm⟩ }
      finite_index := second.finite_index
      generator := second.generator
      frame := second.frame
      equation_eq := by
        intro chart nonempty
        let : Nonempty (second.cartier.opens chart) := nonempty
        change (rational : scheme.functionField) * second.cartier.equation chart =
          (second.frame chart).genericCoordinate firstSection
        rw [sectionEquation, _root_.map_smul, smul_eq_mul, second.equation_eq chart nonempty] }
  refine ⟨rational, sectionEquation, fun point => ?_⟩
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

section Cycles

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsNoetherian scheme]
  {bundle : scheme.Modules}

theorem change_section_zeroCycle {firstSection secondSection : bundle.presheaf.stalk (genericPoint scheme)}
    (first : LineRationalSectionPresentation bundle firstSection)
    (second : LineRationalSectionPresentation bundle secondSection)
    (dimensionBound : topologicalKrullDim scheme ≤ 1) :
    ∃ rational : scheme.functionFieldˣ, firstSection = (rational : scheme.functionField) • secondSection ∧
      first.cartier.zeroCycle dimensionBound = DimensionCycle.add (second.cartier.zeroCycle dimensionBound)
        ((principalCartierData rational).zeroCycle dimensionBound) := by
  obtain ⟨rational, sectionEquation, coefficients⟩ := change_section first second
  refine ⟨rational, sectionEquation, ?_⟩
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro point
  change first.cartier.coefficient point = second.cartier.coefficient point +
    (principalCartierData rational).coefficient point
  rw [principalCartierData_coefficient]
  exact coefficients point

theorem change_section_degreeOver {baseField : Type u} [Field baseField]
    {firstSection secondSection : bundle.presheaf.stalk (genericPoint scheme)}
    (first : LineRationalSectionPresentation bundle firstSection)
    (second : LineRationalSectionPresentation bundle secondSection)
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) :
    ∃ rational : scheme.functionFieldˣ, firstSection = (rational : scheme.functionField) • secondSection ∧
      first.cartier.degreeOver structureMap dimensionBound -
        second.cartier.degreeOver structureMap dimensionBound =
          (principalCartierData rational).degreeOver structureMap dimensionBound := by
  obtain ⟨rational, sectionEquation, cycles⟩ := change_section_zeroCycle first second dimensionBound
  refine ⟨rational, sectionEquation, ?_⟩
  unfold CartierLocalData.degreeOver
  rw [cycles, rawZeroCycleDegree_add, add_sub_cancel_left]

end Cycles

end LineRationalSectionPresentation

end AlgebraicGeometry.Divisors

