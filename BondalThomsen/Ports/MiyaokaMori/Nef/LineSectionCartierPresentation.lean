module

public import BondalThomsen.Ports.MiyaokaMori.Nef.FrameCoordinates
public import BondalThomsen.Ports.MiyaokaMori.Nef.CartierCurveDegree

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

section Ratio

variable {scheme : Scheme.{u}} [IsIntegral scheme] {bundle : scheme.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]

theorem frameSection_coordinate_unit_ratio {firstRegion secondRegion : scheme.Opens}
    {firstGenerator : Γ(bundle, firstRegion)} {secondGenerator : Γ(bundle, secondRegion)}
    (firstFrame : IsFrame bundle firstRegion firstGenerator)
    (secondFrame : IsFrame bundle secondRegion secondGenerator)
    [Nonempty firstRegion] [Nonempty secondRegion] [Nonempty ↑(firstRegion ⊓ secondRegion)]
    (sectionValue : Γ(bundle, ⊤)) (nonzero : sectionValue ≠ 0) :
    ∃ unit : Γ(scheme, firstRegion ⊓ secondRegion)ˣ,
      scheme.germToFunctionField (firstRegion ⊓ secondRegion) unit =
        scheme.germToFunctionField firstRegion
          (firstFrame.coord le_rfl (bundle.res le_top sectionValue)) /
        scheme.germToFunctionField secondRegion
          (secondFrame.coord le_rfl (bundle.res le_top sectionValue)) := by
  let overlap := firstRegion ⊓ secondRegion
  let firstOverlap := firstFrame.restrict (inf_le_left : overlap ≤ firstRegion)
  let secondOverlap := secondFrame.restrict (inf_le_right : overlap ≤ secondRegion)
  obtain ⟨unit, generatorEquation⟩ := firstOverlap.unit_transition secondOverlap
  let restricted := bundle.res (le_top : overlap ≤ ⊤) sectionValue
  have coordinateEquation : firstOverlap.coord le_rfl restricted =
      (unit : Γ(scheme, overlap)) * secondOverlap.coord le_rfl restricted := by
    apply firstOverlap.coord_unique
    simp only [res_self]
    rw [mul_comm, mul_smul, generatorEquation]
    simpa only [res_self] using secondOverlap.coord_smul_frame le_rfl restricted
  have firstRestriction : scheme.germToFunctionField firstRegion
      (firstFrame.coord le_rfl (bundle.res le_top sectionValue)) =
      scheme.germToFunctionField overlap (firstOverlap.coord le_rfl restricted) := by
    have coordinateRestriction := firstFrame.coord_map (inf_le_left : overlap ≤ firstRegion)
      le_rfl (bundle.res le_top sectionValue)
    simp only [res_res] at coordinateRestriction
    rw [firstFrame.coord_restrict inf_le_left restricted, coordinateRestriction]
    exact (scheme.presheaf.germ_res_apply (homOfLE inf_le_left)
      (genericPoint scheme) (by
        obtain ⟨point, contains⟩ := (inferInstance : Nonempty overlap)
        exact (genericPoint_specializes point).mem_open overlap.isOpen contains) _).symm
  have secondRestriction : scheme.germToFunctionField secondRegion
      (secondFrame.coord le_rfl (bundle.res le_top sectionValue)) =
      scheme.germToFunctionField overlap (secondOverlap.coord le_rfl restricted) := by
    have coordinateRestriction := secondFrame.coord_map (inf_le_right : overlap ≤ secondRegion)
      le_rfl (bundle.res le_top sectionValue)
    simp only [res_res] at coordinateRestriction
    rw [secondFrame.coord_restrict inf_le_right restricted, coordinateRestriction]
    exact (scheme.presheaf.germ_res_apply (homOfLE inf_le_right)
      (genericPoint scheme) (by
        obtain ⟨point, contains⟩ := (inferInstance : Nonempty overlap)
        exact (genericPoint_specializes point).mem_open overlap.isOpen contains) _).symm
  have denominatorNonzero : scheme.germToFunctionField overlap
      (secondOverlap.coord le_rfl restricted) ≠ 0 := by
    rw [← secondRestriction]
    intro zero
    exact secondFrame.coord_globalSection_ne_zero sectionValue nonzero
      (scheme.germToFunctionField_injective secondRegion (zero.trans (map_zero _).symm))
  refine ⟨unit, ?_⟩
  rw [firstRestriction, secondRestriction, coordinateEquation, map_mul,
    mul_div_cancel_right₀ _ denominatorNonzero]

end Ratio

structure LineSectionCartierPresentation {scheme : Scheme.{u}} [IsIntegral scheme]
    [IsLocallyNoetherian scheme] (bundle : scheme.Modules) (sectionValue : Γ(bundle, ⊤)) where
  section_ne_zero : sectionValue ≠ 0
  cartier : CartierLocalData scheme
  generator : ∀ chart, Γ(bundle, cartier.opens chart)
  frame : ∀ chart, IsFrame bundle (cartier.opens chart) (generator chart)
  equation_eq : ∀ chart (nonempty : Nonempty (cartier.opens chart)),
    letI : Nonempty (cartier.opens chart) := nonempty
    cartier.equation chart = scheme.germToFunctionField (cartier.opens chart)
      ((frame chart).coord le_rfl (bundle.res le_top sectionValue))

namespace LineSectionCartierPresentation

section Construction

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]
  (bundle : scheme.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
  (sectionValue : Γ(bundle, ⊤)) (nonzero : sectionValue ≠ 0)

def ofFiniteFrames {index : Type u} [Finite index] (regions : index → scheme.Opens)
    (nonempty : ∀ chart, Nonempty (regions chart))
    (cover : ⋃ chart, (regions chart : Set scheme) = Set.univ)
    (generators : ∀ chart, Γ(bundle, regions chart))
    (frames : ∀ chart, IsFrame bundle (regions chart) (generators chart)) :
    LineSectionCartierPresentation bundle sectionValue where
  section_ne_zero := nonzero
  cartier :=
    { index := index
      opens := regions
      cover := cover
      locallyFinite := locallyFinite_of_finite _
      equation := fun chart =>
        @Scheme.germToFunctionField scheme _ (regions chart) (nonempty chart)
          ((frames chart).coord le_rfl (bundle.res le_top sectionValue))
      equation_ne_zero := by
        intro chart
        let : Nonempty (regions chart) := nonempty chart
        intro zero
        exact (frames chart).coord_globalSection_ne_zero sectionValue nonzero
          (scheme.germToFunctionField_injective (regions chart) (zero.trans (map_zero _).symm))
      ratio_unit := by
        intro first second overlapNonempty
        let : Nonempty (regions first) := nonempty first
        let : Nonempty (regions second) := nonempty second
        let : Nonempty ↑(regions first ⊓ regions second) := overlapNonempty
        obtain ⟨unit, equation⟩ := frameSection_coordinate_unit_ratio
          (frames first) (frames second) sectionValue nonzero
        exact ⟨unit, unit.isUnit, equation⟩ }
  generator := generators
  frame := frames
  equation_eq := fun _ _ => rfl

include nonzero in
theorem exists_of_nonzero [CompactSpace scheme] :
    Nonempty (LineSectionCartierPresentation bundle sectionValue) := by
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
  exact ⟨ofFiniteFrames bundle sectionValue nonzero (fun point : indices => regions point.1)
    (fun point => ⟨⟨point.1, contains point.1⟩⟩) restrictedCover
    (fun point => generators point.1) (fun point => frames point.1)⟩

end Construction

section Independence

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]
  {bundle : scheme.Modules} [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
  {sectionValue : Γ(bundle, ⊤)}

omit [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] in
theorem regular (presentation : LineSectionCartierPresentation bundle sectionValue) :
    presentation.cartier.IsRegular := by
  intro chart nonempty
  let : Nonempty (presentation.cartier.opens chart) := nonempty
  exact ⟨(presentation.frame chart).coord le_rfl (bundle.res le_top sectionValue),
    (presentation.equation_eq chart nonempty).symm⟩

theorem coefficient_eq (first second : LineSectionCartierPresentation bundle sectionValue) :
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
  obtain ⟨unit, equation⟩ := frameSection_coordinate_unit_ratio
    (first.frame firstChart) (second.frame secondChart) sectionValue first.section_ne_zero
  refine ⟨unit, unit.isUnit, ?_⟩
  rw [first.equation_eq firstChart inferInstance, second.equation_eq secondChart inferInstance]
  exact equation

end Independence

section Degree

variable {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
  [IsIntegral scheme] [IsNoetherian scheme] {bundle : scheme.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle]
  {sectionValue : Γ(bundle, ⊤)}

def degreeOver (presentation : LineSectionCartierPresentation bundle sectionValue)
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) : ℤ :=
  presentation.cartier.degreeOver structureMap dimensionBound

end Degree

end LineSectionCartierPresentation

end AlgebraicGeometry.Divisors

