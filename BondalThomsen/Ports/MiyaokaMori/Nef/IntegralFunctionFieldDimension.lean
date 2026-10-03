module

public import BondalThomsen.Ports.MiyaokaMori.Nef.FiniteTypeDomainDimension
public import BondalThomsen.Ports.MiyaokaMori.Nef.DominantAffineAlgebra
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry.IntegralFunctionFieldDimension

theorem topologicalKrullDim_eq_iSup_openCover {source : Scheme.{u}} (cover : source.OpenCover) :
    topologicalKrullDim source = ⨆ chart, topologicalKrullDim (cover.X chart) := by
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun closedSubset => ?_
    obtain ⟨point, pointMember⟩ := closedSubset.isIrreducible.nonempty
    obtain ⟨chartPoint, chartEquality⟩ := cover.covers point
    have chartOpen : Topology.IsOpenEmbedding (cover.f (cover.idx point)) :=
      (cover.f (cover.idx point)).isOpenEmbedding
    have nonemptyPreimage : ((cover.f (cover.idx point)) ⁻¹' (closedSubset : Set source)).Nonempty :=
      ⟨chartPoint, by simpa [chartEquality] using pointMember⟩
    have closedEquality : closedSubset =
        IrreducibleCloseds.map (cover.f (cover.idx point)) chartOpen.continuous
          ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ chartOpen).symm
            ⟨closedSubset, nonemptyPreimage⟩) :=
      congrArg Subtype.val
        ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ chartOpen).apply_symm_apply
          ⟨closedSubset, nonemptyPreimage⟩).symm
    rw [closedEquality, chartOpen.coheight_map]
    exact (Order.coheight_le_krullDim _).trans
      (le_iSup (fun chart => topologicalKrullDim (cover.X chart)) (cover.idx point))
  · exact iSup_le fun chart => (cover.f chart).isOpenEmbedding.isInducing.topologicalKrullDim_le

@[reducible] def baseFunctionFieldAlgebra {baseField : Type u} [Field baseField]
    {source : Scheme.{u}} [IsIntegral source] (structureMap : source ⟶ Spec (CommRingCat.of baseField)) :
    Algebra baseField source.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of baseField)).inv ≫ structureMap.appTop ≫
    source.presheaf.germ ⊤ (genericPoint source) trivial).hom.toAlgebra

@[reducible] def baseSectionAlgebra {baseField : Type u} [Field baseField]
    {source : Scheme.{u}} (structureMap : source ⟶ Spec (CommRingCat.of baseField))
    (region : source.Opens) : Algebra baseField Γ(source, region) :=
  ((Scheme.ΓSpecIso (CommRingCat.of baseField)).inv ≫ structureMap.appLE ⊤ region le_top).hom.toAlgebra

theorem baseSectionAlgebra_finiteType {baseField : Type u} [Field baseField]
    {source : Scheme.{u}} (structureMap : source ⟶ Spec (CommRingCat.of baseField))
    [LocallyOfFiniteType structureMap] {region : source.Opens} (affine : IsAffineOpen region) :
    letI := baseSectionAlgebra structureMap region
    Algebra.FiniteType baseField Γ(source, region) := by
  have sectionFinite : (structureMap.appLE ⊤ region le_top).hom.FiniteType :=
    structureMap.finiteType_appLE (isAffineOpen_top _) affine _
  have specFinite : ((Scheme.ΓSpecIso (CommRingCat.of baseField)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of baseField)).symm.commRingCatIsoToRingEquiv.surjective
  exact sectionFinite.comp specFinite

theorem baseSectionFunctionField_tower {baseField : Type u} [Field baseField]
    {source : Scheme.{u}} [IsIntegral source]
    (structureMap : source ⟶ Spec (CommRingCat.of baseField))
    (region : source.Opens) [Nonempty region] :
    letI := baseFunctionFieldAlgebra structureMap
    letI := baseSectionAlgebra structureMap region
    IsScalarTower baseField Γ(source, region) source.functionField := by
  let := baseFunctionFieldAlgebra structureMap
  let := baseSectionAlgebra structureMap region
  have genericInRegion : genericPoint source ∈ region :=
    genericPoint_mem_of_nonempty region (by simpa using (show Nonempty region from inferInstance))
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext element
  simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (congrArg (fun ringMap : Γ(source, ⊤) ⟶ source.functionField =>
    ringMap.hom (structureMap.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of baseField)).inv.hom element)))
      (source.presheaf.germ_res (homOfLE le_top) (genericPoint source) genericInRegion)).symm

theorem affine_dimension_eq_functionField_trdeg {baseField : Type u} [Field baseField]
    {source : Scheme.{u}} [IsIntegral source]
    (structureMap : source ⟶ Spec (CommRingCat.of baseField)) [LocallyOfFiniteType structureMap]
    {region : source.Opens} (affine : IsAffineOpen region) [Nonempty region] :
    letI := baseFunctionFieldAlgebra structureMap
    topologicalKrullDim region =
      (Cardinal.toENat (Algebra.trdeg baseField source.functionField) : WithBot ℕ∞) := by
  let := baseFunctionFieldAlgebra structureMap
  let := baseSectionAlgebra structureMap region
  have := baseSectionAlgebra_finiteType structureMap affine
  have := functionField_isFractionRing_of_isAffineOpen source region affine
  have := baseSectionFunctionField_tower structureMap region
  have : FaithfulSMul Γ(source, region) source.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  have : Algebra.IsAlgebraic Γ(source, region) source.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(source, region))
  have fieldTrdeg : Algebra.trdeg baseField source.functionField =
      Algebra.trdeg baseField Γ(source, region) := by
    have relativeTrdegZero : Algebra.trdeg Γ(source, region) source.functionField = 0 :=
      trdeg_eq_zero
    rw [← trdeg_add_eq baseField Γ(source, region) (A := source.functionField),
      relativeTrdegZero, add_zero]
  rw [IsHomeomorph.topologicalKrullDim_eq _ affine.isoSpec.hom.homeomorph.isHomeomorph]
  erw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(source, region)]
  rw [MiyaokaMori.RingTheory.finiteTypeDomain_ringKrullDim_eq_trdeg baseField Γ(source, region),
    fieldTrdeg]

theorem topologicalKrullDim_eq_trdeg_functionField {baseField : Type u} [Field baseField]
    {source : Scheme.{u}} [IsIntegral source]
    (structureMap : source ⟶ Spec (CommRingCat.of baseField)) [LocallyOfFiniteType structureMap] :
    letI := baseFunctionFieldAlgebra structureMap
    topologicalKrullDim source =
      (Cardinal.toENat (Algebra.trdeg baseField source.functionField) : WithBot ℕ∞) := by
  let := baseFunctionFieldAlgebra structureMap
  obtain ⟨_, ⟨genericRegion, genericAffine, rfl⟩, genericInRegion, _⟩ :=
    source.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint source)) isOpen_univ
  have : Nonempty genericRegion := ⟨⟨genericPoint source, genericInRegion⟩⟩
  have lowerBound :
      (Cardinal.toENat (Algebra.trdeg baseField source.functionField) : WithBot ℕ∞) ≤
        topologicalKrullDim source := by
    rw [← affine_dimension_eq_functionField_trdeg structureMap genericAffine]
    exact topologicalKrullDim_subspace_le source genericRegion
  refine le_antisymm ?_ lowerBound
  rw [topologicalKrullDim_eq_iSup_openCover
    (source.openCoverOfIsOpenCover (fun region : source.affineOpens => region.1)
      (iSup_affineOpens_eq_top source))]
  refine iSup_le fun region => ?_
  change topologicalKrullDim region.1 ≤ _
  by_cases nonempty : (region.1 : Set source).Nonempty
  · have : Nonempty region.1 := nonempty.to_subtype
    exact (affine_dimension_eq_functionField_trdeg structureMap region.2).le
  · have : IsEmpty region.1 := Set.isEmpty_coe_sort.mpr
      (Set.not_nonempty_iff_eq_empty.mp nonempty)
    have : IsEmpty (IrreducibleCloseds region.1) :=
      ⟨fun closedSubset => isEmptyElim closedSubset.isIrreducible'.nonempty.some⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le

theorem exists_transcendental_of_dimension_one {baseField : Type u} [Field baseField]
    {source : Scheme.{u}} [IsIntegral source]
    (structureMap : source ⟶ Spec (CommRingCat.of baseField)) [LocallyOfFiniteType structureMap]
    (dimensionOne : topologicalKrullDim source = 1) :
    letI := baseFunctionFieldAlgebra structureMap
    ∃ rational : source.functionField, Transcendental baseField rational := by
  let := baseFunctionFieldAlgebra structureMap
  have dimensionFormula := topologicalKrullDim_eq_trdeg_functionField structureMap
  rw [dimensionOne] at dimensionFormula
  have trdegOne : Algebra.trdeg baseField source.functionField = 1 := by
    apply Cardinal.toENat_eq_one.mp
    exact_mod_cast dimensionFormula.symm
  have transcendentalField : Algebra.Transcendental baseField source.functionField := by
    rw [← trdeg_ne_zero_iff, trdegOne]
    exact one_ne_zero
  exact Algebra.transcendental_def.mp transcendentalField

end AlgebraicGeometry.IntegralFunctionFieldDimension
