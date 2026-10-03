module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ResidueFieldDegree
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BigOperators

universe u

noncomputable section

def AlgebraicGeometry.AlgebraicCycle.degree {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} [scheme.Over (Spec (CommRingCat.of baseField))]
    (cycle : AlgebraicCycle scheme ℤ) : ℤ :=
  ∑ᶠ point : scheme, cycle point *
    ((scheme ↘ Spec (CommRingCat.of baseField)).residueDegree point : ℤ)

theorem AlgebraicGeometry.AlgebraicCycle.degree_zero {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} [scheme.Over (Spec (CommRingCat.of baseField))] :
    AlgebraicCycle.degree (baseField := baseField) (0 : AlgebraicCycle scheme ℤ) = 0 := by
  unfold AlgebraicCycle.degree
  simp

namespace AlgebraicGeometry.Intersection

theorem cycle_finiteSupport {scheme : Scheme.{u}} [CompactSpace scheme]
    (cycle : AlgebraicCycle scheme ℤ) : (Function.support cycle).Finite := by
  simpa using cycle.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ

theorem properCycle_finiteSupport {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (cycle : AlgebraicCycle scheme ℤ) : (Function.support cycle).Finite := by
  let : CompactSpace scheme := QuasiCompact.compactSpace_of_compactSpace structureMap
  exact cycle_finiteSupport cycle

theorem properFieldScheme_isNoetherian {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} (structureMap : scheme ⟶ Spec (CommRingCat.of baseField))
    [IsProper structureMap] : IsNoetherian scheme := by
  let : IsLocallyNoetherian scheme := LocallyOfFiniteType.isLocallyNoetherian structureMap
  let : CompactSpace scheme := QuasiCompact.compactSpace_of_compactSpace structureMap
  exact ⟨⟩

end AlgebraicGeometry.Intersection

open AlgebraicGeometry.Intersection in
theorem AlgebraicGeometry.AlgebraicCycle.degree_add {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} [scheme.Over (Spec (CommRingCat.of baseField))]
    [IsProper (scheme ↘ Spec (CommRingCat.of baseField))] (first second : AlgebraicCycle scheme ℤ) :
    AlgebraicCycle.degree (baseField := baseField) (first + second) =
      AlgebraicCycle.degree (baseField := baseField) first +
        AlgebraicCycle.degree (baseField := baseField) second := by
  have firstFinite : (Function.support first).Finite :=
    properCycle_finiteSupport (scheme ↘ Spec (CommRingCat.of baseField)) first
  have secondFinite : (Function.support second).Finite :=
    properCycle_finiteSupport (scheme ↘ Spec (CommRingCat.of baseField)) second
  unfold AlgebraicCycle.degree
  rw [show (fun point : scheme => (first + second) point *
      ((scheme ↘ Spec (CommRingCat.of baseField)).residueDegree point : ℤ)) =
      (fun point : scheme => first point *
        ((scheme ↘ Spec (CommRingCat.of baseField)).residueDegree point : ℤ) +
        second point * ((scheme ↘ Spec (CommRingCat.of baseField)).residueDegree point : ℤ)) by
      funext point
      simp [add_mul]]
  exact finsum_add_distrib (firstFinite.subset (Function.support_mul_subset_left _ _))
    (secondFinite.subset (Function.support_mul_subset_left _ _))

namespace AlgebraicGeometry.Intersection

abbrev rawZeroCycleDegree {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (cycle : DimensionCycle scheme 0) : ℤ :=
  @AlgebraicCycle.degree baseField _ scheme ⟨structureMap⟩ cycle.1

theorem rawZeroCycleDegree_eq_sum_on {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (cycle : DimensionCycle scheme 0) (points : Finset scheme)
    (support : ∀ point, point ∉ points → cycle.1 point = 0) :
    rawZeroCycleDegree structureMap cycle =
      ∑ point ∈ points, cycle.1 point * (residueFieldDegree structureMap point : ℤ) := by
  change (∑ᶠ point : scheme, cycle.1 point * (structureMap.residueDegree point : ℤ)) = _
  rw [finsum_eq_sum_of_support_subset _ (s := points)]
  · exact Finset.sum_congr rfl fun point _ => by
      rw [Scheme.Hom.residueFieldDegree_eq_residueDegree]
  · intro point nonzero
    by_contra absent
    exact nonzero (by simp [support point absent])

theorem rawZeroCycleDegree_eq_sum {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (cycle : DimensionCycle scheme 0) :
    rawZeroCycleDegree structureMap cycle =
      ∑ point ∈ (properCycle_finiteSupport structureMap cycle.1).toFinset,
        cycle.1 point * (residueFieldDegree structureMap point : ℤ) :=
  rawZeroCycleDegree_eq_sum_on structureMap cycle _ fun point absent => by
    by_contra nonzero
    exact absent ((properCycle_finiteSupport structureMap cycle.1).mem_toFinset.mpr nonzero)

end AlgebraicGeometry.Intersection
