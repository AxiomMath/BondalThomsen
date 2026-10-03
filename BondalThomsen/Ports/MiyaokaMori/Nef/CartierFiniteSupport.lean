module

public import BondalThomsen.Ports.MiyaokaMori.Nef.OrdFiniteOnNoetherianOpen
public import BondalThomsen.Ports.MiyaokaMori.Nef.CartierLocalData
public import BondalThomsen.Ports.MiyaokaMori.Nef.ZeroCycleDegree

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry TopologicalSpace Order
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry.Intersection

theorem isClosed_singleton_of_coheight_eq_one {scheme : Scheme.{u}}
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (point : scheme)
    (coheightOne : coheight point = 1) : IsClosed ({point} : Set scheme) := by
  have krullBound : Order.krullDim scheme ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := scheme))]
    exact dimensionBound
  have coheightBound (element : scheme) : coheight element ≤ 1 :=
    WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim element).trans krullBound)
  apply closure_eq_iff_isClosed.mp
  apply Set.Subset.antisymm
  · intro element contains
    have elementBelow : element ≤ point :=
      Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr contains)
    have pointBelow : point ≤ element := by
      by_contra different
      have coheightStrict : coheight point < coheight element :=
        Order.coheight_strictAnti (lt_of_le_not_ge elementBelow different) (by simp [coheightOne])
      rw [coheightOne] at coheightStrict
      exact (not_lt_of_ge (coheightBound element)) coheightStrict
    exact ((Scheme.le_iff_specializes.mp pointBelow).antisymm
      (Scheme.le_iff_specializes.mp elementBelow)).eq
  · exact subset_closure

theorem pointClosureDimension_eq_zero_of_coheight_eq_one {scheme : Scheme.{u}}
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (point : scheme)
    (coheightOne : coheight point = 1) : pointClosureDimension scheme point = 0 :=
  pointClosureDimension_eq_zero_of_isClosed point
    (isClosed_singleton_of_coheight_eq_one dimensionBound point coheightOne)

namespace CartierLocalData

variable {scheme : Scheme.{u}} [IsIntegral scheme]

section Local

variable [IsLocallyNoetherian scheme]

theorem coefficient_eq_ord_of_mem (datum : CartierLocalData scheme) (point : scheme)
    (chart : datum.index) (contains : point ∈ datum.opens chart) :
    datum.coefficient point = scheme.ord (datum.equation chart) point := by
  by_cases coheightOne : coheight point = 1
  · rw [datum.coefficient_eq_ord point coheightOne]
    exact datum.coefficient_eq_of_mem point coheightOne (datum.indexAt point) chart
      (datum.indexAt_mem point) contains
  · rw [datum.coefficient_eq_zero_of_coheight_ne_one point coheightOne,
      Scheme.ord_eq_zero_of_coheight_neq_one coheightOne]

theorem coefficient_pointClosureDimension_zero (datum : CartierLocalData scheme)
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (point : scheme)
    (nonzero : datum.coefficient point ≠ 0) : pointClosureDimension scheme point = 0 := by
  apply pointClosureDimension_eq_zero_of_coheight_eq_one dimensionBound point
  by_contra different
  exact nonzero (datum.coefficient_eq_zero_of_coheight_ne_one point different)

end Local

variable [IsNoetherian scheme]

theorem coefficient_finite_support (datum : CartierLocalData scheme) :
    (Function.support datum.coefficient).Finite := by
  obtain ⟨charts, cover⟩ := isCompact_univ.elim_finite_subcover
    (fun chart => (datum.opens chart : Set scheme)) (fun chart => (datum.opens chart).isOpen)
    datum.cover.ge
  have finiteSupport : (⋃ chart ∈ charts, Function.support (scheme.ord (datum.equation chart))).Finite :=
    charts.finite_toSet.biUnion fun chart _ =>
      AlgebraicGeometry.Divisors.finite_support_ord scheme (datum.equation chart)
        (datum.equation_ne_zero chart)
  apply finiteSupport.subset
  intro point nonzero
  obtain ⟨chart, chartContains, contains⟩ := Set.mem_iUnion₂.mp (cover (Set.mem_univ point))
  refine Set.mem_iUnion₂.mpr ⟨chart, chartContains, ?_⟩
  change scheme.ord (datum.equation chart) point ≠ 0
  change datum.coefficient point ≠ 0 at nonzero
  rwa [datum.coefficient_eq_ord_of_mem point chart contains] at nonzero

def toFiniteCartierDivisor (datum : CartierLocalData scheme) :
    FiniteCartierDivisor scheme where
  toCartierLocalData := datum
  finite_support := datum.coefficient_finite_support

@[simp] theorem toFiniteCartierDivisor_toCartierLocalData
    (datum : CartierLocalData scheme) : datum.toFiniteCartierDivisor.toCartierLocalData = datum := rfl

theorem zeroDimensionalSupport (datum : CartierLocalData scheme)
    (dimensionBound : topologicalKrullDim scheme ≤ 1) :
    datum.toFiniteCartierDivisor.ZeroDimensionalSupport :=
  ⟨fun point nonzero => datum.coefficient_pointClosureDimension_zero dimensionBound point nonzero⟩

def zeroCycle (datum : CartierLocalData scheme)
    (dimensionBound : topologicalKrullDim scheme ≤ 1) : DimensionCycle scheme 0 :=
  datum.toFiniteCartierDivisor.zeroCycle (datum.zeroDimensionalSupport dimensionBound)

@[simp] theorem zeroCycle_apply (datum : CartierLocalData scheme)
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (point : scheme) :
    (datum.zeroCycle dimensionBound).1 point = datum.coefficient point := rfl

end CartierLocalData

end AlgebraicGeometry.Intersection
