module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperNormOrder
public import BondalThomsen.Ports.MiyaokaMori.Nef.PrincipalCartierDivisor
public import BondalThomsen.Ports.MiyaokaMori.Nef.ResidueDegreeComposition
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Classical BigOperators

universe u

noncomputable section

namespace AlgebraicGeometry.ProperCurveWeightedDegree

theorem closedPoint_coheight_eq_one_of_dimension_one
    (source : Scheme.{u}) [IsIntegral source] (dimensionOne : topologicalKrullDim source = 1)
    (point : source) (pointClosed : IsClosed ({point} : Set source)) : Order.coheight point = 1 := by
  have orderDimension : Order.krullDim source = 1 := by
    calc
      Order.krullDim source = topologicalKrullDim source :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := source))).symm
      _ = 1 := dimensionOne
  have coheightBound : Order.coheight point ≤ 1 := by
    exact_mod_cast (Order.coheight_le_krullDim point).trans_eq orderDimension
  have coheightNonzero : Order.coheight point ≠ 0 := by
    intro coheightZero
    have pointMaximal : IsMax point := Order.coheight_eq_zero.mp coheightZero
    have heightBound : Order.height (⊤ : source) ≤ 0 := by
      rw [← Scheme.height_of_isClosed pointClosed]
      exact Order.height_mono (pointMaximal le_top)
    have coercedHeightBound : (Order.height (⊤ : source) : WithBot ℕ∞) ≤ 0 := by
      exact_mod_cast heightBound
    rw [Order.height_top_eq_krullDim, orderDimension] at coercedHeightBound
    exact (not_le_of_gt (zero_lt_one : (0 : WithBot ℕ∞) < 1)) coercedHeightBound
  exact le_antisymm coheightBound (Order.one_le_iff_ne_zero.mpr coheightNonzero)

theorem finsum_eq_fiberwise_of_finite_support {sourcePoints targetPoints : Type*}
    {coefficientGroup : Type*} [AddCommMonoid coefficientGroup]
    (pointMap : sourcePoints → targetPoints) (coefficients : sourcePoints → coefficientGroup)
    (finiteSupport : (Function.support coefficients).Finite) :
    (∑ᶠ point : sourcePoints, coefficients point) =
      ∑ᶠ image : targetPoints, ∑ᶠ point ∈ pointMap ⁻¹' {image}, coefficients point := by
  classical
  let support := finiteSupport.toFinset
  have supportEquality : (support : Set sourcePoints) = Function.support coefficients :=
    finiteSupport.coe_toFinset
  have fiberSum (image : targetPoints) :
      (∑ᶠ point ∈ pointMap ⁻¹' {image}, coefficients point) =
        ∑ point ∈ support.filter (fun point => pointMap point = image), coefficients point := by
    apply finsum_mem_eq_sum_of_subset
    · intro point member
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at member
      exact Finset.mem_filter.mpr
        ⟨finiteSupport.mem_toFinset.mpr member.2, member.1⟩
    · intro point member
      exact (Finset.mem_filter.mp member).2
  have outerSupport : (Function.support fun image : targetPoints =>
      ∑ᶠ point ∈ pointMap ⁻¹' {image}, coefficients point) ⊆ (support.image pointMap : Set targetPoints) := by
    intro image nonzero
    by_contra absent
    apply nonzero
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro point pointMember
    by_contra coefficientNonzero
    apply absent
    exact Finset.mem_image.mpr ⟨point,
      finiteSupport.mem_toFinset.mpr coefficientNonzero,
      pointMember⟩
  rw [finsum_eq_sum_of_support_subset _
    (show Function.support coefficients ⊆ (support : Set sourcePoints) from
      fun _ nonzero => finiteSupport.mem_toFinset.mpr nonzero),
    finsum_eq_sum_of_support_subset _ outerSupport]
  simp_rw [fiberSum]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun point member => Finset.mem_image.mpr ⟨point, member, rfl⟩) coefficients).symm

theorem proper_norm_order_eq_fiber_sum_all_points
    {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    [IsNoetherian source] [IsNoetherian target]
    (morphism : source ⟶ target) [IsProper morphism]
    (genericEquality : morphism (genericPoint source) = genericPoint target)
    (genericFinite : (morphism.residueFieldMap (genericPoint source)).hom.Finite)
    (sourceDimension : topologicalKrullDim source = 1)
    (targetDimension : topologicalKrullDim target = 1)
    (rational : source.functionField) (rationalNonzero : rational ≠ 0) (targetPoint : target) :
    letI := functionFieldAlgebra morphism genericEquality
    target.ord (Algebra.norm target.functionField rational) targetPoint =
      ∑ᶠ point ∈ morphism.base ⁻¹' {targetPoint},
        source.ord rational point * (morphism.residueDegree point : ℤ) := by
  let := functionFieldAlgebra morphism genericEquality
  by_cases coheightOne : Order.coheight targetPoint = 1
  · exact proper_norm_order_eq_fiber_sum morphism genericEquality genericFinite targetPoint
      coheightOne rational rationalNonzero
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one coheightOne]
    symm
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro point pointMember
    have orderZero : source.ord rational point = 0 := by
      by_contra orderNonzero
      have sourceCoheight : Order.coheight point = 1 := by
        by_contra notOne
        exact orderNonzero (Scheme.ord_eq_zero_of_coheight_neq_one notOne rational)
      have sourceClosed : IsClosed ({point} : Set source) :=
        Intersection.isClosed_singleton_of_coheight_eq_one sourceDimension.le point sourceCoheight
      have targetClosed : IsClosed ({targetPoint} : Set target) := by
        have closedImage := morphism.isProperMap.isClosedMap _ sourceClosed
        have imageEquality : morphism point = targetPoint := pointMember
        simpa only [Set.image_singleton, imageEquality] using closedImage
      exact coheightOne
        (closedPoint_coheight_eq_one_of_dimension_one target targetDimension targetPoint targetClosed)
    rw [orderZero, zero_mul]

theorem proper_norm_weighted_degree_eq
    {source target base : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    [IsNoetherian source] [IsNoetherian target]
    (morphism : source ⟶ target) [IsProper morphism]
    (sourceStructure : source ⟶ base) (targetStructure : target ⟶ base)
    (baseEquality : morphism ≫ targetStructure = sourceStructure)
    (genericEquality : morphism (genericPoint source) = genericPoint target)
    (genericFinite : (morphism.residueFieldMap (genericPoint source)).hom.Finite)
    (sourceDimension : topologicalKrullDim source = 1)
    (targetDimension : topologicalKrullDim target = 1)
    (rational : source.functionField) (rationalNonzero : rational ≠ 0) :
    letI := functionFieldAlgebra morphism genericEquality
    (∑ᶠ point : source, source.ord rational point * (sourceStructure.residueDegree point : ℤ)) =
      ∑ᶠ point : target, target.ord (Algebra.norm target.functionField rational) point *
        (targetStructure.residueDegree point : ℤ) := by
  let := functionFieldAlgebra morphism genericEquality
  have weightedFinite : (Function.support fun point : source =>
      source.ord rational point * (sourceStructure.residueDegree point : ℤ)).Finite :=
    (Divisors.finite_support_ord source rational rationalNonzero).subset fun point nonzero =>
      (mul_ne_zero_iff.mp nonzero).1
  rw [finsum_eq_fiberwise_of_finite_support morphism
    (fun point => source.ord rational point * (sourceStructure.residueDegree point : ℤ)) weightedFinite]
  refine finsum_congr fun targetPoint => ?_
  rw [proper_norm_order_eq_fiber_sum_all_points morphism genericEquality genericFinite sourceDimension
    targetDimension rational rationalNonzero targetPoint, finsum_mem_mul]
  refine finsum_mem_congr rfl fun point pointMember => ?_
  have imageEquality : morphism point = targetPoint := pointMember
  rw [← baseEquality, Intersection.residueDegree_comp]
  rw [imageEquality, Nat.cast_mul]
  ring

end AlgebraicGeometry.ProperCurveWeightedDegree
