module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperCurveProjectiveLineModel
public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperCurveWeightedDegree
public import BondalThomsen.Ports.MiyaokaMori.Nef.PrincipalCartierDivisor

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace
open scoped Classical BigOperators AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.PrincipalCurveDegree

theorem functionField_finite_of_generic_residueField_finite
    {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    (morphism : source ⟶ target)
    (genericEquality : morphism (genericPoint source) = genericPoint target)
    (genericFinite : (morphism.residueFieldMap (genericPoint source)).hom.Finite) :
    letI := functionFieldAlgebra morphism genericEquality
    Module.Finite target.functionField source.functionField := by
  let := functionFieldAlgebra morphism genericEquality
  let sourceResidueEquivalence : source.functionField ≃+*
      source.residueField (genericPoint source) :=
    RingEquiv.ofBijective (source.residue (genericPoint source)).hom
      ⟨(source.residue (genericPoint source)).hom.injective,
        IsLocalRing.residue_surjective⟩
  have stalkFinite : (morphism.stalkMap (genericPoint source)).hom.Finite := by
    have residueCompositeFinite := genericFinite.comp
      (RingHom.Finite.of_surjective
        (target.residue (morphism (genericPoint source))).hom
        IsLocalRing.residue_surjective)
    have inverseCompositeFinite := sourceResidueEquivalence.symm.finite.comp residueCompositeFinite
    have compositeEquality :
        sourceResidueEquivalence.symm.toRingHom.comp
          ((morphism.residueFieldMap (genericPoint source)).hom.comp
            (target.residue (morphism (genericPoint source))).hom) =
          (morphism.stalkMap (genericPoint source)).hom := by
      rw [← CommRingCat.hom_comp, Scheme.residue_residueFieldMap]
      ext element
      exact sourceResidueEquivalence.symm_apply_apply _
    rwa [compositeEquality] at inverseCompositeFinite
  have congrFinite := RingHom.Finite.of_surjective
    (target.presheaf.stalkCongr (Inseparable.of_eq genericEquality.symm)).hom.hom
    (ConcreteCategory.bijective_of_isIso
      (target.presheaf.stalkCongr (Inseparable.of_eq genericEquality.symm)).hom).surjective
  exact stalkFinite.comp congrFinite

theorem principal_weighted_degree_eq_zero
    {baseField : Type u} [Field baseField] {source : Scheme.{u}} [IsIntegral source]
    (sourceStructure : source ⟶ Spec (CommRingCat.of baseField)) [IsProper sourceStructure]
    (dimensionOne : topologicalKrullDim source = 1)
    (rational : source.functionField) (rationalNonzero : rational ≠ 0) :
    letI := Intersection.properFieldScheme_isNoetherian sourceStructure
    ∑ᶠ point : source, source.ord rational point *
      (sourceStructure.residueDegree point : ℤ) = 0 := by
  have : IsNoetherian source := Intersection.properFieldScheme_isNoetherian sourceStructure
  have := ProperCurveProjectiveLine.projectiveLineStructure_isProper baseField
  have := Intersection.properFieldScheme_isNoetherian
    (ProjectiveLinePrincipalDegree.structureMap baseField)
  obtain ⟨model, _, _, projection, _, projectionGeneric, projectionRank,
      targetProjection, _, modelDimension, baseEquality, targetGeneric,
      projectionFinite, targetFinite⟩ :=
    ProperCurveProjectiveLine.exists_proper_birational_dominant_projectiveLine
      sourceStructure dimensionOne
  let modelStructure := projection ≫ sourceStructure
  let := functionFieldAlgebra projection projectionGeneric
  let liftedRational := algebraMap source.functionField model.functionField rational
  have liftedNonzero : liftedRational ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap source.functionField model.functionField).injective.ne rationalNonzero
  have projectionNorm : Algebra.norm source.functionField liftedRational = rational := by
    rw [Algebra.norm_algebraMap, projectionRank, pow_one]
  have projectionDegree := ProperCurveWeightedDegree.proper_norm_weighted_degree_eq
    projection modelStructure sourceStructure rfl projectionGeneric projectionFinite
    modelDimension dimensionOne liftedRational liftedNonzero
  rw [projectionNorm] at projectionDegree
  let := functionFieldAlgebra targetProjection targetGeneric
  have : Module.Finite (ProjectiveLinePrincipalDegree.projectiveLine baseField).functionField
      model.functionField :=
    functionField_finite_of_generic_residueField_finite targetProjection targetGeneric targetFinite
  have normNonzero : Algebra.norm
      (ProjectiveLinePrincipalDegree.projectiveLine baseField).functionField liftedRational ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr liftedNonzero
  have targetDegree := ProperCurveWeightedDegree.proper_norm_weighted_degree_eq
    targetProjection modelStructure (ProjectiveLinePrincipalDegree.structureMap baseField)
    baseEquality.symm targetGeneric targetFinite modelDimension
    (ProperCurveProjectiveLine.projectiveLine_dimension_one baseField) liftedRational liftedNonzero
  exact projectionDegree.symm.trans (targetDegree.trans
    (ProjectiveLinePrincipalDegree.principal_weighted_degree_eq_zero baseField _ normNonzero))

theorem principalDivisor_degree_eq_zero
    {baseField : Type u} [Field baseField] {source : Scheme.{u}} [IsIntegral source]
    (sourceStructure : source ⟶ Spec (CommRingCat.of baseField)) [IsProper sourceStructure]
    (dimensionOne : topologicalKrullDim source = 1) (rational : source.functionFieldˣ) :
    letI := Intersection.properFieldScheme_isNoetherian sourceStructure
    ∑ᶠ point : source, source.ord (rational : source.functionField) point *
      (sourceStructure.residueDegree point : ℤ) = 0 :=
  principal_weighted_degree_eq_zero sourceStructure dimensionOne rational rational.ne_zero

end AlgebraicGeometry.PrincipalCurveDegree

namespace AlgebraicGeometry.Intersection

theorem rawZeroCycleDegree_principal_eq_zero_of_dim_eq_one
    {baseField : Type u} [Field baseField] {source : Scheme.{u}} [IsIntegral source]
    (sourceStructure : source ⟶ Spec (CommRingCat.of baseField)) [IsProper sourceStructure]
    (dimensionOne : topologicalKrullDim source = 1) (rational : source.functionFieldˣ) :
    letI := properFieldScheme_isNoetherian sourceStructure
    rawZeroCycleDegree sourceStructure ((principalCartierData rational).zeroCycle dimensionOne.le) = 0 := by
  classical
  have := properFieldScheme_isNoetherian sourceStructure
  rw [rawZeroCycleDegree_principal_eq_sum]
  have weightedZero := PrincipalCurveDegree.principalDivisor_degree_eq_zero
    sourceStructure dimensionOne rational
  rw [finsum_eq_sum_of_support_subset _ (show
    Function.support (fun point : source => source.ord (rational : source.functionField) point *
      (sourceStructure.residueDegree point : ℤ)) ⊆
      ((Divisors.finite_support_ord source rational rational.ne_zero).toFinset : Set source) from by
        intro point nonzero
        exact (Divisors.finite_support_ord source rational rational.ne_zero).mem_toFinset.mpr
          (mul_ne_zero_iff.mp nonzero).1)] at weightedZero
  simpa only [Scheme.Hom.residueFieldDegree_eq_residueDegree] using weightedZero

theorem rawZeroCycleDegree_principal_eq_zero
    {baseField : Type u} [Field baseField] {source : Scheme.{u}} [IsIntegral source]
    (sourceStructure : source ⟶ Spec (CommRingCat.of baseField)) [IsProper sourceStructure]
    (dimensionBound : topologicalKrullDim source ≤ 1) (rational : source.functionFieldˣ) :
    letI := properFieldScheme_isNoetherian sourceStructure
    rawZeroCycleDegree sourceStructure ((principalCartierData rational).zeroCycle dimensionBound) = 0 := by
  have := properFieldScheme_isNoetherian sourceStructure
  by_cases strictBound : topologicalKrullDim source < 1
  · rw [principalCartierData_zeroCycle_eq_zero_of_dim_lt_one strictBound,
      rawZeroCycleDegree_zero]
  · have dimensionOne : topologicalKrullDim source = 1 :=
      le_antisymm dimensionBound (le_of_not_gt strictBound)
    exact rawZeroCycleDegree_principal_eq_zero_of_dim_eq_one sourceStructure dimensionOne rational

end AlgebraicGeometry.Intersection
