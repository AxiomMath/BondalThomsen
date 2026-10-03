module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperRationalGraphModel
public import BondalThomsen.Ports.MiyaokaMori.Nef.GenericFiniteCurveMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.IntegralFunctionFieldDimension
open AlgebraicGeometry.ProjectiveLinePrincipalDegree
open scoped Classical

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProperCurveProjectiveLine

theorem fromSpecStalk_comp_toSpec {source : Scheme.{u}} {ring : CommRingCat.{u}}
    (morphism : source ⟶ Spec ring) (point : source) :
    source.fromSpecStalk point ≫ morphism =
      Spec.map ((Scheme.ΓSpecIso ring).inv ≫ morphism.appTop ≫
        source.presheaf.germ ⊤ point trivial) := by
  calc source.fromSpecStalk point ≫ morphism
      = source.fromSpecStalk point ≫ (morphism ≫ (Spec ring).toSpecΓ) ≫
          Spec.map (Scheme.ΓSpecIso ring).inv := by
        rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = (source.fromSpecStalk point ≫ source.toSpecΓ) ≫ Spec.map morphism.appTop ≫
          Spec.map (Scheme.ΓSpecIso ring).inv := by
        rw [Scheme.toSpecΓ_naturality]
        simp only [Category.assoc]
    _ = _ := by
        rw [Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp, Category.assoc]

theorem genericFunctionField_base_commutes {baseField : Type u} [Field baseField]
    {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    (sourceStructure : source ⟶ Spec (CommRingCat.of baseField))
    (targetStructure : target ⟶ Spec (CommRingCat.of baseField))
    (morphism : source ⟶ target) (baseEquality : morphism ≫ targetStructure = sourceStructure)
    (genericEquality : morphism (genericPoint source) = genericPoint target) (scalar : baseField) :
    letI := baseFunctionFieldAlgebra sourceStructure
    letI := baseFunctionFieldAlgebra targetStructure
    (functionFieldAlgebra morphism genericEquality).algebraMap
      (algebraMap baseField target.functionField scalar) =
        algebraMap baseField source.functionField scalar := by
  let := baseFunctionFieldAlgebra sourceStructure
  let := baseFunctionFieldAlgebra targetStructure
  have germCongruence : target.presheaf.germ ⊤ (genericPoint target) trivial ≫
      (target.presheaf.stalkCongr (Inseparable.of_eq genericEquality.symm)).hom =
        target.presheaf.germ ⊤ (morphism (genericPoint source)) trivial := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have germMap := Scheme.Hom.germ_stalkMap morphism ⊤ (genericPoint source) trivial
  have mapsEquality :
      ((Scheme.ΓSpecIso (CommRingCat.of baseField)).inv ≫ targetStructure.appTop ≫
          target.presheaf.germ ⊤ (genericPoint target) trivial) ≫
        ((target.presheaf.stalkCongr (Inseparable.of_eq genericEquality.symm)).hom ≫
          morphism.stalkMap (genericPoint source)) =
      (Scheme.ΓSpecIso (CommRingCat.of baseField)).inv ≫ sourceStructure.appTop ≫
        source.presheaf.germ ⊤ (genericPoint source) trivial := by
    rw [Category.assoc, Category.assoc, reassoc_of% germCongruence, germMap]
    change (Scheme.ΓSpecIso (CommRingCat.of baseField)).inv ≫
      (targetStructure.appTop ≫ morphism.appTop) ≫
        source.presheaf.germ ⊤ (genericPoint source) trivial = _
    rw [← Scheme.Hom.comp_appTop, baseEquality]
  exact congrArg (fun ringMap => ringMap.hom scalar) mapsEquality

theorem dimension_eq_of_generic_bijective {baseField : Type u} [Field baseField]
    {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    (sourceStructure : source ⟶ Spec (CommRingCat.of baseField))
    (targetStructure : target ⟶ Spec (CommRingCat.of baseField))
    [LocallyOfFiniteType sourceStructure] [LocallyOfFiniteType targetStructure]
    (morphism : source ⟶ target) (baseEquality : morphism ≫ targetStructure = sourceStructure)
    (genericEquality : morphism (genericPoint source) = genericPoint target)
    (genericBijective : Function.Bijective (functionFieldAlgebra morphism genericEquality).algebraMap) :
    topologicalKrullDim source = topologicalKrullDim target := by
  let := baseFunctionFieldAlgebra sourceStructure
  let := baseFunctionFieldAlgebra targetStructure
  let fieldEquivalence : target.functionField ≃ₐ[baseField] source.functionField :=
    AlgEquiv.ofBijective
      { toRingHom := (functionFieldAlgebra morphism genericEquality).algebraMap
        commutes' := genericFunctionField_base_commutes sourceStructure targetStructure morphism
          baseEquality genericEquality } genericBijective
  rw [topologicalKrullDim_eq_trdeg_functionField sourceStructure,
    topologicalKrullDim_eq_trdeg_functionField targetStructure, fieldEquivalence.trdeg_eq]

theorem projectiveLineStructure_isProper (baseField : Type u) [Field baseField] :
    IsProper (ProjectiveLinePrincipalDegree.structureMap baseField) := by
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0)
      (MvPolynomial (Fin 2) baseField) := by
    refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact adjoin_variables baseField
  have constantsBijective : Function.Bijective
      (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0)) := by
    constructor
    · intro first second equality
      have constantsEquality : MvPolynomial.C first = (MvPolynomial.C second : MvPolynomial (Fin 2) baseField) :=
        congrArg Subtype.val equality
      simpa using congrArg (fun polynomial : MvPolynomial (Fin 2) baseField => polynomial.coeff 0)
        constantsEquality
    · intro polynomial
      refine ⟨polynomial.val.coeff 0, Subtype.ext ?_⟩
      exact (MvPolynomial.homogeneousComponent_zero polynomial.val).symm.trans
        (MvPolynomial.homogeneousComponent_eq_self polynomial.property)
  let constantsEquivalence := RingEquiv.ofBijective
    (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0)) constantsBijective
  have : IsIso (CommRingCat.ofHom
      (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0))) :=
    constantsEquivalence.toCommRingCatIso.isIso_hom
  unfold ProjectiveLinePrincipalDegree.structureMap
  infer_instance

theorem projectiveLine_dimension_one (baseField : Type u) [Field baseField] :
    topologicalKrullDim (projectiveLine baseField) = 1 := by
  have := projectiveLineStructure_isProper baseField
  have : LocallyOfFiniteType (AffineLinePrincipalOrder.structureMap baseField) := by
    unfold AffineLinePrincipalOrder.structureMap
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have chartGeneric : chartι baseField 0 (genericPoint _) = genericPoint (projectiveLine baseField) :=
    genericPoint_eq_of_isOpenImmersion _
  have genericBijective : Function.Bijective
      (functionFieldAlgebra (chartι baseField 0) chartGeneric).algebraMap :=
    ConcreteCategory.bijective_of_isIso
      (((projectiveLine baseField).presheaf.stalkCongr
        (Inseparable.of_eq chartGeneric.symm)).hom ≫
          (chartι baseField 0).stalkMap (genericPoint _))
  have dimensionEquality := dimension_eq_of_generic_bijective
    (AffineLinePrincipalOrder.structureMap baseField) (ProjectiveLinePrincipalDegree.structureMap baseField)
    (chartι baseField 0) (chartι_comp_structureMap baseField 0) chartGeneric genericBijective
  rw [← dimensionEquality]
  change topologicalKrullDim (PrimeSpectrum (Polynomial baseField)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  simp

theorem exists_proper_birational_dominant_projectiveLine
    {baseField : Type u} [Field baseField] {source : Scheme.{u}} [IsIntegral source]
    [IsNoetherian source] (sourceStructure : source ⟶ Spec (CommRingCat.of baseField))
    [IsProper sourceStructure] (dimensionOne : topologicalKrullDim source = 1) :
    ∃ (model : Scheme.{u}) (_ : IsIntegral model) (_ : IsNoetherian model)
      (projection : model ⟶ source) (_ : IsProper projection)
      (projectionGeneric : projection (genericPoint model) = genericPoint source)
      (_ : letI := functionFieldAlgebra projection projectionGeneric
        Module.finrank source.functionField model.functionField = 1)
      (targetProjection : model ⟶ projectiveLine baseField) (_ : IsProper targetProjection),
      topologicalKrullDim model = 1 ∧
      projection ≫ sourceStructure = targetProjection ≫ ProjectiveLinePrincipalDegree.structureMap baseField ∧
      targetProjection (genericPoint model) = genericPoint (projectiveLine baseField) ∧
      (projection.residueFieldMap (genericPoint model)).hom.Finite ∧
      (targetProjection.residueFieldMap (genericPoint model)).hom.Finite := by
  classical
  have := projectiveLineStructure_isProper baseField
  let := baseFunctionFieldAlgebra sourceStructure
  obtain ⟨rational, rationalTranscendental⟩ := exists_transcendental_of_dimension_one sourceStructure dimensionOne
  let evaluation : Polynomial baseField →ₐ[baseField] source.functionField := Polynomial.aeval rational
  have evaluationInjective : Function.Injective evaluation :=
    transcendental_iff_injective.mp rationalTranscendental
  let genericMorphism : Spec source.functionField ⟶ projectiveLine baseField :=
    Spec.map (CommRingCat.ofHom evaluation.toRingHom) ≫ chartι baseField 0
  have baseCompatibility : genericMorphism ≫ ProjectiveLinePrincipalDegree.structureMap baseField =
      source.fromSpecStalk (genericPoint source) ≫ sourceStructure := by
    rw [fromSpecStalk_comp_toSpec]
    change Spec.map (CommRingCat.ofHom evaluation.toRingHom) ≫ chartι baseField 0 ≫
      ProjectiveLinePrincipalDegree.structureMap baseField = _
    rw [chartι_comp_structureMap]
    unfold AffineLinePrincipalOrder.structureMap
    rw [← Spec.map_comp]
    congr 1
    ext scalar
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      evaluation]
    exact (Polynomial.aeval rational).commutes scalar
  have genericImage : genericMorphism (IsLocalRing.closedPoint source.functionField) =
      genericPoint (projectiveLine baseField) := by
    change chartι baseField 0
      (Spec.map (CommRingCat.ofHom evaluation.toRingHom) (IsLocalRing.closedPoint source.functionField)) = _
    rw [← genericPoint_eq_of_isOpenImmersion (chartι baseField 0)]
    congr 1
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change Ideal.comap evaluation.toRingHom (IsLocalRing.maximalIdeal source.functionField) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective evaluation.toRingHom evaluationInjective
  obtain ⟨model, _, _, projection, _, projectionGeneric, genericRank, targetProjection, _,
      projectionsBase, targetGeneric⟩ :=
    ProperRationalGraph.exists_proper_birational_graph_model sourceStructure
      (ProjectiveLinePrincipalDegree.structureMap baseField) genericMorphism baseCompatibility genericImage
  have : IsProper (projection ≫ sourceStructure) := inferInstance
  have genericBijective : Function.Bijective (functionFieldAlgebra projection projectionGeneric).algebraMap := by
    let := functionFieldAlgebra projection projectionGeneric
    exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp genericRank
  have modelDimension : topologicalKrullDim model = 1 :=
    (dimension_eq_of_generic_bijective (projection ≫ sourceStructure) sourceStructure projection rfl
      projectionGeneric genericBijective).trans dimensionOne
  have projectionFinite := residueFieldMap_genericPoint_finite_of_equal_dimension
    (projection ≫ sourceStructure) sourceStructure projection rfl projectionGeneric
      (modelDimension.trans dimensionOne.symm)
  have targetFinite := residueFieldMap_genericPoint_finite_of_equal_dimension
    (projection ≫ sourceStructure) (ProjectiveLinePrincipalDegree.structureMap baseField)
      targetProjection projectionsBase.symm targetGeneric
        (modelDimension.trans (projectiveLine_dimension_one baseField).symm)
  exact ⟨model, inferInstance, inferInstance, projection, inferInstance, projectionGeneric, genericRank,
    targetProjection, inferInstance, modelDimension, projectionsBase, targetGeneric, projectionFinite,
    targetFinite⟩

end AlgebraicGeometry.ProperCurveProjectiveLine
