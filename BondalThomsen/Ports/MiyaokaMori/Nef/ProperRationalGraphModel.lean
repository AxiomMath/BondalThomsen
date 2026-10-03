module

public import BondalThomsen.Ports.MiyaokaMori.Nef.IntegralSchemeImage
public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperFiniteLocalModel
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry.ProperRationalGraph

theorem genericPoint_eq_of_isDominant {source target : Scheme.{u}}
    [IrreducibleSpace source] [IrreducibleSpace target]
    (morphism : source ⟶ target) [IsDominant morphism] :
    morphism (genericPoint source) = genericPoint target := by
  have genericImage := (genericPoint_spec source).image morphism.continuous
  rw [Set.image_univ, morphism.denseRange.closure_range] at genericImage
  exact genericImage.eq (genericPoint_spec _)

theorem injective_of_maximalIdeal_eq_bot {sourceRing targetRing : Type*}
    [CommRing sourceRing] [IsLocalRing sourceRing] [CommRing targetRing] [Nontrivial targetRing]
    (ringMap : sourceRing →+* targetRing)
    (maximalIdealZero : IsLocalRing.maximalIdeal sourceRing = ⊥) :
    Function.Injective ringMap := by
  refine (RingHom.injective_iff_ker_eq_bot ringMap).mpr
    (le_bot_iff.mp fun element inKernel => ?_)
  rw [← maximalIdealZero, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro elementUnit
  have imageUnit : IsUnit (ringMap element) := elementUnit.map ringMap
  rw [RingHom.mem_ker.mp inKernel] at imageUnit
  exact not_isUnit_zero imageUnit

theorem stalkMap_bijective_of_comp_isIso {domain model source : Scheme.{u}}
    (inclusion : domain ⟶ model) (projection : model ⟶ source)
    (domainPoint : domain) (modelPoint : model) (sourcePoint : source)
    (inclusionEquality : inclusion domainPoint = modelPoint)
    (projectionEquality : projection modelPoint = sourcePoint)
    (sourceMaximalZero : IsLocalRing.maximalIdeal (source.presheaf.stalk sourcePoint) = ⊥)
    (modelMaximalZero : IsLocalRing.maximalIdeal (model.presheaf.stalk modelPoint) = ⊥)
    [compositeIso : IsIso ((inclusion ≫ projection).stalkMap domainPoint)] :
    Function.Bijective
      ((source.presheaf.stalkCongr (Inseparable.of_eq projectionEquality.symm)).hom ≫
        projection.stalkMap modelPoint).hom := by
  subst inclusionEquality projectionEquality
  have stalkCompositeIso : IsIso
      (projection.stalkMap (inclusion domainPoint) ≫ inclusion.stalkMap domainPoint) := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact compositeIso
  have compositeBijective : Function.Bijective
      (projection.stalkMap (inclusion domainPoint) ≫ inclusion.stalkMap domainPoint).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at compositeBijective
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  refine ⟨injective_of_maximalIdeal_eq_bot _ sourceMaximalZero, fun element => ?_⟩
  obtain ⟨preimage, preimageEquality⟩ :=
    compositeBijective.2 ((inclusion.stalkMap domainPoint).hom element)
  exact ⟨preimage, injective_of_maximalIdeal_eq_bot _ modelMaximalZero preimageEquality⟩

theorem exists_proper_birational_graph_model
    {source target base : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    [IsNoetherian source] (sourceStructure : source ⟶ base)
    (targetStructure : target ⟶ base) [IsProper sourceStructure] [IsProper targetStructure]
    (genericMorphism : Spec source.functionField ⟶ target)
    (baseCompatibility : genericMorphism ≫ targetStructure =
      source.fromSpecStalk (genericPoint source) ≫ sourceStructure)
    (genericImage : genericMorphism (IsLocalRing.closedPoint source.functionField) =
      genericPoint target) :
    ∃ (model : Scheme.{u}) (_ : IsIntegral model) (_ : IsNoetherian model)
      (projection : model ⟶ source) (_ : IsProper projection)
      (projectionGeneric : projection (genericPoint model) = genericPoint source)
      (_ : letI := functionFieldAlgebra projection projectionGeneric
        Module.finrank source.functionField model.functionField = 1)
      (targetProjection : model ⟶ target) (_ : IsProper targetProjection),
      projection ≫ sourceStructure = targetProjection ≫ targetStructure ∧
        targetProjection (genericPoint model) = genericPoint target := by
  classical
  let partialMap : source.PartialMap target :=
    Scheme.PartialMap.ofFromSpecStalk sourceStructure targetStructure genericMorphism
      baseCompatibility
  have genericInDomain : genericPoint source ∈ partialMap.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ genericMorphism baseCompatibility
  have partialGeneric : partialMap.fromSpecStalkOfMem genericInDomain = genericMorphism :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ genericMorphism baseCompatibility
  have partialBase : partialMap.hom ≫ targetStructure =
      partialMap.domain.ι ≫ sourceStructure :=
    Scheme.PartialMap.ofFromSpecStalk_comp _ _ genericMorphism baseCompatibility
  let graph : (partialMap.domain : Scheme.{u}) ⟶ pullback sourceStructure targetStructure :=
    pullback.lift partialMap.domain.ι partialMap.hom partialBase.symm
  have : TopologicalSpace.NoetherianSpace partialMap.domain :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (partialMap.domain : Set source))
  have : QuasiCompact graph := inferInstance
  have : Nonempty partialMap.domain := ⟨⟨_, genericInDomain⟩⟩
  have : IsIntegral partialMap.domain := isIntegral_of_isOpenImmersion partialMap.domain.ι
  have : IsIntegral graph.image := graph.isIntegral_image
  let inclusion : (partialMap.domain : Scheme.{u}) ⟶ graph.image := graph.toImage
  let projection : graph.image ⟶ source := graph.imageι ≫ pullback.fst _ _
  let targetProjection : graph.image ⟶ target := graph.imageι ≫ pullback.snd _ _
  have inclusionProjection : inclusion ≫ projection = partialMap.domain.ι := by
    simp only [projection, inclusion, ← Category.assoc, graph.toImage_imageι, graph,
      pullback.lift_fst]
  have inclusionTarget : inclusion ≫ targetProjection = partialMap.hom := by
    simp only [targetProjection, inclusion, ← Category.assoc, graph.toImage_imageι, graph,
      pullback.lift_snd]
  have projectionsBase : projection ≫ sourceStructure = targetProjection ≫ targetStructure := by
    simp only [projection, targetProjection, Category.assoc, pullback.condition]
  have : IsProper projection := inferInstance
  have : IsProper targetProjection := inferInstance
  have : IsLocallyNoetherian graph.image :=
    LocallyOfFiniteType.isLocallyNoetherian projection
  have : CompactSpace graph.image := QuasiCompact.compactSpace_of_compactSpace projection
  have : IsNoetherian graph.image := {}
  have inclusionGeneric : inclusion (genericPoint partialMap.domain) = genericPoint graph.image :=
    genericPoint_eq_of_isDominant inclusion
  have openGeneric : partialMap.domain.ι (genericPoint partialMap.domain) = genericPoint source :=
    genericPoint_eq_of_isOpenImmersion _
  have projectionGeneric : projection (genericPoint graph.image) = genericPoint source := by
    rw [← inclusionGeneric, ← Scheme.Hom.comp_apply, inclusionProjection, openGeneric]
  have domainGeneric : genericPoint partialMap.domain = ⟨genericPoint source, genericInDomain⟩ :=
    partialMap.domain.ι.isOpenEmbedding.injective openGeneric
  have targetGeneric : targetProjection (genericPoint graph.image) = genericPoint target := by
    rw [← inclusionGeneric, ← Scheme.Hom.comp_apply, inclusionTarget, domainGeneric]
    have stalkPointImage : partialMap.domain.ι
        (partialMap.domain.fromSpecStalkOfMem _ genericInDomain
          (IsLocalRing.closedPoint source.functionField)) = genericPoint source :=
      (congrArg (fun morphism : Spec source.functionField ⟶ source =>
        morphism (IsLocalRing.closedPoint source.functionField))
        (Scheme.Opens.fromSpecStalkOfMem_ι partialMap.domain _ genericInDomain)).trans
          Scheme.fromSpecStalk_closedPoint
    have stalkDomainImage : partialMap.domain.fromSpecStalkOfMem _ genericInDomain
        (IsLocalRing.closedPoint source.functionField) = ⟨_, genericInDomain⟩ :=
      partialMap.domain.ι.isOpenEmbedding.injective stalkPointImage
    have partialPoint : partialMap.fromSpecStalkOfMem genericInDomain
        (IsLocalRing.closedPoint source.functionField) = partialMap.hom ⟨_, genericInDomain⟩ :=
      congrArg (fun point => partialMap.hom point) stalkDomainImage
    rw [← partialPoint, partialGeneric]
    exact genericImage
  have sourceMaximalZero : IsLocalRing.maximalIdeal source.functionField = ⊥ :=
    IsLocalRing.maximalIdeal_eq_bot (R := source.functionField)
  have modelMaximalZero : IsLocalRing.maximalIdeal graph.image.functionField = ⊥ :=
    IsLocalRing.maximalIdeal_eq_bot (R := graph.image.functionField)
  have genericBijective : Function.Bijective
      ((source.presheaf.stalkCongr (Inseparable.of_eq projectionGeneric.symm)).hom ≫
        projection.stalkMap (genericPoint graph.image)).hom := by
    have : IsIso ((inclusion ≫ projection).stalkMap (genericPoint partialMap.domain)) := by
      rw [inclusionProjection]
      infer_instance
    exact stalkMap_bijective_of_comp_isIso inclusion projection _ _ _ inclusionGeneric
      projectionGeneric sourceMaximalZero modelMaximalZero
  have genericRank : letI := functionFieldAlgebra projection projectionGeneric
      Module.finrank source.functionField graph.image.functionField = 1 := by
    let := functionFieldAlgebra projection projectionGeneric
    let equivalence : source.functionField ≃ₐ[source.functionField] graph.image.functionField :=
      AlgEquiv.ofBijective (Algebra.ofId _ _) genericBijective
    rw [← equivalence.toLinearEquiv.finrank_eq, Module.finrank_self]
  exact ⟨graph.image, inferInstance, inferInstance, projection, inferInstance,
    projectionGeneric, genericRank, targetProjection, inferInstance, projectionsBase, targetGeneric⟩

end AlgebraicGeometry.ProperRationalGraph
