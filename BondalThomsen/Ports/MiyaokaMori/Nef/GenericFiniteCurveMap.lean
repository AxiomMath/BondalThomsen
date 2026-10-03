module

public import BondalThomsen.Ports.MiyaokaMori.Nef.IntegralFunctionFieldDimension
public import Mathlib.RingTheory.FiniteType

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.IntegralFunctionFieldDimension
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry

theorem residueFieldMap_genericPoint_finite_of_equal_dimension
    {baseField : Type u} [Field baseField] {source target : Scheme.{u}}
    [IsIntegral source] [IsIntegral target]
    (sourceStructure : source ⟶ Spec (CommRingCat.of baseField))
    (targetStructure : target ⟶ Spec (CommRingCat.of baseField))
    [LocallyOfFiniteType sourceStructure] [LocallyOfFiniteType targetStructure]
    (morphism : source ⟶ target)
    (baseCompatibility : morphism ≫ targetStructure = sourceStructure)
    (genericEquality : morphism (genericPoint source) = genericPoint target)
    (dimensionEquality : topologicalKrullDim source = topologicalKrullDim target) :
    (morphism.residueFieldMap (genericPoint source)).hom.Finite := by
  classical
  have : LocallyOfFiniteType morphism := by
    have : LocallyOfFiniteType (morphism ≫ targetStructure) := by
      rw [baseCompatibility]
      infer_instance
    exact locallyOfFiniteType_of_comp morphism targetStructure
  obtain ⟨_, ⟨targetRegion, targetAffine, rfl⟩, targetGenericMember, _⟩ :=
    target.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint target)) isOpen_univ
  have sourcePreimageMember : genericPoint source ∈ morphism ⁻¹ᵁ targetRegion := by
    show morphism (genericPoint source) ∈ targetRegion
    rw [genericEquality]
    exact targetGenericMember
  obtain ⟨_, ⟨sourceRegion, sourceAffine, rfl⟩, sourceGenericMember, sourceContained⟩ :=
    source.isBasis_affineOpens.exists_subset_of_mem_open sourcePreimageMember
      (morphism ⁻¹ᵁ targetRegion).2
  have containment : sourceRegion ≤ morphism ⁻¹ᵁ targetRegion := sourceContained
  let := baseSectionAlgebra targetStructure targetRegion
  let := baseSectionAlgebra sourceStructure sourceRegion
  let : Algebra Γ(target, targetRegion) Γ(source, sourceRegion) :=
    (morphism.appLE targetRegion sourceRegion containment).hom.toAlgebra
  have : IsScalarTower baseField Γ(target, targetRegion) Γ(source, sourceRegion) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have sectionCompatibility :
        targetStructure.appLE ⊤ targetRegion le_top ≫
          morphism.appLE targetRegion sourceRegion containment =
        sourceStructure.appLE ⊤ sourceRegion le_top := by
      rw [Scheme.Hom.appLE_comp_appLE morphism targetStructure ⊤ targetRegion sourceRegion
        le_top containment, baseCompatibility]
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← CommRingCat.hom_comp, Category.assoc, sectionCompatibility]
  have : FaithfulSMul Γ(target, targetRegion) Γ(source, sourceRegion) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (appLE_injective_of_genericPoint morphism genericEquality targetRegion sourceRegion
        containment sourceGenericMember)
  have : Nonempty targetRegion := ⟨⟨_, targetGenericMember⟩⟩
  have : Nonempty sourceRegion := ⟨⟨_, sourceGenericMember⟩⟩
  have := baseSectionAlgebra_finiteType targetStructure targetAffine
  have := baseSectionAlgebra_finiteType sourceStructure sourceAffine
  have targetTrdegDimension :
      topologicalKrullDim target =
        (Cardinal.toENat (Algebra.trdeg baseField Γ(target, targetRegion)) : WithBot ℕ∞) := by
    let := baseFunctionFieldAlgebra targetStructure
    have := baseSectionFunctionField_tower targetStructure targetRegion
    have := functionField_isFractionRing_of_isAffineOpen target targetRegion targetAffine
    have : FaithfulSMul Γ(target, targetRegion) target.functionField :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
    have : Algebra.IsAlgebraic Γ(target, targetRegion) target.functionField :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(target, targetRegion))
    have relativeZero : Algebra.trdeg Γ(target, targetRegion) target.functionField = 0 := trdeg_eq_zero
    rw [topologicalKrullDim_eq_trdeg_functionField targetStructure,
      ← trdeg_add_eq baseField Γ(target, targetRegion) (A := target.functionField), relativeZero,
      add_zero]
  have sourceTrdegDimension :
      topologicalKrullDim source =
        (Cardinal.toENat (Algebra.trdeg baseField Γ(source, sourceRegion)) : WithBot ℕ∞) := by
    let := baseFunctionFieldAlgebra sourceStructure
    have := baseSectionFunctionField_tower sourceStructure sourceRegion
    have := functionField_isFractionRing_of_isAffineOpen source sourceRegion sourceAffine
    have : FaithfulSMul Γ(source, sourceRegion) source.functionField :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
    have : Algebra.IsAlgebraic Γ(source, sourceRegion) source.functionField :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(source, sourceRegion))
    have relativeZero : Algebra.trdeg Γ(source, sourceRegion) source.functionField = 0 := trdeg_eq_zero
    rw [topologicalKrullDim_eq_trdeg_functionField sourceStructure,
      ← trdeg_add_eq baseField Γ(source, sourceRegion) (A := source.functionField), relativeZero,
      add_zero]
  obtain ⟨targetDimension, targetTrdeg⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := baseField) (S := Γ(target, targetRegion)))
  obtain ⟨sourceDimension, sourceTrdeg⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := baseField) (S := Γ(source, sourceRegion)))
  have sameFiniteDimension : sourceDimension = targetDimension := by
    rw [sourceTrdegDimension, targetTrdegDimension, targetTrdeg, sourceTrdeg,
      Cardinal.toENat_nat, Cardinal.toENat_nat] at dimensionEquality
    exact_mod_cast dimensionEquality
  have : Algebra.IsAlgebraic Γ(target, targetRegion) Γ(source, sourceRegion) := by
    rw [← trdeg_eq_zero_iff]
    have towerTrdeg := trdeg_add_eq baseField Γ(target, targetRegion) (A := Γ(source, sourceRegion))
    rw [targetTrdeg, sourceTrdeg, sameFiniteDimension] at towerTrdeg
    have relativeFinite : Algebra.trdeg Γ(target, targetRegion) Γ(source, sourceRegion) <
        Cardinal.aleph0 := by
      by_contra notFinite
      have tooLarge : Cardinal.aleph0 ≤ (targetDimension : Cardinal.{u}) :=
        (not_lt.mp notFinite).trans
          ((self_le_add_left _ _).trans_eq towerTrdeg)
      exact (not_le.mpr Cardinal.natCast_lt_aleph0) tooLarge
    obtain ⟨relativeDimension, relativeTrdeg⟩ := Cardinal.lt_aleph0.mp relativeFinite
    rw [relativeTrdeg] at towerTrdeg ⊢
    have dimensionSum : targetDimension + relativeDimension = targetDimension := by
      exact_mod_cast towerTrdeg
    have relativeZero : relativeDimension = 0 := by omega
    simp [relativeZero]
  let := (target.evaluation targetRegion (morphism (genericPoint source))
    (containment sourceGenericMember)).hom.toAlgebra
  let := (morphism.residueFieldMap (genericPoint source)).hom.toAlgebra
  let := (source.evaluation sourceRegion (genericPoint source) sourceGenericMember).hom.toAlgebra
  let : Algebra Γ(target, targetRegion) (source.residueField (genericPoint source)) :=
    ((morphism.residueFieldMap (genericPoint source)).hom.comp
      (target.evaluation targetRegion (morphism (genericPoint source))
        (containment sourceGenericMember)).hom).toAlgebra
  have : IsScalarTower Γ(target, targetRegion)
      (target.residueField (morphism (genericPoint source)))
      (source.residueField (genericPoint source)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(target, targetRegion) Γ(source, sourceRegion)
      (source.residueField (genericPoint source)) :=
    IsScalarTower.of_algebraMap_eq fun element =>
      residueFieldMap_evaluation_eq_evaluation_appLE morphism targetRegion sourceRegion
        containment _ sourceGenericMember element
  have : Algebra.IsAlgebraic Γ(source, sourceRegion) (source.residueField (genericPoint source)) :=
    residueField_isAlgebraic_of_isAffineOpen sourceAffine _ sourceGenericMember
  have : Algebra.IsAlgebraic Γ(target, targetRegion) (source.residueField (genericPoint source)) :=
    Algebra.IsAlgebraic.trans _ Γ(source, sourceRegion) _
  have : Algebra.IsAlgebraic (target.residueField (morphism (genericPoint source)))
      (source.residueField (genericPoint source)) := by
    apply Algebra.IsAlgebraic.extendScalars (R := Γ(target, targetRegion))
    have evaluationInjective : ∀ point : target, ∀ member : point ∈ targetRegion,
        point = genericPoint target → Function.Injective (target.evaluation targetRegion point member) := by
      rintro point member rfl
      exact evaluation_genericPoint_injective targetRegion member
    exact evaluationInjective _ _ genericEquality
  have : Algebra.EssFiniteType (target.residueField (morphism (genericPoint source)))
      (source.residueField (genericPoint source)) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap morphism (genericPoint source))
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end AlgebraicGeometry
