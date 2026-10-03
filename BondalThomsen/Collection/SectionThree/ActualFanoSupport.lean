module

public import BondalThomsen.Toric.Positivity.ActualAmpleStrictSupportCriterion
public import BondalThomsen.Collection.SectionThree.Equivalences
public import BondalThomsen.Fan.PrimitiveRelationBasis
public import BondalThomsen.Fan.PrimitiveRelationDegree

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Module Finset
open TauCeti.AlgebraicGeometry TauCeti.Toric.Fan

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem PrimitiveLatticeRelation.degree_pos_of_actualCanonicalInverse_isAmple
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ample :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      BondalThomsen.SchemeLineBundleClassAmple
        ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹)) :
    0 < relation.degree :=
  relation.degree_pos_of_strict_support complete regular
    (fan.strictAnticanonicalSupport_of_actualCanonicalInverse_isAmple 𝕜 complete regular ample)

theorem PrimitiveLatticeRelation.coefficient_sum_lt_card_of_actualCanonicalInverse_isAmple
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ample :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      BondalThomsen.SchemeLineBundleClassAmple
        ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹)) :
    (∑ ray : right, relation.coefficients ray) < Fintype.card left :=
  relation.degree_pos_iff_coefficient_sum_lt.mp
    (relation.degree_pos_of_actualCanonicalInverse_isAmple 𝕜 complete regular ample)

theorem PrimitiveRelationConeBasis.strictAnticanonicalDatum_of_actualCanonicalInverse_isAmple
    {fan : Fan embedding} {left right : Finset fan.Ray}
    {relation : fan.PrimitiveLatticeRelation left right} {distinguished : left}
    {dimension : ℕ} (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ample :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      BondalThomsen.SchemeLineBundleClassAmple
        ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹))
    (ray : fan.Ray) (outside : ray.val ∉ Set.range cone_basis.basis) :
    (-1 : ℚ) < (cone_basis.anticanonicalDatum ray.val : ℚ) := by
  have bound := fan.strictAnticanonicalSupport_of_actualCanonicalInverse_isAmple 𝕜
    complete regular ample dimension cone_basis.basis cone_basis.cone_basis ray outside
  change (-1 : ℤ) < cone_basis.anticanonicalDatum ray.val at bound
  exact_mod_cast bound

end TauCeti.Toric.Fan

namespace BondalThomsen

universe schemeUniverse

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def ToricExtremalDropOneConeIncidence (fan : TauCeti.Toric.Fan embedding)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop) :
    Prop :=
  ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
    extremal left right relation →
      ∀ primitive : left, relation.DropOneConeIncidence primitive

theorem toricFanoExtremalSupport_of_actualCanonicalInverse_isAmple
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (reference : Basis (Fin dimension) ℤ Lattice)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (ample :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹))
    (incidence : ToricExtremalDropOneConeIncidence fan extremal) :
    ToricFanoExtremalSupport fan dimension extremal := by
  classical
  intro left right relation is_extremal
  have witnesses := fun primitive : left =>
    relation.exists_coneBasisWitness_of_dropOneCone primitive complete regular reference
      (incidence left right relation is_extremal primitive)
  let drop_one : ∀ primitive : left, PrimitiveRelationConeBasis relation primitive dimension :=
    fun primitive => Classical.choice (witnesses primitive)
  refine ⟨drop_one,
    relation.coefficient_sum_lt_card_of_actualCanonicalInverse_isAmple 𝕜 complete regular ample, ?_⟩
  intro primitive ray outside
  exact (drop_one primitive).strictAnticanonicalDatum_of_actualCanonicalInverse_isAmple 𝕜
    complete regular ample ray outside

theorem small_extremal_of_sheafExt_backward_ordering_of_actualCanonicalInverse_isAmple
    (fan : TauCeti.Toric.Fan embedding) [Fintype fan.BondalThomsenClass]
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (reference : Basis (Fin dimension) ℤ Lattice)
    (scheme : Scheme.{schemeUniverse})
    (realization : fan.InvariantRayDivisorClass → InvertibleSheaf scheme)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (ample :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹))
    (incidence : ToricExtremalDropOneConeIncidence fan extremal)
    (comparison : PrimitiveFloorPairSheafComparison fan scheme realization)
    (ordering : ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Ext (realization source.val).obj (realization target.val).obj degree),
          extension = 0) :
    ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1 :=
  small_extremal_of_sheafExt_backward_ordering fan complete dimension scheme realization extremal
    (toricFanoExtremalSupport_of_actualCanonicalInverse_isAmple 𝕜
      fan complete regular reference extremal ample incidence)
    comparison ordering

end BondalThomsen
