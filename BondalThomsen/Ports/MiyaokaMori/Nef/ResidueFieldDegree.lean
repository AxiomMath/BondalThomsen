module

public import BondalThomsen.Ports.MiyaokaMori.Nef.DimensionCycle
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BigOperators

universe u

noncomputable section

namespace AlgebraicGeometry.Intersection

theorem pointClosureDimension_eq_zero_of_isClosed {scheme : Scheme.{u}} (point : scheme)
    (closed : IsClosed ({point} : Set scheme)) : pointClosureDimension scheme point = 0 := by
  rw [pointClosureDimension_eq_topologicalKrullDim_closure, closed.closure_eq]
  let : Nonempty ({point} : Set scheme) := ⟨⟨point, rfl⟩⟩
  let : IrreducibleSpace ({point} : Set scheme) :=
    isIrreducible_iff_irreducibleSpace.mp isIrreducible_singleton
  let : Nonempty (IrreducibleCloseds ({point} : Set scheme)) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

def pointBaseMap {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) (point : scheme) :
    CommRingCat.of baseField ⟶ scheme.residueField point :=
  Spec.preimage (scheme.fromSpecResidueField point ≫ structureMap)

def residueFieldDegree {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) (point : scheme) : ℕ := by
  letI : Algebra baseField (scheme.residueField point) :=
    (pointBaseMap structureMap point).hom.toAlgebra
  exact Module.finrank baseField (scheme.residueField point)

end AlgebraicGeometry.Intersection

open AlgebraicGeometry.Intersection in
theorem AlgebraicGeometry.Scheme.Hom.residueFieldDegree_eq_residueDegree
    {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) (point : scheme) :
    residueFieldDegree structureMap point = structureMap.residueDegree point := by
  let baseMap : CommRingCat.of baseField ⟶
      (Spec (CommRingCat.of baseField)).residueField (structureMap point) :=
    Spec.preimage ((Spec (CommRingCat.of baseField)).fromSpecResidueField (structureMap point))
  have composite : pointBaseMap structureMap point = baseMap ≫ structureMap.residueFieldMap point := by
    apply Spec.map_injective
    rw [pointBaseMap, Spec.map_preimage, Spec.map_comp, Spec.map_preimage,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have bijective : Function.Bijective baseMap.hom := by
    let : (structureMap point).asIdeal.IsPrime := (structureMap point).isPrime
    have baseMapEquation : baseMap =
        CommRingCat.ofHom (algebraMap baseField (structureMap point).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (CommRingCat.of baseField) (structureMap point)).inv := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp,
        Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    have idealBot : (structureMap point).asIdeal = (⊥ : Ideal baseField) :=
      Ideal.eq_bot_of_prime (structureMap point).asIdeal
    let : (structureMap point).asIdeal.IsMaximal := by
      rw [idealBot]
      exact Ideal.bot_isMaximal
    have surjective : Function.Surjective
        (algebraMap baseField (structureMap point).asIdeal.ResidueField) :=
      Ideal.algebraMap_residueField_surjective (structureMap point).asIdeal
    have injective : Function.Injective
        (algebraMap baseField (structureMap point).asIdeal.ResidueField) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField, idealBot]
    have isoBijective : Function.Bijective
        (Scheme.Spec.residueFieldIso (CommRingCat.of baseField) (structureMap point)).inv.hom :=
      ConcreteCategory.bijective_of_isIso _
    rw [baseMapEquation]
    exact isoBijective.comp ⟨injective, surjective⟩
  unfold residueFieldDegree Scheme.Hom.residueDegree
  let : Algebra baseField (scheme.residueField point) :=
    (pointBaseMap structureMap point).hom.toAlgebra
  let : Algebra ((Spec (CommRingCat.of baseField)).residueField (structureMap point))
      (scheme.residueField point) := (structureMap.residueFieldMap point).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.ofBijective baseMap.hom bijective) (RingEquiv.refl _) ?_
  ext scalar
  change (structureMap.residueFieldMap point).hom (baseMap.hom scalar) =
    (pointBaseMap structureMap point).hom scalar
  rw [composite]
  rfl

