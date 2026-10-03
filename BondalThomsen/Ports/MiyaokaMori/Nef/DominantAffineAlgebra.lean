module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ProjectiveLinePrincipalDegreeZero
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Algebraic.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Opposite
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry

variable {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target] (morphism : source ⟶ target)

theorem genericPoint_mem_of_nonempty (sourceRegion : source.Opens) (hV : (sourceRegion : Set source).Nonempty) :
    genericPoint source ∈ sourceRegion := by
  refine ((genericPoint_spec source).mem_open_set_iff sourceRegion.2).mpr ?_
  simpa using hV

theorem evaluation_genericPoint_injective (sourceRegion : source.Opens) (hV : genericPoint source ∈ sourceRegion) :
    Function.Injective (source.evaluation sourceRegion (genericPoint source) hV) := by
  have h1 : Function.Injective (source.presheaf.germ sourceRegion (genericPoint source) hV) :=
    germ_injective_of_isIntegral _ _ hV
  have h2 : Function.Injective (source.residue (genericPoint source)) :=
    (IsLocalRing.residue (source.functionField)).injective
  exact h2.comp h1

theorem residueFieldMap_evaluation_eq_evaluation_appLE (region : target.Opens) (sourceRegion : source.Opens)
    (contained : sourceRegion ≤ morphism ⁻¹ᵁ region) (point : source) (hx : point ∈ sourceRegion) (element : Γ(target, region)) :
    morphism.residueFieldMap point (target.evaluation region (morphism point) (contained hx) element) =
      source.evaluation sourceRegion point hx (morphism.appLE region sourceRegion contained element) := by
  refine (Scheme.evaluation_naturality_apply morphism point (contained hx) element).trans ?_
  simp only [Scheme.Hom.appLE, Scheme.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

theorem appLE_injective_of_genericPoint (hf : morphism (genericPoint source) = genericPoint target)
    (region : target.Opens) (sourceRegion : source.Opens) (contained : sourceRegion ≤ morphism ⁻¹ᵁ region) (hV : genericPoint source ∈ sourceRegion) :
    Function.Injective (morphism.appLE region sourceRegion contained).hom := by
  rw [injective_iff_map_eq_zero]
  intro element ha
  have h1 := residueFieldMap_evaluation_eq_evaluation_appLE morphism region sourceRegion contained _ hV element
  rw [show (morphism.appLE region sourceRegion contained) element = 0 from ha, map_zero] at h1
  have h2 : target.evaluation region (morphism (genericPoint source)) (contained hV) element = 0 :=
    (morphism.residueFieldMap (genericPoint source)).hom.injective (by simpa using h1)
  replace h2 := (target.evaluation_eq_zero_iff_notMem_basicOpen _ (contained hV) element).mp h2
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  apply h2
  rw [hf]
  apply genericPoint_mem_of_nonempty
  exact Set.nonempty_iff_ne_empty.mpr fun equality ↦ hne (Opens.ext (equality.trans Opens.coe_bot.symm))

theorem residueField_isAlgebraic_of_isAffineOpen {region : target.Opens} (hU : IsAffineOpen region) (targetPoint : target)
    (hy : targetPoint ∈ region) :
    letI := (target.evaluation region targetPoint hy).hom.toAlgebra
    Algebra.IsAlgebraic Γ(target, region) (target.residueField targetPoint) := by
  let := (target.evaluation region targetPoint hy).hom.toAlgebra
  let := target.presheaf.algebra_section_stalk ⟨targetPoint, hy⟩
  have hloc := hU.isLocalization_stalk ⟨targetPoint, hy⟩
  have : Nontrivial Γ(target, region) := by
    have : Nonempty region := ⟨⟨targetPoint, hy⟩⟩
    infer_instance
  have halg : Algebra.IsAlgebraic Γ(target, region) (target.presheaf.stalk targetPoint) :=
    IsLocalization.isAlgebraic _ (hU.primeIdealOf ⟨targetPoint, hy⟩).asIdeal.primeCompl
  let ringMap : target.presheaf.stalk targetPoint →ₐ[Γ(target, region)] target.residueField targetPoint :=
    { (target.residue targetPoint).hom with commutes' := fun _ ↦ rfl }
  refine ⟨fun element ↦ ?_⟩
  obtain ⟨preimage, rfl⟩ := target.residue_surjective targetPoint element
  exact (halg.isAlgebraic preimage).algHom ringMap

theorem appLE_isAlgebraic_of_genericPoint
    (hfin : (morphism.residueFieldMap (genericPoint source)).hom.Finite)
    {region : target.Opens} (hU : IsAffineOpen region) (sourceRegion : source.Opens) (contained : sourceRegion ≤ morphism ⁻¹ᵁ region)
    (hV : genericPoint source ∈ sourceRegion) :
    letI := (morphism.appLE region sourceRegion contained).hom.toAlgebra
    Algebra.IsAlgebraic Γ(target, region) Γ(source, sourceRegion) := by
  let algRC := (morphism.appLE region sourceRegion contained).hom.toAlgebra
  let algRk := (target.evaluation region (morphism (genericPoint source)) (contained hV)).hom.toAlgebra
  let algkl := (morphism.residueFieldMap (genericPoint source)).hom.toAlgebra
  let algCl := (source.evaluation sourceRegion (genericPoint source) hV).hom.toAlgebra
  let algRl : Algebra Γ(target, region) (source.residueField (genericPoint source)) :=
    ((morphism.residueFieldMap (genericPoint source)).hom.comp
      (target.evaluation region (morphism (genericPoint source)) (contained hV)).hom).toAlgebra
  have t1 : IsScalarTower Γ(target, region) (target.residueField (morphism (genericPoint source)))
      (source.residueField (genericPoint source)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have t2 : IsScalarTower Γ(target, region) Γ(source, sourceRegion) (source.residueField (genericPoint source)) :=
    IsScalarTower.of_algebraMap_eq fun element ↦
      residueFieldMap_evaluation_eq_evaluation_appLE morphism region sourceRegion contained _ hV element
  have a1 : Algebra.IsAlgebraic Γ(target, region) (target.residueField (morphism (genericPoint source))) :=
    residueField_isAlgebraic_of_isAffineOpen hU _ (contained hV)
  have hfin' : Module.Finite (target.residueField (morphism (genericPoint source)))
      (source.residueField (genericPoint source)) := hfin
  have a2 : Algebra.IsAlgebraic (target.residueField (morphism (genericPoint source)))
      (source.residueField (genericPoint source)) := Algebra.IsAlgebraic.of_finite _ _
  have a3 : Algebra.IsAlgebraic Γ(target, region) (source.residueField (genericPoint source)) :=
    Algebra.IsAlgebraic.trans _ (target.residueField (morphism (genericPoint source))) _
  refine ⟨fun element ↦ ?_⟩
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom Γ(target, region) Γ(source, sourceRegion)
    (source.residueField (genericPoint source))) (evaluation_genericPoint_injective sourceRegion hV)).mp
    (a3.isAlgebraic _)

end AlgebraicGeometry

end
