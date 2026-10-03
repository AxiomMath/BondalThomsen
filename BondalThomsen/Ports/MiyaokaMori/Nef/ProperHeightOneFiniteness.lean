module

public import BondalThomsen.Ports.MiyaokaMori.Nef.HeightOnePrimes
public import BondalThomsen.Ports.MiyaokaMori.Nef.DominantAffineAlgebra
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Polynomial
open scoped Classical AlgebraicGeometry

universe u

noncomputable section

open AlgebraicGeometry in

private theorem finite_fiber_inter_affine {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    [IsLocallyNoetherian target] (morphism : source ⟶ target) [LocallyOfFiniteType morphism]
    (hf : morphism.base (genericPoint source) = genericPoint target)
    (hfin : (morphism.residueFieldMap (genericPoint source)).hom.Finite) (targetPoint : target)
    (hξ : ringKrullDim (target.presheaf.stalk targetPoint) = 1) {region : target.Opens} (hU : IsAffineOpen region) (hξU : targetPoint ∈ region)
    {sourceRegion : source.Opens} (hV : IsAffineOpen sourceRegion) (contained : sourceRegion ≤ morphism ⁻¹ᵁ region) :
    (morphism.base ⁻¹' {targetPoint} ∩ (sourceRegion : Set source)).Finite := by
  classical
  by_cases hne : (sourceRegion : Set source).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.inter_empty]; exact Set.finite_empty
  have hηV : genericPoint source ∈ sourceRegion := genericPoint_mem_of_nonempty sourceRegion hne
  have : Nonempty region := ⟨⟨targetPoint, hξU⟩⟩
  have : Nonempty sourceRegion := ⟨⟨_, hηV⟩⟩
  have hinj := appLE_injective_of_genericPoint morphism hf region sourceRegion contained hηV
  have halg := appLE_isAlgebraic_of_genericPoint morphism hfin hU sourceRegion contained hηV
  have hft : (morphism.appLE region sourceRegion contained).hom.FiniteType := morphism.finiteType_appLE hU hV contained
  have hnoeth : IsNoetherianRing Γ(target, region) := IsLocallyNoetherian.component_noetherian ⟨region, hU⟩
  algebraize [(morphism.appLE region sourceRegion contained).hom]
  have : FaithfulSMul Γ(target, region) Γ(source, sourceRegion) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let primeIdeal : Ideal Γ(target, region) := (hU.primeIdealOf ⟨targetPoint, hξU⟩).asIdeal
  have hp : primeIdeal.height = 1 := by
    let := target.presheaf.algebra_section_stalk ⟨targetPoint, hξU⟩
    have hloc := hU.isLocalization_stalk ⟨targetPoint, hξU⟩
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height primeIdeal (target.presheaf.stalk targetPoint)
    rw [hξ] at h1
    exact_mod_cast h1.symm
  obtain ⟨hfinite, -⟩ := Ideal.finite_primesOver_and_height_eq_one (extensionRing := Γ(source, sourceRegion)) primeIdeal hp
  let ringMap : source → Ideal Γ(source, sourceRegion) := fun generator ↦
    if equality : generator ∈ sourceRegion then (hV.primeIdealOf ⟨generator, equality⟩).asIdeal else ⊥
  refine Set.Finite.of_injOn (f := ringMap) (t := primeIdeal.primesOver Γ(source, sourceRegion)) ?_ ?_ hfinite
  · rintro generator ⟨hxξ, hxV⟩
    have hxV' : generator ∈ sourceRegion := hxV
    simp only [ringMap, dite_eq_left hxV']
    refine ⟨(hV.primeIdealOf ⟨generator, hxV'⟩).isPrime, ⟨?_⟩⟩
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := morphism) region hU sourceRegion hV contained hxV'
    have hxξ' : morphism.base generator = targetPoint := hxξ
    subst hxξ'
    exact congr($(h1).asIdeal).symm
  · rintro generator ⟨-, hxV⟩ otherPoint ⟨-, hxV'⟩ hxx'
    have hxV₁ : generator ∈ sourceRegion := hxV
    have hxV₂ : otherPoint ∈ sourceRegion := hxV'
    simp only [ringMap, dite_eq_left hxV₁, dite_eq_left hxV₂] at hxx'
    have h2 : hV.primeIdealOf ⟨generator, hxV₁⟩ = hV.primeIdealOf ⟨otherPoint, hxV₂⟩ := PrimeSpectrum.ext hxx'
    have h3 := hV.fromSpec_primeIdealOf ⟨generator, hxV₁⟩
    rw [h2, hV.fromSpec_primeIdealOf] at h3
    exact h3.symm

theorem AlgebraicGeometry.exists_isFinite_restrict_of_dim_one {source target : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral source] [AlgebraicGeometry.IsIntegral target]
    [AlgebraicGeometry.IsLocallyNoetherian target] (morphism : source ⟶ target) [AlgebraicGeometry.IsProper morphism]
    (hf : morphism.base (genericPoint source) = genericPoint target)
    (hfin : (morphism.residueFieldMap (genericPoint source)).hom.Finite) (targetPoint : target)
    (hξ : ringKrullDim (target.presheaf.stalk targetPoint) = 1) :
    ∃ sourceRegion : target.Opens, targetPoint ∈ sourceRegion ∧ AlgebraicGeometry.IsFinite (morphism ∣_ sourceRegion) := by
  apply exists_isFinite_morphismRestrict_of_finite_preimage_singleton
  obtain ⟨_, ⟨region, hU, rfl⟩, hξU, -⟩ := target.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ targetPoint) isOpen_univ
  have hc : IsCompact (morphism ⁻¹ᵁ region : Set source) :=
    QuasiCompact.isCompact_preimage (f := morphism) _ region.2 hU.isCompact
  obtain ⟨generators, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := morphism ⁻¹ᵁ region)).mp hc
  have hle : ∀ sourceRegion ∈ generators, (sourceRegion : source.Opens) ≤ morphism ⁻¹ᵁ region := fun sourceRegion hV ↦ by
    rw [hsU]; exact le_iSup₂ (f := fun (i : source.affineOpens) (_ : i ∈ generators) ↦ (i : source.Opens)) sourceRegion hV
  refine (hs.biUnion fun sourceRegion hV ↦ finite_fiber_inter_affine morphism hf hfin targetPoint hξ hU hξU sourceRegion.2
    (hle sourceRegion hV)).subset ?_
  intro generator hx
  have hxU : generator ∈ morphism ⁻¹ᵁ region := by
    have : morphism.base generator = targetPoint := hx
    show morphism.base generator ∈ region
    rw [this]; exact hξU
  rw [hsU] at hxU
  simp only [Opens.mem_iSup] at hxU
  obtain ⟨sourceRegion, hVs, hxV⟩ := hxU
  exact Set.mem_biUnion hVs ⟨hx, hxV⟩

end
