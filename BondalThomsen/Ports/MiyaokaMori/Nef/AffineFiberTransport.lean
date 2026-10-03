module

public import BondalThomsen.Ports.MiyaokaMori.Nef.DominantAffineAlgebra
public import BondalThomsen.Ports.MiyaokaMori.Nef.ResidueDegreeComposition
public import Mathlib.AlgebraicGeometry.ResidueField

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

variable {source target : Scheme.{u}} (morphism : source ⟶ target)

def stalkMapOfEq {point : source} {targetPoint : target} (hx : morphism.base point = targetPoint) : target.presheaf.stalk targetPoint →+* source.presheaf.stalk point :=
  ((target.presheaf.stalkCongr (Inseparable.of_eq hx.symm)).hom ≫ morphism.stalkMap point).hom

theorem stalkMapOfEq_germ {point : source} {targetPoint : target} (hx : morphism.base point = targetPoint) (region : target.Opens) (hz : targetPoint ∈ region)
    (element : Γ(target, region)) :
    stalkMapOfEq morphism hx (target.presheaf.germ region targetPoint hz element) =
      source.presheaf.germ (morphism ⁻¹ᵁ region) point (show morphism.base point ∈ region from hx ▸ hz) (morphism.app region element) := by
  subst hx
  simp only [stalkMapOfEq, TopCat.Presheaf.stalkCongr, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact Scheme.Hom.germ_stalkMap_apply morphism region point hz element

instance isLocalHom_stalkMapOfEq {point : source} {targetPoint : target} (hx : morphism.base point = targetPoint) :
    IsLocalHom (stalkMapOfEq morphism hx) := by
  subst hx
  unfold stalkMapOfEq
  rw [CommRingCat.hom_comp]
  infer_instance

private theorem finrank_residueField_congr {A S : Type*} [CommRing A] [CommRing S] [IsLocalRing A]
    [IsLocalRing S] (morphism g : A →+* S) [IsLocalHom morphism] [IsLocalHom g] (equality : morphism = g) :
    (letI := (IsLocalRing.ResidueField.map morphism).toAlgebra
     Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S)) =
    (letI := (IsLocalRing.ResidueField.map g).toAlgebra
     Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S)) := by
  subst equality; rfl

theorem finrank_residueField_stalkMapOfEq {point : source} {targetPoint : target} (hx : morphism.base point = targetPoint) :
    (letI := (IsLocalRing.ResidueField.map (stalkMapOfEq morphism hx)).toAlgebra
     Module.finrank (IsLocalRing.ResidueField (target.presheaf.stalk targetPoint))
      (IsLocalRing.ResidueField (source.presheaf.stalk point))) = morphism.residueDegree point := by
  subst hx
  have equality : stalkMapOfEq morphism rfl = (morphism.stalkMap point).hom := by
    ext element
    simp [stalkMapOfEq, TopCat.Presheaf.stalkCongr]
  exact (finrank_residueField_congr _ _ equality).trans rfl

section Fiber

variable {region : target.Opens} (hU : IsAffineOpen region) (hW : IsAffineOpen (morphism ⁻¹ᵁ region)) {targetPoint : target} (hz : targetPoint ∈ region)

theorem fromSpec_mem_of_isAffineOpen {source : Scheme.{u}} {sourceRegion : source.Opens} (hW : IsAffineOpen sourceRegion)
    (primePoint : Spec Γ(source, sourceRegion)) : hW.fromSpec primePoint ∈ sourceRegion := by
  have : hW.fromSpec primePoint ∈ Set.range hW.fromSpec := ⟨primePoint, rfl⟩
  rwa [hW.range_fromSpec] at this

theorem primeIdealOf_fromSpec {source : Scheme.{u}} {sourceRegion : source.Opens} (hW : IsAffineOpen sourceRegion)
    (primePoint : Spec Γ(source, sourceRegion)) :
    hW.primeIdealOf ⟨hW.fromSpec primePoint, fromSpec_mem_of_isAffineOpen hW primePoint⟩ = primePoint := by
  apply hW.fromSpec.isOpenEmbedding.injective
  exact hW.fromSpec_primeIdealOf _

abbrev appPreimage (region : target.Opens) : Γ(target, region) →+* Γ(source, morphism ⁻¹ᵁ region) := (morphism.app region).hom

include hU in
theorem comap_primeIdealOf_app {point : source} (hx : point ∈ morphism ⁻¹ᵁ region) :
    (hW.primeIdealOf ⟨point, hx⟩).asIdeal.comap (appPreimage morphism region) =
      (hU.primeIdealOf ⟨morphism.base point, hx⟩).asIdeal := by
  have equality := IsAffineOpen.comap_primeIdealOf_appLE (f := morphism) region hU (morphism ⁻¹ᵁ region) hW le_rfl hx
  rw [← Scheme.Hom.app_eq_appLE] at equality
  exact congr($(equality).asIdeal)

theorem base_fromSpec_eq (primePoint : Spec Γ(source, morphism ⁻¹ᵁ region))
    (primeEquation : primePoint.asIdeal.comap (appPreimage morphism region) = (hU.primeIdealOf ⟨targetPoint, hz⟩).asIdeal) :
    morphism.base (hW.fromSpec primePoint) = targetPoint := by
  have hx := fromSpec_mem_of_isAffineOpen hW primePoint
  have h1 := comap_primeIdealOf_app morphism hU hW hx
  rw [primeIdealOf_fromSpec hW primePoint, primeEquation] at h1
  have h2 : hU.primeIdealOf ⟨targetPoint, hz⟩ = hU.primeIdealOf ⟨morphism.base (hW.fromSpec primePoint), hx⟩ :=
    PrimeSpectrum.ext h1
  have h3 := hU.fromSpec_primeIdealOf ⟨targetPoint, hz⟩
  rw [h2, hU.fromSpec_primeIdealOf] at h3
  exact h3

def fiberEquiv :
    {primePoint : PrimeSpectrum Γ(source, morphism ⁻¹ᵁ region) //
      primePoint.asIdeal.comap (appPreimage morphism region) = (hU.primeIdealOf ⟨targetPoint, hz⟩).asIdeal} ≃
    {point : source // morphism.base point = targetPoint} where
  toFun primePoint := ⟨hW.fromSpec primePoint.1, base_fromSpec_eq morphism hU hW hz primePoint.1 primePoint.2⟩
  invFun point := ⟨hW.primeIdealOf ⟨point.1, show morphism.base point.1 ∈ region by rw [point.2]; exact hz⟩, by
    obtain ⟨point, rfl⟩ := point
    exact comap_primeIdealOf_app morphism hU hW _⟩
  left_inv primePoint := Subtype.ext (primeIdealOf_fromSpec hW primePoint.1)
  right_inv point := Subtype.ext (hW.fromSpec_primeIdealOf _)

end Fiber

end AlgebraicGeometry

end
