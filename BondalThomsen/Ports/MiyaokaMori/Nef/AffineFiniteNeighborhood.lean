module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperHeightOneFiniteness
public import BondalThomsen.Ports.MiyaokaMori.Nef.AffineFiberTransport

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

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
theorem isFinite_morphismRestrict_of_le {source target : Scheme.{u}} (morphism : source ⟶ target) {region sourceRegion : target.Opens}
    (hUV : region ≤ sourceRegion) [IsFinite (morphism ∣_ sourceRegion)] : IsFinite (morphism ∣_ region) := by
  have h1 : IsFinite (morphism ∣_ sourceRegion ∣_ (sourceRegion.ι ⁻¹ᵁ region)) := inferInstance
  have h2 : IsFinite (morphism ∣_ (sourceRegion.ι ''ᵁ (sourceRegion.ι ⁻¹ᵁ region))) :=
    ((MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict morphism sourceRegion _))).mp h1
  have h3 : sourceRegion.ι ''ᵁ (sourceRegion.ι ⁻¹ᵁ region) = region := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hUV
  rwa [h3] at h2

set_option backward.isDefEq.respectTransparency.types false in
theorem isAffineOpen_preimage_and_finite_app_of_isFinite {source target : Scheme.{u}} (morphism : source ⟶ target)
    {region : target.Opens} (hU : IsAffineOpen region) [IsFinite (morphism ∣_ region)] :
    IsAffineOpen (morphism ⁻¹ᵁ region) ∧ (morphism.app region).hom.Finite := by
  have : IsAffine region.toScheme := hU
  refine ⟨isAffine_of_isAffineHom (morphism ∣_ region), ?_⟩
  have equality := IsFinite.finite_app (morphism ∣_ region) ⊤ (isAffineOpen_top _)
  rw [Scheme.Hom.app_eq_appLE, morphismRestrict_appLE] at equality
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr morphism _ (Scheme.Opens.ι_image_top region) (by simp)
    (fun morphism => morphism.hom.Finite)).mp equality

theorem exists_affine_finite_neighbourhood {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    [IsLocallyNoetherian target] (morphism : source ⟶ target) [IsProper morphism]
    (hp : morphism.base (genericPoint source) = genericPoint target)
    (hfin : (morphism.residueFieldMap (genericPoint source)).hom.Finite) (targetPoint : target)
    (hz : ringKrullDim (target.presheaf.stalk targetPoint) = 1) :
    ∃ region : target.Opens, IsAffineOpen region ∧ targetPoint ∈ region ∧ IsAffineOpen (morphism ⁻¹ᵁ region) ∧ (morphism.app region).hom.Finite := by
  obtain ⟨sourceRegion, hzV, hV⟩ := exists_isFinite_restrict_of_dim_one morphism hp hfin targetPoint hz
  obtain ⟨_, ⟨region, hU, rfl⟩, hzU, hUV⟩ :=
    target.isBasis_affineOpens.exists_subset_of_mem_open hzV sourceRegion.2
  have := isFinite_morphismRestrict_of_le morphism (region := region) (sourceRegion := sourceRegion) hUV
  exact ⟨region, hU, hzU, isAffineOpen_preimage_and_finite_app_of_isFinite morphism hU⟩

end AlgebraicGeometry

end
