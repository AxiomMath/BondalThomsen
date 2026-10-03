module

public import BondalThomsen.LineBundle.AmpleLineBundleClassCriterion
public import BondalThomsen.LineBundle.SchemePicardGlobalGeneration
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.TensorProduct

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe schemeUniverse

noncomputable section

namespace BondalThomsen

variable {source target : Scheme.{schemeUniverse}}

def schemeRestrictedSection (map : source ⟶ target) [IsOpenImmersion map]
    (sheaf : target.Modules) (open_set : target.Opens) (section_value : Γ(sheaf, open_set)) :
    Γ(sheaf.restrict map, map ⁻¹ᵁ open_set) :=
  (sheaf.restrictAppIso map _).inv (sheaf.res (map.image_preimage_le open_set) section_value)

theorem schemeRestrictedSection_res (map : source ⟶ target) [IsOpenImmersion map]
    (sheaf : target.Modules) (open_set : target.Opens) (section_value : Γ(sheaf, open_set))
    (smaller : source.Opens) (inclusion : smaller ≤ map ⁻¹ᵁ open_set) :
    (sheaf.restrict map).res inclusion (schemeRestrictedSection map sheaf open_set section_value) =
      (sheaf.restrictAppIso map smaller).inv
        (sheaf.res ((map.image_mono inclusion).trans (map.image_preimage_le open_set)) section_value) := by
  change sheaf.res (map.image_mono inclusion)
    (sheaf.res (map.image_preimage_le open_set) section_value) = _
  rw [Scheme.Modules.res_res]
  rfl

theorem schemeRestrictedSection_isFrame (map : source ⟶ target) [IsOpenImmersion map]
    (sheaf : target.Modules) {open_set : target.Opens} {section_value : Γ(sheaf, open_set)}
    (frame : Scheme.Modules.IsFrame sheaf open_set section_value) :
    Scheme.Modules.IsFrame (sheaf.restrict map) (map ⁻¹ᵁ open_set)
      (schemeRestrictedSection map sheaf open_set section_value) := by
  intro smaller inclusion
  rw [schemeRestrictedSection_res]
  change Function.Bijective (fun scalar : Γ(source, smaller) =>
    (map.appIso smaller).inv scalar •
      sheaf.res ((map.image_mono inclusion).trans (map.image_preimage_le open_set)) section_value)
  exact (frame _ _).comp (ConcreteCategory.bijective_of_isIso (map.appIso smaller).inv)

def schemeRestrictedGlobalSection (map : source ⟶ target) [IsOpenImmersion map]
    (sheaf : target.Modules) (section_value : Γ(sheaf, ⊤)) : Γ(sheaf.restrict map, ⊤) :=
  schemeRestrictedSection map sheaf ⊤ section_value

theorem schemeRestrictedGlobalSection_res (map : source ⟶ target) [IsOpenImmersion map]
    (sheaf : target.Modules) (section_value : Γ(sheaf, ⊤)) (open_set : target.Opens) :
    (sheaf.restrict map).res le_top (schemeRestrictedGlobalSection map sheaf section_value) =
      schemeRestrictedSection map sheaf open_set (sheaf.res le_top section_value) := by
  change sheaf.res _ (sheaf.res _ section_value) =
    sheaf.res _ (sheaf.res le_top section_value)
  rw [Scheme.Modules.res_res]
  rw [Scheme.Modules.res_res]

theorem schemeRestrictedSection_smul (map : source ⟶ target) [IsOpenImmersion map]
    (sheaf : target.Modules) (open_set : target.Opens)
    (scalar : Γ(target, open_set)) (section_value : Γ(sheaf, open_set)) :
    schemeRestrictedSection map sheaf open_set (scalar • section_value) =
      map.app open_set scalar • schemeRestrictedSection map sheaf open_set section_value := by
  change sheaf.presheaf.map (homOfLE (map.image_preimage_le open_set)).op
    (scalar • section_value) =
      (map.appIso (map ⁻¹ᵁ open_set)).inv (map.app open_set scalar) •
        sheaf.presheaf.map (homOfLE (map.image_preimage_le open_set)).op section_value
  rw [Scheme.Modules.map_smul]
  have coefficient := ConcreteCategory.congr_hom (map.app_appIso_inv open_set) scalar
  change (map.appIso (map ⁻¹ᵁ open_set)).inv (map.app open_set scalar) = _ at coefficient
  rw [coefficient]
  rfl

instance schemeRestriction_isInvertible (map : source ⟶ target) [IsOpenImmersion map]
    (sheaf : target.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf] :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible source (sheaf.restrict map) := by
  exact (TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible source).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback map).app sheaf).symm inferInstance

theorem schemeRestrictedGlobalSection_nonvanishingLocus (map : source ⟶ target)
    [IsOpenImmersion map] (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (section_value : Γ(sheaf, ⊤)) :
    (sheaf.restrict map).nonvanishingLocus (schemeRestrictedGlobalSection map sheaf section_value) =
      map ⁻¹ᵁ sheaf.nonvanishingLocus section_value := by
  apply TopologicalSpace.Opens.ext
  ext point
  change point ∈ (sheaf.restrict map).nonvanishingLocus
    (schemeRestrictedGlobalSection map sheaf section_value) ↔
      map point ∈ sheaf.nonvanishingLocus section_value
  obtain ⟨open_set, contains, section_frame, frame⟩ := Scheme.Modules.exists_frame sheaf (map point)
  let restricted_frame := schemeRestrictedSection_isFrame map sheaf frame
  let coefficient := frame.coord le_rfl (sheaf.res le_top section_value)
  have relation : (sheaf.restrict map).res le_top
      (schemeRestrictedGlobalSection map sheaf section_value) =
      map.app open_set coefficient •
        schemeRestrictedSection map sheaf open_set section_frame := by
    rw [schemeRestrictedGlobalSection_res]
    rw [← frame.coord_smul_frame le_rfl (sheaf.res le_top section_value)]
    rw [Scheme.Modules.res_self, schemeRestrictedSection_smul]
  have coord_relation : restricted_frame.coord le_rfl
      ((sheaf.restrict map).res le_top (schemeRestrictedGlobalSection map sheaf section_value)) =
      map.app open_set coefficient := by
    apply (restricted_frame _ le_rfl).injective
    dsimp only
    rw [restricted_frame.coord_smul_frame, Scheme.Modules.res_self]
    exact relation
  have source_local := restricted_frame.inf_nonvanishingLocus_eq_basicOpen
    (sheaf.restrict map) (schemeRestrictedGlobalSection map sheaf section_value)
  rw [coord_relation, ← Scheme.preimage_basicOpen] at source_local
  have target_local := frame.inf_nonvanishingLocus_eq_basicOpen sheaf section_value
  have local_equality : (map ⁻¹ᵁ open_set) ⊓
      (sheaf.restrict map).nonvanishingLocus (schemeRestrictedGlobalSection map sheaf section_value) =
      map ⁻¹ᵁ (open_set ⊓ sheaf.nonvanishingLocus section_value) := by
    rw [source_local, target_local]
  have local_equivalence : point ∈ (map ⁻¹ᵁ open_set) ⊓
      (sheaf.restrict map).nonvanishingLocus (schemeRestrictedGlobalSection map sheaf section_value) ↔
      point ∈ map ⁻¹ᵁ (open_set ⊓ sheaf.nonvanishingLocus section_value) :=
    local_equality ▸ Iff.rfl
  change (map point ∈ open_set ∧ point ∈ (sheaf.restrict map).nonvanishingLocus
    (schemeRestrictedGlobalSection map sheaf section_value)) ↔
      (map point ∈ open_set ∧ map point ∈ sheaf.nonvanishingLocus section_value) at local_equivalence
  simpa only [contains, true_and] using local_equivalence

end BondalThomsen

