module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Flasque
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Basic
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.AffineQuasicoherentCohomologyVanishing

universe ringUniverse

noncomputable section

variable {ring : CommRingCat.{ringUniverse}}

instance moduleSpecGlobalSections_additive :
    (moduleSpecΓFunctor (R := ring)).Additive where
  map_add := by intros; rfl

theorem quasicoherentGlobalSections_epi
    {first second : (Spec ring).Modules}
    [first.IsQuasicoherent] [second.IsQuasicoherent]
    (coefficient_map : first ⟶ second) [Epi coefficient_map] :
    Epi (moduleSpecΓFunctor.map coefficient_map) := by
  letI : Epi (first.fromTildeΓ ≫ coefficient_map) := inferInstance
  have naturality := Scheme.Modules.fromTildeΓNatTrans.naturality coefficient_map
  change (tilde.functor ring).map (moduleSpecΓFunctor.map coefficient_map) ≫
    second.fromTildeΓ = first.fromTildeΓ ≫ coefficient_map at naturality
  letI : Epi ((tilde.functor ring).map (moduleSpecΓFunctor.map coefficient_map) ≫
      second.fromTildeΓ) := by
    rw [naturality]
    infer_instance
  have image_epi : Epi ((tilde.functor ring).map
      (moduleSpecΓFunctor.map coefficient_map)) :=
    (epi_comp_iff_of_isIso _ second.fromTildeΓ).mp inferInstance
  exact (tilde.functor ring).epi_of_epi_map image_epi

def sectionRestriction (coefficient : (Spec ring).Modules)
    {larger smaller : (Spec ring).Opens} (inclusion : smaller ⟶ larger) :
    Γ(coefficient, larger) →ₗ[ring] Γ(coefficient, smaller) :=
  ((modulesSpecToSheaf.obj coefficient).obj.map inclusion.op).hom

def basicSectionRestriction (coefficient : (Spec ring).Modules) (element : ring) :
    Γ(coefficient, ⊤) →ₗ[ring] Γ(coefficient, PrimeSpectrum.basicOpen element) := by
  exact sectionRestriction coefficient
    (homOfLE (show PrimeSpectrum.basicOpen element ≤ (⊤ : (Spec ring).Opens) from le_top))

theorem sectionRestriction_comp_top (coefficient : (Spec ring).Modules)
    {larger smaller : (Spec ring).Opens} (inclusion : smaller ⟶ larger) :
    (sectionRestriction coefficient inclusion).comp
      (sectionRestriction coefficient larger.leTop) =
      sectionRestriction coefficient smaller.leTop := by
  rw [sectionRestriction, sectionRestriction, sectionRestriction,
    ← ModuleCat.hom_comp, ← Functor.map_comp]
  rfl

theorem sectionRestriction_comp (coefficient : (Spec ring).Modules)
    {larger middle smaller : (Spec ring).Opens}
    (first_inclusion : middle ⟶ larger) (second_inclusion : smaller ⟶ middle) :
    (sectionRestriction coefficient second_inclusion).comp
      (sectionRestriction coefficient first_inclusion) =
      sectionRestriction coefficient (second_inclusion ≫ first_inclusion) := by
  rw [sectionRestriction, sectionRestriction, sectionRestriction,
    ← ModuleCat.hom_comp, ← Functor.map_comp]
  rfl

instance basicSectionRestriction_isLocalized (coefficient : (Spec ring).Modules)
    [coefficient.IsQuasicoherent] (element : ring) :
    IsLocalizedModule.Away element (basicSectionRestriction coefficient element) :=
  ((isIso_fromTildeΓ_iff_isLocalizing coefficient).mp inferInstance) element

end

end BondalThomsen.AffineQuasicoherentCohomologyVanishing
