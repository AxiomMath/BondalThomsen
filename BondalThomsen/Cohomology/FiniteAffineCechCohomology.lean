module

public import BondalThomsen.Cohomology.FiniteAffineCoverQuasicoherentExtensions
public import BondalThomsen.Cohomology.AffineCechDerivedComparison

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.AffineCechDerivedComparison
open BondalThomsen.FiniteAffineCoverQuasicoherentExtensions
open BondalThomsen.QuasicoherentFlasqueTowerConstruction

namespace BondalThomsen.FiniteAffineCechCohomology

universe u

noncomputable section

variable {scheme : Scheme.{u}}

theorem affineOpenSections_surjective {first second : scheme.Modules}
    [first.IsQuasicoherent] [second.IsQuasicoherent]
    (coefficient_map : first ⟶ second) [Epi coefficient_map]
    (open_set : scheme.Opens) (affine : IsAffineOpen open_set) :
    Function.Surjective (coefficient_map.app open_set) := by
  let restriction := Scheme.Modules.restrictFunctor affine.fromSpec
  let local_map := restriction.map coefficient_map
  let : Epi (moduleSpecΓFunctor.map local_map) :=
    BondalThomsen.AffineQuasicoherentCohomologyVanishing.quasicoherentGlobalSections_epi local_map
  have local_surjectivity :=
    (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map local_map)).mp inferInstance
  have open_image : affine.fromSpec ''ᵁ (⊤ : (Spec Γ(scheme, open_set)).Opens) = open_set := by
    rw [Scheme.Hom.image_top_eq_opensRange, affine.opensRange_fromSpec]
  change Function.Surjective (coefficient_map.app (affine.fromSpec ''ᵁ ⊤)) at local_surjectivity
  rw [open_image] at local_surjectivity
  exact local_surjectivity

end

end BondalThomsen.FiniteAffineCechCohomology
