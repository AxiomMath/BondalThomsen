module

public import BondalThomsen.Toric.Frobenius.FrobeniusFinite
public import BondalThomsen.Toric.Frobenius.MultiplicationFiniteLocallyFree
public import BondalThomsen.Derived.SheafExtCohomologyDimensionShift
public import BondalThomsen.Toric.Frobenius.FrobeniusCohomologyAssembly

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.ToricMultiplicationCohomologyTransport

universe schemeUniverse

noncomputable section

variable {Source Target : Scheme.{schemeUniverse}}

def pushforwardGlobalSectionsEquiv (morphism : Source ⟶ Target) (coefficient : Source.Modules) :
    Γ((Scheme.Modules.pushforward morphism).obj coefficient, ⊤) ≃+ Γ(coefficient, ⊤) :=
  (coefficient.presheaf.mapIso
    (eqToIso (show morphism ⁻¹ᵁ (⊤ : Target.Opens) = ⊤ from by ext; simp)).op).symm
      |>.addCommGroupIsoToAddEquiv

def pushforwardCohomologyZeroEquiv (morphism : Source ⟶ Target) (coefficient : Source.Modules) :
    Cohomology ((Scheme.Modules.pushforward morphism).obj coefficient) 0 ≃+
      Cohomology coefficient 0 :=
  (cohomologyZeroEquiv _).trans
    ((pushforwardGlobalSectionsEquiv morphism coefficient).trans (cohomologyZeroEquiv _).symm)

theorem pushforwardCohomologyZeroEquiv_naturality (morphism : Source ⟶ Target)
    {first second : Source.Modules} (coefficient_map : first ⟶ second)
    (element : Cohomology ((Scheme.Modules.pushforward morphism).obj first) 0) :
    pushforwardCohomologyZeroEquiv morphism second
      (cohomologyMap ((Scheme.Modules.pushforward morphism).map coefficient_map) 0 element) =
      cohomologyMap coefficient_map 0
        (pushforwardCohomologyZeroEquiv morphism first element) := by
  apply (cohomologyZeroEquiv second).injective
  simp only [pushforwardCohomologyZeroEquiv, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, cohomologyZeroEquiv_cohomologyMap]
  change pushforwardGlobalSectionsEquiv morphism second
      (((Scheme.Modules.pushforward morphism).map coefficient_map).app ⊤
        (cohomologyZeroEquiv _ element)) =
    coefficient_map.app ⊤
      (pushforwardGlobalSectionsEquiv morphism first (cohomologyZeroEquiv _ element))
  exact congrArg (fun map => map
    (cohomologyZeroEquiv ((Scheme.Modules.pushforward morphism).obj first) element))
    (coefficient_map.mapPresheaf.naturality
      (eqToHom (show ⊤ = morphism ⁻¹ᵁ (⊤ : Target.Opens) from by ext; simp)).op).symm

instance pushforward_isFlasque (morphism : Source ⟶ Target) (coefficient : Source.Modules)
    [coefficient.presheaf.IsFlasque] :
    ((Scheme.Modules.pushforward morphism).obj coefficient).presheaf.IsFlasque where
  epi {first_open second_open} restriction := by
    change Epi (coefficient.presheaf.map
      ((TopologicalSpace.Opens.map morphism.base).map restriction.unop).op)
    infer_instance

theorem pushforward_shortExact_of_epi (morphism : Source ⟶ Target)
    {sequence : ShortComplex Source.Modules} (exact_sequence : sequence.ShortExact)
    [Epi ((Scheme.Modules.pushforward morphism).map sequence.g)] :
    (sequence.map (Scheme.Modules.pushforward morphism)).ShortExact := by
  letI : Mono sequence.f := exact_sequence.mono_f
  have exactness := exact_sequence.exact.map_of_mono_of_preservesKernel
    (Scheme.Modules.pushforward morphism) (inferInstance : Mono sequence.f)
      (inferInstance : PreservesLimit (parallelPair sequence.g 0)
        (Scheme.Modules.pushforward morphism))
  exact ShortComplex.ShortExact.mk' exactness
    (inferInstance : Mono ((Scheme.Modules.pushforward morphism).map sequence.f))
    (inferInstance : Epi ((Scheme.Modules.pushforward morphism).map sequence.g))

end

end BondalThomsen.ToricMultiplicationCohomologyTransport

