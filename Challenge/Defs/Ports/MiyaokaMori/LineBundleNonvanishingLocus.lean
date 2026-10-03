module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Challenge.Defs.Ports.MiyaokaMori.ModuleSheafFrameStalk
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {X : AlgebraicGeometry.Scheme.{u}}
theorem isOpen_setOf_germ_notMem_maximalIdeal_smul (L : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] (s : Γ(L, ⊤)) :
    IsOpen {x : X | L.presheaf.germ ⊤ x trivial s ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x))} :=
  sorry

end AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry in

noncomputable def AlgebraicGeometry.Scheme.Modules.nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] (s : Γ(L, ⊤)) : X.Opens :=
  ⟨{x | TopCat.Presheaf.germ L.presheaf ⊤ x trivial s ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x))},
    AlgebraicGeometry.Scheme.Modules.isOpen_setOf_germ_notMem_maximalIdeal_smul L s⟩

namespace AlgebraicGeometry.Scheme.Modules
variable {X : AlgebraicGeometry.Scheme.{u}}
end AlgebraicGeometry.Scheme.Modules
end
end
