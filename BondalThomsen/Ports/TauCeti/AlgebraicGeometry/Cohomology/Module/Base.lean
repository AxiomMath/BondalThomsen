module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Module.Basic

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
variable {M N : X.Modules}

instance (priority := 900) _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBaseModule
    (M : X.Modules) (i : ℕ) : Module R (Cohomology M i) :=
  Module.compHom (Cohomology M i) (baseRingToGlobalSections R X)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.base_smul_cohomology
    (M : X.Modules) (i : ℕ) (r : R) (x : Cohomology M i) :
    r • x = (baseRingToGlobalSections R X r) • x :=
  rfl

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
