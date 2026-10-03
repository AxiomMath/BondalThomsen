module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section
open CategoryTheory Limits AlgebraicGeometry
namespace TauCeti
namespace AlgebraicGeometry
universe u
noncomputable section
namespace Scheme.Modules
variable (X : Scheme.{u})
def _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso (X : Scheme.{u})
    {M N : X.Modules} (e : @Iso (SheafOfModules X.ringCatSheaf) _ M N) : M ≅ N :=
  { hom := ⟨e.hom.val⟩
    inv := ⟨e.inv.val⟩
    hom_inv_id := by
      apply SheafOfModules.Hom.ext
      exact congrArg SheafOfModules.Hom.val e.hom_inv_id
    inv_hom_id := by
      apply SheafOfModules.Hom.ext
      exact congrArg SheafOfModules.Hom.val e.inv_hom_id }

variable {X}
end Scheme.Modules
end
end AlgebraicGeometry
end TauCeti
end
