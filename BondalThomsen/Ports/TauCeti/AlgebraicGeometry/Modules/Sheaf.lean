module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness
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

def toSheaf : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  _root_.SheafOfModules.toSheaf X.ringCatSheaf

instance : (toSheaf X).Additive :=
  inferInstanceAs (_root_.SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance : PreservesFiniteLimits (toSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (_root_.SheafOfModules.toSheaf X.ringCatSheaf))

instance : PreservesFiniteColimits (toSheaf X) :=
  inferInstanceAs (PreservesFiniteColimits (_root_.SheafOfModules.toSheaf X.ringCatSheaf))

variable {X}

theorem shortExact_map_toSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toSheaf X)).ShortExact :=
  hS.map_of_exact _

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
