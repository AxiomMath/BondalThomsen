module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality

@[expose] public section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace TauCeti
namespace AlgebraicGeometry
universe u
noncomputable section
namespace SheafOfModules
variable (X : Scheme.{u})
def LocalTrivializations.ofIsOpenCover {M : X.Modules} {ι : Type u} (W : ι → X.Opens)
    (hW : IsOpenCover W)
    (e : ∀ i, _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)) ≅ M.over (W i)) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} M :=
  { I := ι
    X := W
    coversTop := (Opens.coversTop_iff (X : Type u) W).mpr hW
    iso := fun i ↦ TauCeti.SheafOfModules.freePUnitIsoUnit
      (X.ringCatSheaf.over (W i)) ≪≫ e i }

abbrev isInvertible : ObjectProperty X.Modules :=
  TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf)

end SheafOfModules
variable {X : Scheme.{u}}
abbrev InvertibleSheaf (X : Scheme.{u}) : Type _ :=
  ObjectProperty.FullSubcategory (SheafOfModules.isInvertible X)

namespace InvertibleSheaf
instance (L : InvertibleSheaf X) : SheafOfModules.isInvertible X L.obj :=
  sorry

def free (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    InvertibleSheaf X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance⟩

def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  free X PUnit

@[simp]
lemma trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = SheafOfModules.free (R := X.ringCatSheaf) PUnit :=
  sorry

end InvertibleSheaf
end
end AlgebraicGeometry
namespace SheafOfModules.LocalTrivializations
universe u
variable {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U : X.Opens}
end SheafOfModules.LocalTrivializations
namespace AlgebraicGeometry.SheafOfModules
open _root_.AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}} {M : X.Modules}
end AlgebraicGeometry.SheafOfModules
end TauCeti
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory Opposite
universe u
noncomputable section
variable {X : Scheme.{u}}
end
end AlgebraicGeometry.Scheme.Modules
end
