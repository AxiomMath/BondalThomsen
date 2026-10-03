module

public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

abbrev Cohomology (M : X.Modules) (i : ℕ) : Type u :=
  CategoryTheory.Sheaf.H.{u}
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) i

abbrev cohomologyFunctor (X : Scheme.{u}) (i : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  _root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i

instance (X : Scheme.{u}) (i : ℕ) : (cohomologyFunctor X i).Additive :=
  inferInstanceAs ((_root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i).Additive)

def cohomologyZeroEquiv (M : X.Modules) :
    Cohomology M 0 ≃+ Γ(M, ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop

lemma cohomologyZeroEquiv_naturality {M N : X.Modules} (f : M ⟶ N) (x : Cohomology M 0) :
    cohomologyZeroEquiv N ((cohomologyFunctor X 0).map f x) =
      f.app ⊤ (cohomologyZeroEquiv M x) :=
  (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) x).symm

section Opens

variable (M : X.Modules)

abbrev cohomologyOn (n : ℕ) (U : Opens X) : AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.H'.{u} ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n U

abbrev cohomologyOnRes (n : ℕ) {U V : Opens X} (h : U ≤ V) :
    cohomologyOn M n V ⟶ cohomologyOn M n U :=
  (CategoryTheory.Sheaf.cohomologyPresheaf.{u}
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n).map (homOfLE h).op

noncomputable abbrev cohomologyOnTopIso (n : ℕ) :
    cohomologyOn M n ⊤ ≅ AddCommGrpCat.of (Cohomology M n) :=
  ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheafObjIsoH
    n isTerminalTop

end Opens

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
