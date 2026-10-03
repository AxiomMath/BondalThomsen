module

public import BondalThomsen.Cohomology.AffineQuasicoherentCohomologyVanishing
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.AffineQuasicoherentCohomologyVanishing

namespace BondalThomsen.AffineCechDerivedComparison

universe schemeUniverse

noncomputable section

variable {scheme : Scheme.{schemeUniverse}}

def cohomologyOnZeroEquiv (coefficient : scheme.Modules) (open_set : scheme.Opens) :
    cohomologyOn coefficient 0 open_set ≃+ Γ(coefficient, open_set) :=
  Abelian.Ext.addEquiv₀.trans
    (TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
      (Opens.grothendieckTopology scheme) open_set
      ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj coefficient))

theorem cohomologyOnZeroEquiv_restriction (coefficient : scheme.Modules)
    {smaller larger : scheme.Opens} (inclusion : smaller ≤ larger)
    (element : cohomologyOn coefficient 0 larger) :
    cohomologyOnZeroEquiv coefficient smaller
      (cohomologyOnRes coefficient 0 inclusion element) =
    coefficient.presheaf.map (homOfLE inclusion).op
      (cohomologyOnZeroEquiv coefficient larger element) := by
  obtain ⟨section_map, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective element
  change cohomologyOnZeroEquiv coefficient smaller
    ((Abelian.Ext.mk₀
      ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
        (Opens.grothendieckTopology scheme)).map (homOfLE inclusion))).comp
      (Abelian.Ext.mk₀ section_map) (zero_add 0)) = _
  rw [Abelian.Ext.mk₀_comp_mk₀]
  simp only [cohomologyOnZeroEquiv, AddEquiv.trans_apply,
    ← Abelian.Ext.addEquiv₀_symm_apply]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  change TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
    (Opens.grothendieckTopology scheme) smaller _
    ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
      (Opens.grothendieckTopology scheme)).map (homOfLE inclusion) ≫ section_map) =
    coefficient.presheaf.map (homOfLE inclusion).op
      (TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
        (Opens.grothendieckTopology scheme) larger _ section_map)
  exact TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv_naturality_left
    (Opens.grothendieckTopology scheme) (homOfLE inclusion) _ section_map

end

end BondalThomsen.AffineCechDerivedComparison
