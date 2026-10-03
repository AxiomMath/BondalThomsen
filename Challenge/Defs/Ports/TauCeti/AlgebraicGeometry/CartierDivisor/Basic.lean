module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import Challenge.Defs.Ports.TauCeti.CategoryTheory.Sites.Units

@[expose] public section
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite
namespace TauCeti
namespace AlgebraicGeometry
universe u
noncomputable section
namespace Scheme
variable (X : Scheme.{u}) [IsIntegral X]
noncomputable abbrev regularUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj X.sheaf

noncomputable abbrev rationalUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj
    (rationalFunctionsRing X)

def toRationalUnitSheaf : regularUnitSheaf X ⟶ rationalUnitSheaf X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).map
    (toRationalFunctionsRing X)

def cartierDivisorSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  cokernel (toRationalUnitSheaf X)

def toCartierDivisorSheaf : rationalUnitSheaf X ⟶ cartierDivisorSheaf X :=
  cokernel.π (toRationalUnitSheaf X)

abbrev CartierDivisor : Type u :=
  ((cartierDivisorSheaf X).obj.obj (op (⊤ : X.Opens)) : Type u)

local instance instNonemptyTopOpens (X : Scheme.{u}) [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  sorry

def rationalUnitSectionsEquiv (U : X.Opens) [Nonempty U] :
    Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ) ≃+
      Additive X.functionFieldˣ := by
  exact (Units.mapEquiv (rationalFunctionsRingEquiv U).toMulEquiv).toAdditive

noncomputable def regularUnitToFunctionField (U : X.Opens) [Nonempty U] :
    ((X.presheaf.obj (op U)) : Type u)ˣ →* X.functionFieldˣ := by
  exact Units.map (X.germToFunctionField U).hom.toMonoidHom

def rationalUnitClass (U : X.Opens) [Nonempty U] :
    Additive X.functionFieldˣ →+ ((cartierDivisorSheaf X).obj.obj (op U) : Type u) :=
  (((toCartierDivisorSheaf X).hom.app (op U)).hom).comp
    (rationalUnitSectionsEquiv X U).symm.toAddMonoidHom

def principalCartierDivisorAddHom : Additive X.functionFieldˣ →+ CartierDivisor X :=
  rationalUnitClass X ⊤

def principalCartierDivisor (f : X.functionFieldˣ) : CartierDivisor X :=
  principalCartierDivisorAddHom X (Additive.ofMul f)

end Scheme
end
end AlgebraicGeometry
end TauCeti
end
