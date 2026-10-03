module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Closure
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Associator
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Basic
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.LineBundle.Class
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.Sheaf
public import Challenge.Defs.Ports.TauCeti.CategoryTheory.Sites.Units
public import Challenge.Defs.Ports.TauCeti.CategoryTheory.Skeletal

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace TauCeti
namespace AlgebraicGeometry
universe u
noncomputable section
namespace Scheme.CartierDivisor
open _root_.AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} [SheafOfModules.isInvertible X M]
  {U : X.Opens} {e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U}
  {hU : Dense (U : Set X)} {D : CartierDivisor X}
variable (D) in

def toLineBundleClass : LineBundleClass X :=
  LineBundleClass.mk D.toInvertibleSheaf

@[simp]
lemma toLineBundleClass_principalCartierDivisor (f : X.functionFieldˣ) :
    (principalCartierDivisor X f).toLineBundleClass = 1 :=
  sorry

@[simp]
lemma toLineBundleClass_zero : (0 : CartierDivisor X).toLineBundleClass = 1 :=
  sorry

end Scheme.CartierDivisor
end
end AlgebraicGeometry
end TauCeti
end
