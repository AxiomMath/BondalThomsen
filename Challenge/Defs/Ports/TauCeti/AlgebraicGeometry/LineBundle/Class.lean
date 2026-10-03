module

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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
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
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Closure
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Associator
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.Sheaf
public import Challenge.Defs.Ports.TauCeti.CategoryTheory.Skeletal

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace TauCeti
namespace AlgebraicGeometry
universe u v
noncomputable section
def LineBundleClass (X : Scheme.{u}) : Type _ :=
  Skeleton (InvertibleSheaf X)

namespace LineBundleClass
variable {X : Scheme.{u}}
def mk (L : InvertibleSheaf X) : LineBundleClass X :=
  toSkeleton L

noncomputable def lift {α : Sort v} (f : InvertibleSheaf X → α)
    (hf : ∀ L M, Nonempty (L.obj ≅ M.obj) → f L = f M) : LineBundleClass X → α :=
  (SheafOfModules.isInvertible X).skeletonLift f hf

theorem mk_surjective : Function.Surjective (mk : InvertibleSheaf X → LineBundleClass X) :=
  sorry

noncomputable def tensorProduct (a b : LineBundleClass X) : LineBundleClass X :=
  Quotient.map₂ InvertibleSheaf.tensorProduct
    (fun _ _ hL _ _ hK ↦ InvertibleSheaf.isIsomorphic_tensorProduct hL hK) a b

noncomputable instance : Mul (LineBundleClass X) where
  mul := tensorProduct

noncomputable instance : One (LineBundleClass X) where
  one := mk (InvertibleSheaf.trivial X)

noncomputable instance : CommMonoid (LineBundleClass X) := by
  let mulComm : ∀ a b : LineBundleClass X, a * b = b * a := by
    intro a b
    induction a using Quotient.inductionOn with
    | _ L =>
      induction b using Quotient.inductionOn with
      | _ K => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorProductComm L K)
  let mulAssoc : ∀ a b c : LineBundleClass X, a * b * c = a * (b * c) := by
    intro a b c
    induction a using Quotient.inductionOn with
    | _ L =>
      induction b using Quotient.inductionOn with
      | _ K =>
        induction c using Quotient.inductionOn with
        | _ M => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorProductAssoc L K M)
  let oneMul : ∀ a : LineBundleClass X, 1 * a = a := by
    intro a
    induction a using Quotient.inductionOn with
    | _ L => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorTrivialLeftIso L)
  let mulOne : ∀ a : LineBundleClass X, a * 1 = a := by
    intro a
    induction a using Quotient.inductionOn with
    | _ L => exact congr_toSkeleton_of_iso (InvertibleSheaf.tensorTrivialRightIso L)
  exact
    { mul_assoc := mulAssoc
      one_mul := oneMul
      mul_one := mulOne
      mul_comm := mulComm }

end LineBundleClass
end
end AlgebraicGeometry
end TauCeti
end
