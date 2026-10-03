module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Skeletal

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

@[simp]
theorem lift_mk {α : Sort v} {f : InvertibleSheaf X → α}
    {hf : ∀ L M, Nonempty (L.obj ≅ M.obj) → f L = f M} (L : InvertibleSheaf X) :
    lift f hf (mk L) = f L :=
  ObjectProperty.skeletonLift_toSkeleton _ L

@[simp]
lemma mk_eq_mk_iff {L K : InvertibleSheaf X} :
    mk L = mk K ↔ Nonempty (L.obj ≅ K.obj) := by
  exact (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso
    (SheafOfModules.isInvertible X) L.property K.property)

theorem mk_surjective : Function.Surjective (mk : InvertibleSheaf X → LineBundleClass X) :=
  fun a ↦ Quotient.inductionOn a fun L ↦ ⟨L, rfl⟩

noncomputable def tensorProduct (a b : LineBundleClass X) : LineBundleClass X :=
  Quotient.map₂ InvertibleSheaf.tensorProduct
    (fun _ _ hL _ _ hK ↦ InvertibleSheaf.isIsomorphic_tensorProduct hL hK) a b

noncomputable instance : Mul (LineBundleClass X) where
  mul := tensorProduct

@[simp]
lemma mk_tensorProduct (L K : InvertibleSheaf X) :
    mk (InvertibleSheaf.tensorProduct L K) = mk L * mk K :=
  (rfl)

noncomputable instance : One (LineBundleClass X) where
  one := mk (InvertibleSheaf.trivial X)

@[simp]
lemma mk_trivial : mk (InvertibleSheaf.trivial X) = (1 : LineBundleClass X) :=
  rfl

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
