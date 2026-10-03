module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Representation
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.TensorProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TensorProduct TopologicalSpace

namespace TauCeti
namespace AlgebraicGeometry
namespace Scheme.CartierDivisor

universe u

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

section TensorProduct

variable (D E : CartierDivisor X)

@[simp]
theorem toLineBundleClass_add :
    (D + E).toLineBundleClass = D.toLineBundleClass * E.toLineBundleClass := by
  have h (F : CartierDivisor X) :
      F.toLineBundleClass = LineBundleClass.mk F.toInvertibleSheaf := by
    apply toLineBundleClass_eq_mk_iff.mpr
    simpa only [toInvertibleSheaf_obj] using
      (⟨Iso.refl _⟩ : Nonempty (F.sheaf ≅ F.sheaf))
  rw [h (D + E), h D, h E, ← LineBundleClass.mk_tensorProduct,
    LineBundleClass.mk_eq_mk_iff]
  refine ⟨?_⟩
  simp only [toInvertibleSheaf_obj, InvertibleSheaf.tensorProduct_obj]
  exact (tensorProductSheafIso D E).symm

theorem isUnit_toLineBundleClass : IsUnit D.toLineBundleClass :=
  ⟨⟨D.toLineBundleClass, (-D).toLineBundleClass,
    by rw [← toLineBundleClass_add, add_neg_cancel, toLineBundleClass_zero],
    by rw [← toLineBundleClass_add, neg_add_cancel, toLineBundleClass_zero]⟩, rfl⟩

end TensorProduct

end
end CartierDivisor
end Scheme

namespace LineBundleClass

universe u

variable {X : Scheme.{u}} [IsIntegral X]

theorem isUnit (a : LineBundleClass X) : IsUnit a := by
  obtain ⟨D, rfl⟩ := Scheme.CartierDivisor.toLineBundleClass_surjective a
  exact Scheme.CartierDivisor.isUnit_toLineBundleClass D

noncomputable instance : CommGroup (LineBundleClass X) :=
  commGroupOfIsUnit isUnit

end LineBundleClass

namespace Scheme.CartierDivisor

universe u

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable def toLineBundleClassHom : CartierDivisor X →+ Additive (LineBundleClass X) where
  toFun D := Additive.ofMul D.toLineBundleClass
  map_zero' := congrArg Additive.ofMul toLineBundleClass_zero
  map_add' D E := congrArg Additive.ofMul (toLineBundleClass_add D E)

end Scheme.CartierDivisor

end AlgebraicGeometry
end TauCeti
