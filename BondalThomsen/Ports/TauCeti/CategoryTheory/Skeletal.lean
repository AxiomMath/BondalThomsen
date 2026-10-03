module

public import Mathlib.CategoryTheory.Skeletal

@[expose] public section

namespace CategoryTheory

attribute [local instance] isIsomorphicSetoid

universe u v w

namespace ObjectProperty

theorem toSkeleton_eq_toSkeleton_iff_nonempty_iso {C : Type u} [Category.{v} C]
    (P : ObjectProperty C) {X Y : C} (hX : P X) (hY : P Y) :
    toSkeleton (⟨X, hX⟩ : P.FullSubcategory) = toSkeleton ⟨Y, hY⟩ ↔ Nonempty (X ≅ Y) := by
  rw [CategoryTheory.toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨P.ι.mapIso e⟩, fun ⟨e⟩ ↦ ⟨ObjectProperty.isoMk _ e⟩⟩

noncomputable def skeletonLift {C : Type u} [Category.{v} C] (P : ObjectProperty C)
    {α : Sort w} (f : P.FullSubcategory → α)
    (hf : ∀ X Y : P.FullSubcategory, Nonempty (X.obj ≅ Y.obj) → f X = f Y) :
    Skeleton P.FullSubcategory → α :=
  _root_.Quotient.lift f fun X Y e ↦ e.elim fun i ↦ hf X Y ⟨P.ι.mapIso i⟩

@[simp]
theorem skeletonLift_toSkeleton {C : Type u} [Category.{v} C] (P : ObjectProperty C)
    {α : Sort w} {f : P.FullSubcategory → α}
    {hf : ∀ X Y : P.FullSubcategory, Nonempty (X.obj ≅ Y.obj) → f X = f Y}
    (X : P.FullSubcategory) :
    P.skeletonLift f hf (toSkeleton X) = f X :=
  (rfl)

end ObjectProperty

end CategoryTheory
