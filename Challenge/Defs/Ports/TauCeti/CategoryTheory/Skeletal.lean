module

public import Mathlib.CategoryTheory.Skeletal

@[expose] public section
namespace CategoryTheory
attribute [local instance] isIsomorphicSetoid
universe u v w
namespace ObjectProperty
noncomputable def skeletonLift {C : Type u} [Category.{v} C] (P : ObjectProperty C)
    {α : Sort w} (f : P.FullSubcategory → α)
    (hf : ∀ X Y : P.FullSubcategory, Nonempty (X.obj ≅ Y.obj) → f X = f Y) :
    Skeleton P.FullSubcategory → α :=
  _root_.Quotient.lift f fun X Y e ↦ e.elim fun i ↦ hf X Y ⟨P.ι.mapIso i⟩

end ObjectProperty
end CategoryTheory
end
