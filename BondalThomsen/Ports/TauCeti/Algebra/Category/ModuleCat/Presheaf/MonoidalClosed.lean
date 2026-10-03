module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace PresheafOfModules

variable {C : Type u} [SmallCategory C] (R₀ : Cᵒᵖ ⥤ CommRingCat.{u})

instance monoidalClosed : MonoidalClosed (PresheafOfModules.{u} (R₀ ⋙ forget₂ _ RingCat)) where
  closed M :=
    letI := isLeftAdjoint_of_preservesColimits_of_isSeparating.{u}
      (_root_.PresheafOfModules.freeYoneda.isSeparating (R₀ ⋙ forget₂ _ RingCat)) (tensorLeft M)
    { rightAdj := (tensorLeft M).rightAdjoint
      adj := Adjunction.ofIsLeftAdjoint (tensorLeft M) }

end PresheafOfModules

end

end TauCeti
