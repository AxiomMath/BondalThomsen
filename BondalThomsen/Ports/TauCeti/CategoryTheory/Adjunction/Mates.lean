module

public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

section Conjugate

namespace Adjunction

variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

theorem homEquiv_conjugateEquiv (α : L₂ ⟶ L₁) {c : C} {d : D} (a : L₁.obj c ⟶ d) :
    adj₁.homEquiv c d a ≫ (conjugateEquiv adj₁ adj₂ α).app d =
      adj₂.homEquiv c d (α.app c ≫ a) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv, Category.assoc, Category.assoc, NatTrans.naturality]

end Adjunction

end Conjugate

end CategoryTheory
