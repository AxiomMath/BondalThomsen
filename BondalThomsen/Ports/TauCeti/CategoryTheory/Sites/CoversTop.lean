module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.GrothendieckTopology.CoversTop

variable {C : Type u} [Category.{v} C]

structure CommonRefinement (J : GrothendieckTopology C) {I₁ I₂ : Type*}
    (X₁ : I₁ → C) (X₂ : I₂ → C) where

  I : Type u

  X : I → C

  leftIndex : I → I₁

  left : ∀ i, X i ⟶ X₁ (leftIndex i)

  rightIndex : I → I₂

  right : ∀ i, X i ⟶ X₂ (rightIndex i)

  coversTop : J.CoversTop X

noncomputable def commonRefinement {I₁ I₂ : Type*} {X₁ : I₁ → C} {X₂ : I₂ → C}
    {J : GrothendieckTopology C} (h₁ : J.CoversTop X₁) (h₂ : J.CoversTop X₂) :
    CommonRefinement J X₁ X₂ := by
  let I := {W : C // (∃ i, Nonempty (W ⟶ X₁ i)) ∧ (∃ j, Nonempty (W ⟶ X₂ j))}
  let leftIndex : I → I₁ := fun w => w.2.1.choose
  let left : ∀ w : I, w.1 ⟶ X₁ (leftIndex w) :=
    fun w => w.2.1.choose_spec.some
  let rightIndex : I → I₂ := fun w => w.2.2.choose
  let right : ∀ w : I, w.1 ⟶ X₂ (rightIndex w) :=
    fun w => w.2.2.choose_spec.some
  exact
    { I := I
      X := Subtype.val
      leftIndex := leftIndex
      left := left
      rightIndex := rightIndex
      right := right
      coversTop := by
        intro A
        refine J.superset_covering ?_ (J.intersection_covering (h₁ A) (h₂ A))
        rintro Z f ⟨⟨i, ⟨a⟩⟩, ⟨j, ⟨b⟩⟩⟩
        exact ⟨⟨Z, ⟨⟨i, ⟨a⟩⟩, ⟨j, ⟨b⟩⟩⟩⟩, ⟨𝟙 Z⟩⟩ }

end CategoryTheory.GrothendieckTopology.CoversTop
