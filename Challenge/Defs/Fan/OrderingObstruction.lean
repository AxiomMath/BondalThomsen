module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Relation
public import Mathlib.Order.Extension.Linear

@[expose] public section
namespace BondalThomsen.OrderingObstruction
universe u v w
variable {Object : Type u}
def IsBackwardVanishing {Position : Type v} [LT Position]
    (nonvanishing : ℤ → Object → Object → Prop) (numbering : Object → Position) : Prop :=
  ∀ source target, numbering target < numbering source →
    ∀ degree, ¬ nonvanishing degree source target

def IsStrongVanishing (nonvanishing : ℤ → Object → Object → Prop) : Prop :=
  ∀ degree, degree ≠ 0 → ∀ source target, ¬ nonvanishing degree source target

def IsExceptionalOrdering [Fintype Object]
    (exceptional : Object → Prop) (nonvanishing : ℤ → Object → Object → Prop)
    (numbering : Object ≃ Fin (Fintype.card Object)) : Prop :=
  (∀ object, exceptional object) ∧ IsBackwardVanishing nonvanishing numbering

def IsStrongExceptionalOrdering [Fintype Object]
    (exceptional : Object → Prop) (nonvanishing : ℤ → Object → Object → Prop)
    (numbering : Object ≃ Fin (Fintype.card Object)) : Prop :=
  IsExceptionalOrdering exceptional nonvanishing numbering ∧ IsStrongVanishing nonvanishing

section Category
open CategoryTheory CategoryTheory.Limits
variable {Category : Type v} [CategoryTheory.Category.{w} Category]
    [HasZeroMorphisms Category]
end Category
end BondalThomsen.OrderingObstruction
end
