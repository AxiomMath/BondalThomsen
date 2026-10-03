module

public import Mathlib.Order.Extension.Linear
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Relation
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

@[expose] public section

namespace BondalThomsen.OrderingObstruction

universe u v w

variable {Object : Type u}

theorem exists_monotone_numbering [Fintype Object]
    (relation : Object → Object → Prop) [IsPartialOrder Object relation] :
    ∃ numbering : Object ≃ Fin (Fintype.card Object),
      ∀ source target, relation source target → numbering source ≤ numbering target := by
  classical
  let : PartialOrder Object :=
    { le := relation
      le_refl := Std.Refl.refl
      le_trans := IsTrans.trans
      le_antisymm := Std.Antisymm.antisymm }
  let : Fintype (LinearExtension Object) := inferInstanceAs (Fintype Object)
  let positions := Fintype.orderIsoFinOfCardEq (LinearExtension Object) rfl
  refine ⟨positions.symm.toEquiv, ?_⟩
  intro source target related
  exact positions.symm.monotone (toLinearExtension.monotone related)

theorem not_relation_of_numbering_lt {Position : Type v} [Preorder Position]
    {relation : Object → Object → Prop} {numbering : Object → Position}
    (compatible : ∀ source target, relation source target →
      numbering source ≤ numbering target)
    {source target : Object} (backward : numbering target < numbering source) :
    ¬ relation source target := by
  intro related
  exact (not_le_of_gt backward) (compatible source target related)

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

theorem backwardVanishing_of_strong {Position : Type v} [Preorder Position]
    {nonvanishing : ℤ → Object → Object → Prop} {numbering : Object → Position}
    (compatible : ∀ source target, nonvanishing 0 source target →
      numbering source ≤ numbering target)
    (strong : IsStrongVanishing nonvanishing) :
    IsBackwardVanishing nonvanishing numbering := by
  intro source target backward degree
  by_cases degree_zero : degree = 0
  · subst degree
    exact not_relation_of_numbering_lt compatible backward
  · exact strong degree degree_zero source target

theorem strongExceptionalOrdering_of_compatible [Fintype Object]
    {exceptional : Object → Prop} {nonvanishing : ℤ → Object → Object → Prop}
    {numbering : Object ≃ Fin (Fintype.card Object)}
    (individual : ∀ object, exceptional object)
    (compatible : ∀ source target, nonvanishing 0 source target →
      numbering source ≤ numbering target)
    (strong : IsStrongVanishing nonvanishing) :
    IsStrongExceptionalOrdering exceptional nonvanishing numbering :=
  ⟨⟨individual, backwardVanishing_of_strong compatible strong⟩, strong⟩

theorem exists_strongExceptionalOrdering [Fintype Object]
    (exceptional : Object → Prop) (nonvanishing : ℤ → Object → Object → Prop)
    [IsPartialOrder Object (nonvanishing 0)]
    (individual : ∀ object, exceptional object)
    (strong : IsStrongVanishing nonvanishing) :
    ∃ numbering : Object ≃ Fin (Fintype.card Object),
      IsStrongExceptionalOrdering exceptional nonvanishing numbering := by
  obtain ⟨numbering, compatible⟩ := exists_monotone_numbering (nonvanishing 0)
  exact ⟨numbering, strongExceptionalOrdering_of_compatible individual compatible strong⟩

section Category

open CategoryTheory CategoryTheory.Limits

variable {Category : Type v} [CategoryTheory.Category.{w} Category]
    [HasZeroMorphisms Category]

def NonzeroHom (objects : Object → Category) (source target : Object) : Prop :=
  ∃ morphism : objects source ⟶ objects target, morphism ≠ 0

theorem nonzeroHom_isPartialOrder (objects : Object → Category)
    (identity_nonzero : ∀ object, 𝟙 (objects object) ≠ 0)
    (composition_nonzero : ∀ {source middle target : Object}
      (first : objects source ⟶ objects middle) (second : objects middle ⟶ objects target),
      first ≠ 0 → second ≠ 0 → first ≫ second ≠ 0)
    (endomorphism_iso : ∀ object (endomorphism : objects object ⟶ objects object),
      endomorphism ≠ 0 → IsIso endomorphism)
    (pairwise_nonisomorphic : ∀ source target,
      Nonempty (objects source ≅ objects target) → source = target) :
    IsPartialOrder Object (NonzeroHom objects) where
  refl := fun object => ⟨𝟙 (objects object), identity_nonzero object⟩
  trans := by
    rintro source middle target ⟨first, first_nonzero⟩ ⟨second, second_nonzero⟩
    exact ⟨first ≫ second, composition_nonzero first second first_nonzero second_nonzero⟩
  antisymm := by
    rintro source target ⟨forward, forward_nonzero⟩ ⟨backward, backward_nonzero⟩
    let : IsIso (forward ≫ backward) := endomorphism_iso source _
      (composition_nonzero forward backward forward_nonzero backward_nonzero)
    let : IsIso (backward ≫ forward) := endomorphism_iso target _
      (composition_nonzero backward forward backward_nonzero forward_nonzero)
    let : Mono forward := mono_of_mono forward backward
    let : IsSplitEpi forward := IsSplitEpi.mk'
      { section_ := inv (backward ≫ forward) ≫ backward
        id := by simp [CategoryTheory.Category.assoc] }
    let : IsIso forward := isIso_of_mono_of_isSplitEpi forward
    exact pairwise_nonisomorphic source target ⟨asIso forward⟩

end Category

end BondalThomsen.OrderingObstruction
