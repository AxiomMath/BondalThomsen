module

public import BondalThomsen.Rarity.Counting

@[expose] public section

namespace BondalThomsen

theorem finite_class_range_of_finite_code_range
    {Index Class Code : Type*} (classify : Index → Class) (code : Index → Code)
    (finiteCodes : (Set.range code).Finite)
    (determines : ∀ first second, code first = code second → classify first = classify second) :
    (Set.range classify).Finite ∧ Nat.card ↥(Set.range classify) ≤ Nat.card ↥(Set.range code) := by
  classical
  let := finiteCodes.fintype
  choose representative representativeEquality using
    (fun object : Set.range classify => object.property)
  let encode : Set.range classify → Set.range code := fun object =>
    ⟨code (representative object), representative object, rfl⟩
  have injective : Function.Injective encode := by
    intro first second equality
    apply Subtype.ext
    rw [← representativeEquality first, ← representativeEquality second]
    exact determines _ _ (congrArg Subtype.val equality)
  let := Finite.of_injective encode injective
  exact ⟨Set.toFinite _, Nat.card_le_card_of_injective encode injective⟩

end BondalThomsen
