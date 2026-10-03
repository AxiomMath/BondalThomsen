module

public import BondalThomsen.Rarity.FiniteComponentTreeEncoding

@[expose] public section

namespace BondalThomsen

open Set

theorem componentTreeMatroid_iso_of_tree_eq {first second : BinaryTree TreeMark}
    (equality : first = second) (first_valid : ComponentTreeShape first)
    (second_valid : ComponentTreeShape second) :
    Nonempty (Matroid.Iso (componentTreeMatroid first first_valid)
      (componentTreeMatroid second second_valid)) := by
  subst second
  exact ⟨Matroid.Iso.refl _⟩

end BondalThomsen
