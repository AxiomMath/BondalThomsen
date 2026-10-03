module

public import BondalThomsen.Ports.Matroid.ProjectiveBound

@[expose] public section

namespace BondalThomsen.BinaryPointExhaustion

open Set Submodule

theorem card_nonzero_coordinates (dimension : ℕ) :
    Nat.card {vector : Fin dimension → ZMod 2 // vector ≠ 0} = 2 ^ dimension - 1 := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [ZMod.card]

theorem card_nonzero_three :
    Nat.card {vector : Fin 3 → ZMod 2 // vector ≠ 0} = 7 := by
  norm_num [card_nonzero_coordinates]

theorem exists_unique_missing_of_six {Index : Type*} (points : Index → Fin 3 → ZMod 2)
    (nonzero : ∀ index, points index ≠ 0) (injective : Function.Injective points)
    (cardinality : Nat.card Index = 6) :
    ∃! vector : Fin 3 → ZMod 2, vector ≠ 0 ∧ vector ∉ Set.range points := by
  classical
  let nonzero_vectors : Set (Fin 3 → ZMod 2) := {vector | vector ≠ 0}
  have contained : Set.range points ⊆ nonzero_vectors := by
    rintro vector ⟨index, rfl⟩
    exact nonzero index
  have range_card : (Set.range points).ncard = 6 := by
    change Nat.card (Set.range points) = 6
    rw [Nat.card_range_of_injective injective, cardinality]
  have nonzero_card : nonzero_vectors.ncard = 7 := card_nonzero_three
  have missing_card : (nonzero_vectors \ Set.range points).ncard = 1 := by
    rw [Set.ncard_sdiff' contained, nonzero_card, range_card]
  obtain ⟨missing, missing_eq⟩ := Set.ncard_eq_one.mp missing_card
  refine ⟨missing, ?_, ?_⟩
  · have member : missing ∈ nonzero_vectors \ Set.range points := by
      rw [missing_eq]
      exact Set.mem_singleton missing
    exact member
  · intro vector member
    exact Set.mem_singleton_iff.mp (missing_eq ▸ member)

end BondalThomsen.BinaryPointExhaustion

namespace Matroid

variable {Label Vector : Type*} [AddCommGroup Vector] [Module (ZMod 2) Vector]
    {matroid : Matroid Label} [matroid.Simple]

def Rep.binaryPoint (representation : matroid.Rep (ZMod 2) Vector) (element : matroid.E) :
    {vector : Vector // vector ≠ 0} :=
  ⟨representation element, (representation.ne_zero_iff_isNonloop element).mpr
    ((Simple.parallel_iff_eq element.property).mpr rfl).1⟩

theorem Rep.binaryPoint_injective (representation : matroid.Rep (ZMod 2) Vector) :
    Function.Injective representation.binaryPoint := by
  intro first second equality
  apply representation.projFun_injective
  exact congrArg (Projectivization.mk' (ZMod 2)) equality

end Matroid
