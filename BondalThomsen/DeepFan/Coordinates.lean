module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic

@[expose] public section

namespace BondalThomsen

open Finset

def DeepCoordinates {Index : Type*} [Fintype Index] (coordinates : Index → ℤ) : Prop :=
  ∑ index, max (coordinates index) 0 ≤ 1

theorem deepCoordinates_iff_toNat_sum {Index : Type*} [Fintype Index]
    (coordinates : Index → ℤ) :
    DeepCoordinates coordinates ↔ ∑ index, (coordinates index).toNat ≤ 1 := by
  have cast_sum : ((∑ index, (coordinates index).toNat : ℕ) : ℤ) =
      ∑ index, max (coordinates index) 0 := by
    simp
  unfold DeepCoordinates
  rw [← cast_sum]
  exact_mod_cast Iff.rfl

theorem DeepCoordinates.coordinate_le_one {Index : Type*} [Fintype Index]
    {coordinates : Index → ℤ} (deep : DeepCoordinates coordinates) (index : Index) :
    coordinates index ≤ 1 := by
  have bound : max (coordinates index) 0 ≤ ∑ other, max (coordinates other) 0 :=
    single_le_sum (fun other _ => le_max_right _ _) (mem_univ index)
  exact (le_max_left _ _).trans (bound.trans deep)

theorem DeepCoordinates.positive_eq_one {Index : Type*} [Fintype Index]
    {coordinates : Index → ℤ} (deep : DeepCoordinates coordinates) {index : Index}
    (positive : 0 < coordinates index) : coordinates index = 1 := by
  have bound := sum_le_one_iff.mp ((deepCoordinates_iff_toNat_sum coordinates).mp deep)
    index index (mem_univ _) (mem_univ _)
    (by omega : (coordinates index).toNat ≠ 0) (by omega : (coordinates index).toNat ≠ 0)
  have := bound.2
  omega

theorem DeepCoordinates.unique_positive {Index : Type*} [Fintype Index]
    {coordinates : Index → ℤ} (deep : DeepCoordinates coordinates) {first second : Index}
    (first_positive : 0 < coordinates first) (second_positive : 0 < coordinates second) :
    first = second := by
  exact (sum_le_one_iff.mp ((deepCoordinates_iff_toNat_sum coordinates).mp deep)
    first second (mem_univ _) (mem_univ _)
    (by omega) (by omega)).1

theorem deepCoordinates_iff {Index : Type*} [Fintype Index]
    (coordinates : Index → ℤ) :
    DeepCoordinates coordinates ↔
      (∀ index, coordinates index ≤ 1) ∧
      (∀ first second, 0 < coordinates first → 0 < coordinates second → first = second) := by
  classical
  constructor
  · intro deep
    exact ⟨deep.coordinate_le_one, fun _ _ => deep.unique_positive⟩
  · rintro ⟨bounded, unique⟩
    by_cases positive : ∃ index, 0 < coordinates index
    · obtain ⟨index, positive⟩ := positive
      have others : ∀ other, other ≠ index → max (coordinates other) 0 = 0 := by
        intro other distinct
        have nonpositive : coordinates other ≤ 0 := by
          by_contra contrary
          exact distinct (unique other index (by omega) positive)
        exact max_eq_right nonpositive
      unfold DeepCoordinates
      rw [sum_eq_single index (fun other _ distinct => others other distinct)
        (by simp)]
      exact max_le (bounded index) (by omega)
    · have nonpositive : ∀ index, coordinates index ≤ 0 := by
        intro index
        by_contra contrary
        exact positive ⟨index, by omega⟩
      simp [DeepCoordinates, max_eq_right (nonpositive _)]

theorem DeepCoordinates.sum_le_one {Index : Type*} [Fintype Index]
    {coordinates : Index → ℤ} (deep : DeepCoordinates coordinates) :
    ∑ index, coordinates index ≤ 1 :=
  (sum_le_sum (fun _ _ => le_max_left _ _)).trans deep

theorem DeepCoordinates.comp {Index Subindex : Type*} [Fintype Index] [Fintype Subindex]
    {coordinates : Index → ℤ} (deep : DeepCoordinates coordinates)
    (inclusion : Subindex → Index) (injective : Function.Injective inclusion) :
    DeepCoordinates (coordinates ∘ inclusion) := by
  apply (deepCoordinates_iff _).mpr
  exact ⟨fun index => deep.coordinate_le_one (inclusion index),
    fun first second first_positive second_positive =>
      injective (deep.unique_positive first_positive second_positive)⟩

theorem DeepCoordinates.eq_basis_vector_of_nonnegative {Index : Type*} [Fintype Index]
    [DecidableEq Index] {coordinates : Index → ℤ} (deep : DeepCoordinates coordinates)
    (nonnegative : ∀ index, 0 ≤ coordinates index) (nonzero : coordinates ≠ 0) :
    ∃ chosen, ∀ index, coordinates index = if index = chosen then 1 else 0 := by
  classical
  have positive : ∃ index, 0 < coordinates index := by
    by_contra none
    apply nonzero
    funext index
    have not_positive : ¬ 0 < coordinates index := fun positive => none ⟨index, positive⟩
    exact le_antisymm (le_of_not_gt not_positive) (nonnegative index)
  obtain ⟨chosen, chosen_positive⟩ := positive
  refine ⟨chosen, fun index => ?_⟩
  by_cases same : index = chosen
  · simp [same, deep.positive_eq_one chosen_positive]
  · have nonpositive : coordinates index ≤ 0 := by
      by_contra contrary
      exact same (deep.unique_positive (by omega) chosen_positive)
    simp [same, le_antisymm nonpositive (nonnegative index)]

theorem DeepCoordinates.eq_basis_vector_of_sum_eq_one {Index : Type*} [Fintype Index]
    [DecidableEq Index]
    {coordinates : Index → ℤ} (deep : DeepCoordinates coordinates)
    (sum_one : ∑ index, coordinates index = 1) :
    ∃ chosen, ∀ index, coordinates index = if index = chosen then 1 else 0 := by
  classical
  have positive : ∃ chosen, 0 < coordinates chosen := by
    by_contra contrary
    have nonpositive : ∀ index, coordinates index ≤ 0 := by
      intro index
      by_contra contrary_index
      exact contrary ⟨index, by omega⟩
    have bound : ∑ index, coordinates index ≤ 0 :=
      sum_nonpos (fun index _ => nonpositive index)
    omega
  obtain ⟨chosen, chosen_positive⟩ := positive
  have chosen_one := deep.positive_eq_one chosen_positive
  have nonnegative : ∀ index, 0 ≤ coordinates index := by
    have equality : ∑ index, coordinates index = ∑ index, max (coordinates index) 0 := by
      have bound := sum_le_sum (fun index (_ : index ∈ (univ : Finset Index)) =>
        le_max_left (coordinates index) 0)
      unfold DeepCoordinates at deep
      omega
    have each := (sum_eq_sum_iff_of_le
      (fun index (_ : index ∈ (univ : Finset Index)) =>
        le_max_left (coordinates index) 0)).mp equality
    intro index
    rw [each index (mem_univ index)]
    exact le_max_right _ _
  refine ⟨chosen, fun index => ?_⟩
  by_cases same : index = chosen
  · simp [same, chosen_one]
  · have nonpositive : coordinates index ≤ 0 := by
      by_contra contrary
      exact same (deep.unique_positive (by omega) chosen_positive)
    simp [same, le_antisymm nonpositive (nonnegative index)]

theorem deep_coordinate_trichotomy {Index : Type*} [Fintype Index]
    {coordinates adjacent : Index → ℤ} (deep : DeepCoordinates coordinates)
    (adjacent_deep : DeepCoordinates adjacent) (index : Index)
    (wall_coordinate : adjacent index = -coordinates index) :
    coordinates index = -1 ∨ coordinates index = 0 ∨ coordinates index = 1 := by
  have upper := deep.coordinate_le_one index
  have lower := adjacent_deep.coordinate_le_one index
  rw [wall_coordinate] at lower
  omega

end BondalThomsen
