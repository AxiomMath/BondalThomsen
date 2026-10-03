module

public import BondalThomsen.Rarity.Counting
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Matrix.Basic

@[expose] public section

namespace BondalThomsen

open Finset

theorem zero_column_translation_eq_zero {Row Column : Type*}
    (first second : Matrix Row Column ℤ)
    (first_nonnegative : ∀ row column, 0 ≤ first row column)
    (second_nonnegative : ∀ row column, 0 ≤ second row column)
    (first_zero : ∃ column, ∀ row, first row column = 0)
    (second_zero : ∃ column, ∀ row, second row column = 0)
    (rows : Equiv.Perm Row) (columns : Equiv.Perm Column) (translation : Row → ℤ)
    (matching : ∀ row column,
      second row column = first (rows row) (columns column) + translation row) :
    translation = 0 := by
  obtain ⟨first_column, first_column_zero⟩ := first_zero
  obtain ⟨second_column, second_column_zero⟩ := second_zero
  funext row
  have upper := matching row second_column
  rw [second_column_zero] at upper
  have lower := matching row (columns.symm first_column)
  rw [columns.apply_symm_apply, first_column_zero, zero_add] at lower
  have lower_nonnegative := second_nonnegative row (columns.symm first_column)
  have upper_nonnegative := first_nonnegative (rows row) (columns second_column)
  change translation row = 0
  linarith

def augmentedColumnMatrix {rows columns ones : ℕ}
    (matrix : FixedWeightMatrix rows columns ones) :
    Matrix (Fin rows) (Option (Fin columns)) ℤ :=
  fun row column => column.elim 0 (fun index => if index ∈ (matrix row).val then 1 else 0)

@[simp] theorem augmentedColumnMatrix_none {rows columns ones : ℕ}
    (matrix : FixedWeightMatrix rows columns ones) (row : Fin rows) :
    augmentedColumnMatrix matrix row none = 0 := rfl

theorem augmentedColumnMatrix_nonnegative {rows columns ones : ℕ}
    (matrix : FixedWeightMatrix rows columns ones) (row : Fin rows)
    (column : Option (Fin columns)) : 0 ≤ augmentedColumnMatrix matrix row column := by
  cases column with
  | none => simp
  | some index => simp only [augmentedColumnMatrix, Option.elim_some]; split <;> norm_num

theorem augmentedColumnMatrix_injective {rows columns ones : ℕ} :
    Function.Injective (augmentedColumnMatrix (rows := rows) (columns := columns)
      (ones := ones)) := by
  intro first second matching
  funext row
  apply Subtype.ext
  ext column
  have entry := congrFun (congrFun matching row) (some column)
  simp only [augmentedColumnMatrix, Option.elim_some] at entry
  by_cases first_mem : column ∈ (first row).val <;>
    by_cases second_mem : column ∈ (second row).val <;> simp_all

def AugmentedPermutationEquivalent {rows columns ones : ℕ}
    (first second : FixedWeightMatrix rows columns ones) : Prop :=
  ∃ row_permutation : Equiv.Perm (Fin rows),
    ∃ column_permutation : Equiv.Perm (Option (Fin columns)),
      augmentedColumnMatrix second =
        (augmentedColumnMatrix first).submatrix row_permutation column_permutation

theorem augmentedPermutationEquivalent_card_le {rows columns ones : ℕ}
    (first : FixedWeightMatrix rows columns ones) :
    Nat.card {second // AugmentedPermutationEquivalent first second} ≤
      rows.factorial * (columns + 1).factorial := by
  classical
  let witnesses (second : {second // AugmentedPermutationEquivalent first second}) :
      Equiv.Perm (Fin rows) × Equiv.Perm (Option (Fin columns)) :=
    ⟨Classical.choose second.property,
      Classical.choose (Classical.choose_spec second.property)⟩
  have witness_eq (second : {second // AugmentedPermutationEquivalent first second}) :
      augmentedColumnMatrix second.val = (augmentedColumnMatrix first).submatrix
        (witnesses second).1 (witnesses second).2 :=
    Classical.choose_spec (Classical.choose_spec second.property)
  have injective : Function.Injective witnesses := by
    intro second third matching
    apply Subtype.ext
    apply augmentedColumnMatrix_injective
    rw [witness_eq second, witness_eq third, matching]
  have bound := Nat.card_le_card_of_injective witnesses injective
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_option, Fintype.card_fin] using bound

theorem fixedWeightMatrix_fiber_bound_of_augmented_rigidity
    {rows columns ones : ℕ} {Classes : Type*} [DecidableEq Classes]
    (classify : FixedWeightMatrix rows columns ones → Classes)
    (rigidity : ∀ first second, classify first = classify second →
      AugmentedPermutationEquivalent first second) (target : Classes) :
    (univ.filter (fun matrix => classify matrix = target)).card ≤
      rows.factorial * (columns + 1).factorial := by
  classical
  let fiber := univ.filter (fun matrix => classify matrix = target)
  by_cases nonempty : fiber.Nonempty
  · obtain ⟨first, first_mem⟩ := nonempty
    have first_eq : classify first = target := (mem_filter.mp first_mem).2
    let injection : fiber → {second // AugmentedPermutationEquivalent first second} :=
      fun second => ⟨second.val, rigidity first second.val
        (first_eq.trans ((mem_filter.mp second.property).2).symm)⟩
    have injective : Function.Injective injection := by
      intro second third matching
      apply Subtype.ext
      exact congrArg (fun matrix : {second // AugmentedPermutationEquivalent first second} =>
        matrix.val) matching
    have bound := Nat.card_le_card_of_injective injection injective
    have fiber_card : Nat.card fiber = fiber.card := by simp [Nat.card_eq_fintype_card]
    rw [fiber_card] at bound
    exact bound.trans (augmentedPermutationEquivalent_card_le first)
  · have empty : fiber = ∅ := not_nonempty_iff_eq_empty.mp nonempty
    change fiber.card ≤ _
    simp [empty]

end BondalThomsen
