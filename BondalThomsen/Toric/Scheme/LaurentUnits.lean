module

public import BondalThomsen.Fan.CompleteFanCharacters
public import BondalThomsen.Toric.Divisor.SupportClasses
public import Mathlib.Algebra.Group.UniqueProds.VectorSpace
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

@[expose] public section

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

open Finset

theorem groupAlgebra_support_card_eq_one_of_mul_eq_one
    {Coefficient Group : Type*} [Semiring Coefficient] [Nontrivial Coefficient]
    [NoZeroDivisors Coefficient] [_root_.Group Group] [TwoUniqueProds Group]
    (first second : MonoidAlgebra Coefficient Group) (product_one : first * second = 1) :
    first.coeff.support.card = 1 ∧ second.coeff.support.card = 1 := by
  classical
  have first_nonzero : first ≠ 0 := by
    intro zero
    simp [zero] at product_one
  have second_nonzero : second ≠ 0 := by
    intro zero
    simp [zero] at product_one
  have first_positive : 0 < first.coeff.support.card := by
    apply Finset.card_pos.mpr
    exact Finsupp.support_nonempty_iff.mpr (MonoidAlgebra.coeff_eq_zero.not.mpr first_nonzero)
  have second_positive : 0 < second.coeff.support.card := by
    apply Finset.card_pos.mpr
    exact Finsupp.support_nonempty_iff.mpr (MonoidAlgebra.coeff_eq_zero.not.mpr second_nonzero)
  have product_card_le : first.coeff.support.card * second.coeff.support.card ≤ 1 := by
    by_contra larger
    have large : 1 < first.coeff.support.card * second.coeff.support.card := by omega
    obtain ⟨first_pair, first_contains, second_pair, second_contains, distinct,
      first_unique, second_unique⟩ := TwoUniqueProds.uniqueMul_of_one_lt_card large
    have unique_product_one : ∀ pair : Group × Group,
        pair ∈ first.coeff.support ×ˢ second.coeff.support →
        UniqueMul first.coeff.support second.coeff.support pair.1 pair.2 →
        pair.1 * pair.2 = 1 := by
      intro pair contains unique
      obtain ⟨first_member, second_member⟩ := Finset.mem_product.mp contains
      have coefficient_nonzero : (first * second).coeff (pair.1 * pair.2) ≠ 0 := by
        rw [MonoidAlgebra.coeff_mul_mul_of_uniqueMul unique]
        exact mul_ne_zero (Finsupp.mem_support_iff.mp first_member)
          (Finsupp.mem_support_iff.mp second_member)
      rw [product_one] at coefficient_nonzero
      have member : pair.1 * pair.2 ∈ (1 : MonoidAlgebra Coefficient Group).coeff.support :=
        Finsupp.mem_support_iff.mpr coefficient_nonzero
      simpa only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
        Finsupp.support_single (1 : Group) (one_ne_zero : (1 : Coefficient) ≠ 0),
        Finset.mem_singleton] using member
    have first_product := unique_product_one first_pair first_contains first_unique
    have second_product := unique_product_one second_pair second_contains second_unique
    obtain ⟨second_first_member, second_second_member⟩ := Finset.mem_product.mp second_contains
    have same_pair := first_unique second_first_member second_second_member
      (second_product.trans first_product.symm)
    exact distinct (Prod.ext same_pair.1.symm same_pair.2.symm)
  constructor <;> nlinarith

theorem groupAlgebra_unit_eq_single
    {Coefficient Group : Type*} [Semiring Coefficient] [Nontrivial Coefficient]
    [NoZeroDivisors Coefficient] [_root_.Group Group] [TwoUniqueProds Group]
    (unit : (MonoidAlgebra Coefficient Group)ˣ) :
    ∃ exponent coefficient, coefficient ≠ 0 ∧
      (unit : MonoidAlgebra Coefficient Group) = MonoidAlgebra.single exponent coefficient := by
  obtain ⟨exponent, support_eq⟩ := Finset.card_eq_one.mp
    (groupAlgebra_support_card_eq_one_of_mul_eq_one unit.val unit.inv unit.val_inv).1
  obtain ⟨nonzero, coefficient_eq⟩ := Finsupp.support_eq_singleton.mp support_eq
  exact ⟨exponent, unit.val.coeff exponent, nonzero,
    MonoidAlgebra.coeff_injective (coefficient_eq.trans (MonoidAlgebra.coeff_single _ _).symm)⟩

end BondalThomsen

namespace TauCeti.Toric.Fan

open Multiplicative

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem character_twoUniqueProds (fan : Fan embedding) :
    TwoUniqueProds (Multiplicative (Lattice →+ ℤ)) := by
  let : UniqueSums (Lattice →+ ℤ) :=
    UniqueSums.of_injective_addHom fan.lattice.realCharacter.toAddHom
      fan.lattice.realCharacter_injective inferInstance
  exact UniqueProds.toTwoUniqueProds_of_group

theorem laurentUnit_eq_single (fan : Fan embedding) (unit : (fan.LaurentCharacterAlgebra 𝕜)ˣ) :
    ∃ character : Lattice →+ ℤ, ∃ coefficient : 𝕜, coefficient ≠ 0 ∧
      (unit : fan.LaurentCharacterAlgebra 𝕜) = MonoidAlgebra.single (ofAdd character) coefficient := by
  let := fan.character_twoUniqueProds
  obtain ⟨exponent, coefficient, nonzero, same⟩ := BondalThomsen.groupAlgebra_unit_eq_single unit
  exact ⟨toAdd exponent, coefficient, nonzero, same⟩

end TauCeti.Toric.Fan
