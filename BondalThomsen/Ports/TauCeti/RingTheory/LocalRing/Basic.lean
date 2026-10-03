module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

namespace TauCeti

theorem IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem {R : Type*} [Ring R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  have hsum : IsUnit (a + (1 - a)) := by simp
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hu | hu
  · exact Or.inr (hu.mul_left_cancel (by rw [ha, mul_one]))
  · refine Or.inl ?_
    have hidem : IsIdempotentElem (1 - a) := IsIdempotentElem.one_sub ha
    have hone : (1 : R) - a = 1 := hu.mul_left_cancel (by rw [hidem, mul_one])
    exact sub_eq_self.mp hone

instance IsLocalRing.isDedekindFiniteMonoid {R : Type*} [Ring R] [IsLocalRing R] :
    IsDedekindFiniteMonoid R where
  mul_eq_one_symm := by
    intro p q hpq
    have he : IsIdempotentElem (q * p) := by
      rw [IsIdempotentElem]
      calc
        (q * p) * (q * p) = q * (p * q) * p := by simp only [mul_assoc]
        _ = q * p := by rw [hpq, mul_one]
    rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem he with h0 | h1
    · have hp0 : p = 0 := by
        calc
          p = (p * q) * p := by rw [hpq, one_mul]
          _ = p * (q * p) := by rw [mul_assoc]
          _ = 0 := by rw [h0, mul_zero]
      simpa only [hp0, mul_zero, zero_mul] using hpq
    · exact h1

theorem IsLocalRing.of_ringEquiv {R S : Type*} [Semiring R] [Semiring S] [IsLocalRing R]
    (e : R ≃+* S) : IsLocalRing S := by
  have := e.symm.toEquiv.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add fun a b hab ↦ ?_
  have hsum : IsUnit (e.symm a + e.symm b) := by simpa using hab.map e.symm
  exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).imp (fun hu ↦ by simpa using hu.map e)
    fun hu ↦ by simpa using hu.map e

end TauCeti
