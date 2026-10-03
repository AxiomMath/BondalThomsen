module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

namespace TauCeti

open MonoidAlgebra

variable (R : Type*) [CommSemiring R] {M N : Type*} [CommMonoid M] [CommMonoid N]

theorem MonoidAlgebra.isLocalization_away_mapDomainRingHom (f : M →* N)
    (hf : Function.Injective f) (x : M) (hx : IsUnit (f x))
    (hsurj : ∀ y : N, ∃ n : ℕ, y * f x ^ n ∈ Set.range f) :
    letI := (mapDomainRingHom R f).toAlgebra
    IsLocalization.Away (single x (1 : R)) (MonoidAlgebra R N) := by
  let := (mapDomainRingHom R f).toAlgebra
  have halg : ∀ a : MonoidAlgebra R M,
      algebraMap (MonoidAlgebra R M) (MonoidAlgebra R N) a = mapDomain f a := fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, mapDomainRingHom_apply]
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [halg, mapDomain_single]
    exact hx.map (of R N)
  · intro s
    induction s using MonoidAlgebra.induction_on with
    | of y =>
      obtain ⟨n, z, hz⟩ := hsurj y
      refine ⟨n, single z 1, ?_⟩
      simp [halg, hz]
    | add s t hs ht =>
      obtain ⟨n, a, ha⟩ := hs
      obtain ⟨k, b, hb⟩ := ht
      refine ⟨n + k, a * single x 1 ^ k + b * single x 1 ^ n, ?_⟩
      simp only [map_add, map_mul, map_pow]
      rw [← ha, ← hb]
      ring
    | smul r s hs =>
      obtain ⟨n, a, ha⟩ := hs
      refine ⟨n, algebraMap R (MonoidAlgebra R M) r * a, ?_⟩
      have ha' : s * mapDomain f (single x 1) ^ n = mapDomain f a := by
        simpa only [halg] using ha
      simp only [Algebra.smul_def, halg]
      rw [mul_assoc, ha', mapDomain_mul]
      congr 1
      exact ((mapDomainAlgHom R R f).commutes r).symm
  · intro a b hab
    exact ⟨0, by rw [mapDomain_injective hf hab]⟩

end TauCeti
