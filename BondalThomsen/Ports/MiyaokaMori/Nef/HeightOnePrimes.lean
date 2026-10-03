module

public import BondalThomsen.Ports.MiyaokaMori.Nef.FiniteFiberHeight

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Polynomial
open scoped Classical AlgebraicGeometry

universe u

noncomputable section

namespace Ideal

theorem finite_primesOver_and_height_of_adjoin_singleton {sourceRing targetRing : Type*} [CommRing sourceRing] [IsDomain sourceRing]
    [IsNoetherianRing sourceRing] [CommRing targetRing] [IsDomain targetRing] [IsNoetherianRing targetRing] [Algebra sourceRing targetRing]
    [FaithfulSMul sourceRing targetRing] (generator : targetRing) (hx : Algebra.adjoin sourceRing {generator} = ⊤) (halg : IsAlgebraic sourceRing generator)
    (intermediatePrime : Ideal sourceRing) [intermediatePrime.IsPrime] (h𝔮 : intermediatePrime.height = 1) :
    (intermediatePrime.primesOver targetRing).Finite ∧ ∀ upperPrime ∈ intermediatePrime.primesOver targetRing, upperPrime.height = 1 := by
  have hfin := finite_fiber_of_adjoin_singleton generator hx halg intermediatePrime h𝔮
  refine ⟨finite_primesOver_of_finite_fiber intermediatePrime, fun upperPrime ⟨hQ, hQ𝔮⟩ ↦ le_antisymm ?_ ?_⟩
  · exact h𝔮 ▸ height_le_of_liesOver_of_finite_fiber intermediatePrime upperPrime
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    have h1 : intermediatePrime = (⊥ : Ideal targetRing).under sourceRing := hQ𝔮.over
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective sourceRing targetRing)]
      at h1
    exact Ideal.ne_bot_of_height_eq_one h𝔮 h1

private theorem aux (baseRing : Type u) [CommRing baseRing] [IsDomain baseRing] [IsNoetherianRing baseRing] (basePrime : Ideal baseRing)
    [basePrime.IsPrime] (hp : basePrime.height = 1) (generatorBound : ℕ) :
    ∀ (extensionRing : Type u) [CommRing extensionRing] [IsDomain extensionRing] [Algebra baseRing extensionRing] [FaithfulSMul baseRing extensionRing]
      [Algebra.IsAlgebraic baseRing extensionRing] (generators : Finset extensionRing), generators.card ≤ generatorBound → Algebra.adjoin baseRing (generators : Set extensionRing) = ⊤ →
      (basePrime.primesOver extensionRing).Finite ∧ ∀ upperPrime ∈ basePrime.primesOver extensionRing, upperPrime.height = 1 := by
  induction generatorBound with
  | zero =>
    intro extensionRing _ _ _ _ _ generators hs hadj
    have hs0 : generators = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    have hB : IsNoetherianRing extensionRing :=
      Algebra.FiniteType.isNoetherianRing baseRing extensionRing (h := ⟨⟨generators, hadj⟩⟩)
    refine finite_primesOver_and_height_of_adjoin_singleton (1 : extensionRing) ?_
      (Algebra.IsAlgebraic.isAlgebraic _) basePrime hp
    rw [← hadj, hs0]
    simp
  | succ generatorBound ih =>
    intro extensionRing _ _ _ _ _ generators hs hadj
    have hB : IsNoetherianRing extensionRing :=
      Algebra.FiniteType.isNoetherianRing baseRing extensionRing (h := ⟨⟨generators, hadj⟩⟩)
    by_cases hs' : generators.card ≤ generatorBound
    · exact ih extensionRing generators hs' hadj
    obtain ⟨generator, hxs⟩ : generators.Nonempty := by
      rw [← Finset.card_pos]; omega
    classical
    set remainingGenerators := generators.erase generator with ht
    have hst : (generators : Set extensionRing) = (remainingGenerators : Set extensionRing) ∪ {generator} := by
      rw [ht, Finset.coe_erase]; simp [Set.insert_eq_of_mem (Finset.mem_coe.mpr hxs)]
    let sourceRing : Subalgebra baseRing extensionRing := Algebra.adjoin baseRing (remainingGenerators : Set extensionRing)
    let liftedGenerators : Finset sourceRing := remainingGenerators.attach.image fun otherElement ↦ ⟨otherElement.1, Algebra.subset_adjoin (Finset.mem_coe.mpr otherElement.2)⟩
    have ht' : (liftedGenerators : Set sourceRing) = ((↑) : sourceRing → extensionRing) ⁻¹' (remainingGenerators : Set extensionRing) := by
      ext ⟨otherElement, hy⟩
      simp [liftedGenerators]
    have hcard : liftedGenerators.card ≤ generatorBound := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_attach, ht, Finset.card_erase_of_mem hxs]; omega
    have hadjR : Algebra.adjoin baseRing (liftedGenerators : Set sourceRing) = ⊤ := by
      rw [ht']; exact Algebra.adjoin_adjoin_coe_preimage
    have hinjR : Function.Injective (algebraMap baseRing sourceRing) := fun element otherElement hab ↦
      FaithfulSMul.algebraMap_injective baseRing extensionRing (congrArg Subtype.val hab)
    have : FaithfulSMul baseRing sourceRing := (faithfulSMul_iff_algebraMap_injective baseRing sourceRing).mpr hinjR
    have : Algebra.IsAlgebraic baseRing sourceRing :=
      Algebra.IsAlgebraic.of_injective sourceRing.val Subtype.val_injective
    have hR : IsNoetherianRing sourceRing :=
      Algebra.FiniteType.isNoetherianRing baseRing sourceRing (h := ⟨⟨liftedGenerators, hadjR⟩⟩)
    obtain ⟨hfinR, hhtR⟩ := ih sourceRing liftedGenerators hcard hadjR
    have hxtop : Algebra.adjoin sourceRing {generator} = ⊤ := by
      have h1 := Algebra.adjoin_union_eq_adjoin_adjoin baseRing (remainingGenerators : Set extensionRing) {generator}
      rw [← hst, hadj] at h1
      refine top_unique fun otherElement _ ↦ ?_
      have : otherElement ∈ (Algebra.adjoin sourceRing {generator}).restrictScalars baseRing := h1 ▸ Algebra.mem_top
      exact this
    have halgx : IsAlgebraic sourceRing generator :=
      (Algebra.IsAlgebraic.isAlgebraic (R := baseRing) generator).extendScalars hinjR
    have key : ∀ intermediatePrime ∈ basePrime.primesOver sourceRing,
        (intermediatePrime.primesOver extensionRing).Finite ∧ ∀ upperPrime ∈ intermediatePrime.primesOver extensionRing, upperPrime.height = 1 := by
      intro intermediatePrime h𝔮
      have := h𝔮.1
      exact finite_primesOver_and_height_of_adjoin_singleton generator hxtop halgx intermediatePrime (hhtR intermediatePrime h𝔮)
    have hcover : ∀ upperPrime ∈ basePrime.primesOver extensionRing, upperPrime.under sourceRing ∈ basePrime.primesOver sourceRing ∧
        upperPrime ∈ (upperPrime.under sourceRing).primesOver extensionRing := by
      rintro upperPrime ⟨hQ, hQp⟩
      refine ⟨⟨inferInstance, ⟨?_⟩⟩, hQ, ⟨rfl⟩⟩
      rw [Ideal.under_under, ← hQp.over]
    refine ⟨?_, fun upperPrime hQ ↦ (key _ (hcover upperPrime hQ).1).2 upperPrime (hcover upperPrime hQ).2⟩
    refine (hfinR.biUnion fun intermediatePrime h𝔮 ↦ (key intermediatePrime h𝔮).1).subset fun upperPrime hQ ↦ ?_
    exact Set.mem_biUnion (hcover upperPrime hQ).1 (hcover upperPrime hQ).2

theorem finite_primesOver_and_height_eq_one {baseRing extensionRing : Type u} [CommRing baseRing] [CommRing extensionRing]
    [IsDomain baseRing] [IsDomain extensionRing] [IsNoetherianRing baseRing] [Algebra baseRing extensionRing] [FaithfulSMul baseRing extensionRing]
    [Algebra.FiniteType baseRing extensionRing] [Algebra.IsAlgebraic baseRing extensionRing] (basePrime : Ideal baseRing) [basePrime.IsPrime]
    (hp : basePrime.height = 1) :
    (basePrime.primesOver extensionRing).Finite ∧ ∀ upperPrime ∈ basePrime.primesOver extensionRing, upperPrime.height = 1 := by
  obtain ⟨generators, hs⟩ := (‹Algebra.FiniteType baseRing extensionRing›).out
  exact aux baseRing basePrime hp generators.card extensionRing generators le_rfl hs

end Ideal

end
