module

public import BondalThomsen.DeepFan.Theorems
public import BondalThomsen.Fan.Representations
public import BondalThomsen.Matroid.TUWalkCycleBridge
public import BondalThomsen.Rarity.TreeEncoding
public import BondalThomsen.Rarity.AsymptoticRarity
public import BondalThomsen.Rarity.FamilyParameters

@[expose] public section

namespace BondalThomsen

open Module

theorem card_le_two_pow_of_tu_matroid_model
    {Row Label Classes : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Label] [DecidableEq Label] [Fintype Classes]
    (reference : Matrix Row Label ℤ) (representative : Classes → Matrix Row Label ℤ)
    (reference_tu : reference.IsTotallyUnimodular)
    (representative_tu : ∀ configuration, (representative configuration).IsTotallyUnimodular)
    (reference_rank : (reference.map (Int.castRingHom ℚ)).rank = Fintype.card Row)
    (matching : ∀ configuration,
      rayMatroid (Field := ℚ) (fun label row => (reference row label : ℚ)) =
        rayMatroid (Field := ℚ) (fun label row => (representative configuration row label : ℚ)))
    (rigidity : ∀ first second (operation : (Matrix Row Row ℤ)ˣ),
      representative second = (operation : Matrix Row Row ℤ) * representative first →
        first = second) : Fintype.card Classes ≤ 2 ^ Fintype.card Label := by
  classical
  have equivalence := fun configuration => totallyUnimodular_arbitrary_rank_integral_equivalence
    reference (representative configuration) reference_tu (representative_tu configuration)
    reference_rank (matching configuration)
  choose operations signs signed equality using equivalence
  let encode : Classes → Label → Bool :=
    fun configuration label => decide (signs configuration label = 1)
  have injective : Function.Injective encode := by
    intro first second same_code
    have same_signs : signs first = signs second := by
      funext label
      have same_entry := congrFun same_code label
      rcases signed first label with positive | negative <;>
        rcases signed second label with positive | negative <;>
        simp_all [encode]
    apply rigidity first second (operations second * (operations first)⁻¹)
    rw [equality first, equality second]
    simp [← Matrix.mul_assoc, same_signs]
  have bound := Fintype.card_le_of_injective encode injective
  simpa only [Fintype.card_fun, Fintype.card_bool] using bound

end BondalThomsen
