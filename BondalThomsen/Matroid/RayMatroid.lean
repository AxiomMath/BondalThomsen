module

public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic

@[expose] public section

namespace BondalThomsen

open Set Submodule

noncomputable def vectorMatroid (Field Vector : Type*) [_root_.DivisionRing Field]
    [AddCommGroup Vector] [Module Field Vector] : Matroid Vector :=
  (IndepMatroid.ofFinitaryCardAugment
    (E := univ)
    (Indep := LinearIndepOn Field id)
    (indep_empty := linearIndepOn_empty Field id)
    (indep_subset := fun _ _ independent subset => independent.mono subset)
    (indep_aug := by
      intro smaller larger smaller_independent smaller_finite larger_independent larger_finite
        cardinality
      have not_contained : ¬ larger ⊆ span Field smaller := by
        rw [← span_le]
        intro contained
        have := smaller_finite.fintype
        have := larger_finite.fintype
        have : Module.Finite Field (span Field smaller) :=
          FiniteDimensional.span_of_finite Field smaller_finite
        apply cardinality.not_ge
        rw [ncard_eq_toFinset_card' larger, ncard_eq_toFinset_card' smaller,
          ← finrank_span_set_eq_card larger_independent,
          ← finrank_span_set_eq_card smaller_independent]
        exact Submodule.finrank_mono contained
      obtain ⟨added, member, not_span⟩ := not_subset.mp not_contained
      have not_member : added ∉ smaller := notMem_subset subset_span not_span
      refine ⟨added, member, not_member, ?_⟩
      simpa using smaller_independent.insert (by simpa using not_span))
    (indep_compact := linearIndepOn_of_finite)
    (subset_ground := fun _ _ => subset_univ _)).matroid

noncomputable def rayMatroid {Label Field Vector : Type*}
    [_root_.DivisionRing Field] [AddCommGroup Vector] [Module Field Vector]
    (vectors : Label → Vector) : Matroid Label :=
  (vectorMatroid Field Vector).comapOn univ vectors

@[simp] theorem rayMatroid_ground {Label Field Vector : Type*}
    [_root_.DivisionRing Field] [AddCommGroup Vector] [Module Field Vector]
    (vectors : Label → Vector) : (rayMatroid (Field := Field) vectors).E = univ := by
  simp [rayMatroid]

@[simp] theorem rayMatroid_indep_iff {Label Field Vector : Type*}
    [_root_.DivisionRing Field] [AddCommGroup Vector] [Module Field Vector]
    (vectors : Label → Vector) (labels : Set Label) :
    (rayMatroid (Field := Field) vectors).Indep labels ↔ LinearIndepOn Field vectors labels := by
  rw [rayMatroid, Matroid.comapOn_indep_iff]
  by_cases injective : Set.InjOn vectors labels
  · simp only [vectorMatroid, IndepMatroid.matroid_Indep,
      IndepMatroid.ofFinitaryCardAugment_indep, injective, subset_univ,
      and_true, ← linearIndepOn_iff_image injective]
  · exact iff_of_false (by simp [injective]) (fun independent => injective independent.injOn)

theorem rayMatroid_map_linearEquiv {Label Field Vector Other : Type*}
    [_root_.DivisionRing Field] [AddCommGroup Vector] [Module Field Vector]
    [AddCommGroup Other] [Module Field Other]
    (vectors : Label → Vector) (change : Vector ≃ₗ[Field] Other) :
    rayMatroid (Field := Field) (fun label => change (vectors label)) =
      rayMatroid (Field := Field) vectors := by
  apply Matroid.ext_indep (by simp)
  intro labels _
  simp only [rayMatroid_indep_iff]
  constructor
  · intro independent
    exact independent.of_comp change.toLinearMap
  · intro independent
    exact independent.map_injOn change.toLinearMap (fun _ _ _ _ equality =>
      change.injective equality)

end BondalThomsen
