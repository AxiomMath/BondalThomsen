module

public import BondalThomsen.Matroid.Binary.MarkedRankThree
public import BondalThomsen.Matroid.Binary.TwoSumLeafLifting

@[expose] public section

namespace Matroid

open Set

variable {Label OtherLabel : Type*} {source : Matroid Label} {other : Matroid OtherLabel}

noncomputable def Iso.dual (isomorphism : Iso source other) : Iso source✶ other✶ where
  toEquiv := isomorphism.toEquiv
  indep_image_iff' := by
    change ∀ selected : Set source.E, source✶.Indep (Subtype.val '' selected) ↔
      other✶.Indep (Subtype.val '' (isomorphism.toEquiv '' selected))
    intro selected
    have equality : (source.restrictSubtype source.E).mapEquiv isomorphism.toEquiv =
        other.restrictSubtype other.E := by
      apply ext_indep (by simp)
      intro chosen subset
      rw [mapEquiv_indep_iff, restrictSubtype_indep_iff, restrictSubtype_indep_iff]
      simpa using isomorphism.indep_image_iff' (isomorphism.toEquiv.symm '' chosen)
    have dual_equality : (source✶.restrictSubtype source.E).mapEquiv isomorphism.toEquiv =
        other✶.restrictSubtype other.E := by
      have transported := congrArg Matroid.dual equality
      simpa only [mapEquiv_eq_map, map_dual, restrictSubtype_dual] using transported
    have independent := congrArg
      (fun matroid => matroid.Indep (isomorphism.toEquiv '' selected)) dual_equality
    rw [mapEquiv_indep_iff, isomorphism.toEquiv.symm_image_image selected,
      restrictSubtype_indep_iff, restrictSubtype_indep_iff] at independent
    exact Iff.of_eq independent

end Matroid

namespace BondalThomsen

open Set Finset

def k4OppositeEdgeEquiv : Fin 6 ≃ Fin 6 := Fin.revPerm

private instance (selected : Finset (Fin 6)) : Decidable (k4BinaryIndependent selected) := by
  unfold k4BinaryIndependent
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_opposite_complement_binary_basis_test :
    ∀ selected : Finset (Fin 6), selected.card = 3 →
      (k4BinaryIndependent selected ↔
        k4BinaryIndependent (Finset.univ \ selected.image k4OppositeEdgeEquiv)) := by
  decide +kernel

theorem k4Matroid_isBase_finset_iff (selected : Finset (Fin 6)) :
    k4Matroid.IsBase (selected : Set (Fin 6)) ↔
      selected.card = 3 ∧ k4BinaryIndependent selected := by
  have independent_iff : k4Matroid.Indep (selected : Set (Fin 6)) ↔
      k4BinaryIndependent selected :=
    (k4Matroid_indep_iff_field (ZMod 2) _).trans
      (k4BinaryIndependent_iff_linearIndepOn selected).symm
  constructor
  · intro base
    have size := base.encard_eq_eRank
    rw [k4Matroid_eRank] at size
    exact ⟨by exact_mod_cast size, independent_iff.mp base.indep⟩
  · rintro ⟨size, independent⟩
    have independent := independent_iff.mpr independent
    apply independent.isBase_of_eRk_ge (Set.toFinite _)
    rw [independent.eRk_eq_encard, k4Matroid_eRank]
    simp [size]

theorem k4Matroid_opposite_base_complement (selected : Set (Fin 6)) :
    k4Matroid.IsBase selected ↔
      k4Matroid.IsBase (Set.univ \ k4OppositeEdgeEquiv '' selected) := by
  classical
  have size_complement : (Finset.univ \ selected.toFinset.image k4OppositeEdgeEquiv).card =
      6 - selected.toFinset.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_image_of_injective]
    · simp
    · exact k4OppositeEdgeEquiv.injective
  have identification : (Set.univ \ k4OppositeEdgeEquiv '' selected : Set (Fin 6)) =
      (Finset.univ \ selected.toFinset.image k4OppositeEdgeEquiv : Finset (Fin 6)) := by
    simp
  rw [identification, ← Set.coe_toFinset selected, k4Matroid_isBase_finset_iff,
    k4Matroid_isBase_finset_iff]
  simp only [Finset.toFinset_coe]
  constructor
  · rintro ⟨size, independent⟩
    exact ⟨by omega, (k4_opposite_complement_binary_basis_test _ size).mp independent⟩
  · rintro ⟨size, independent⟩
    have bound : selected.toFinset.card ≤ 6 := by
      simpa using Finset.card_le_card (Finset.subset_univ selected.toFinset)
    have original_size : selected.toFinset.card = 3 := by omega
    exact ⟨original_size,
      (k4_opposite_complement_binary_basis_test _ original_size).mpr independent⟩

theorem k4Matroid_dual_map_opposite :
    k4Matroid✶.mapEquiv k4OppositeEdgeEquiv = k4Matroid := by
  apply Matroid.ext_isBase (by simp)
  intro chosen subset
  rw [Matroid.mapEquiv_isBase_iff, Matroid.dual_isBase_iff, k4Matroid_ground]
  have symmetry : k4OppositeEdgeEquiv.symm = k4OppositeEdgeEquiv := rfl
  rw [symmetry]
  exact (k4Matroid_opposite_base_complement chosen).symm

def k4OppositeGroundEquiv : k4Matroid.E ≃ k4Matroid✶.E where
  toFun edge := ⟨k4OppositeEdgeEquiv edge.val, by simp⟩
  invFun edge := ⟨k4OppositeEdgeEquiv.symm edge.val, by simp⟩
  left_inv edge := by apply Subtype.ext; exact k4OppositeEdgeEquiv.symm_apply_apply edge.val
  right_inv edge := by apply Subtype.ext; exact k4OppositeEdgeEquiv.apply_symm_apply edge.val

noncomputable def k4Matroid_iso_dual : Matroid.Iso k4Matroid k4Matroid✶ where
  toEquiv := k4OppositeGroundEquiv
  indep_image_iff' selected := by
    have equality := k4Matroid_dual_map_opposite
    have independent := congrArg
      (fun matroid => matroid.Indep (Subtype.val '' selected)) equality
    have transported : Subtype.val '' (k4OppositeGroundEquiv '' selected) =
        k4OppositeEdgeEquiv.symm '' (Subtype.val '' selected) := by
      simp only [Set.image_image]
      rfl
    rw [transported]
    exact (Iff.of_eq independent.symm).trans (Matroid.mapEquiv_indep_iff)

noncomputable def k4GraphCycleMatroid_iso_dual :
    Matroid.Iso k4GraphCycleMatroid k4GraphCycleMatroid✶ :=
  k4Matroid_iso_graphCycleMatroid.symm.trans
    (k4Matroid_iso_dual.trans k4Matroid_iso_graphCycleMatroid.dual)

theorem graph_k4_minor_dual_iff {Label : Type*} (source : Matroid Label) :
    (∃ candidate : Matroid Label, candidate ≤m source✶ ∧
      Nonempty (Matroid.Iso k4GraphCycleMatroid candidate)) ↔
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Matroid.Iso k4GraphCycleMatroid candidate) := by
  constructor
  · rintro ⟨candidate, minor, ⟨isomorphism⟩⟩
    exact ⟨candidate✶, by simpa using minor.dual,
      ⟨k4GraphCycleMatroid_iso_dual.trans isomorphism.dual⟩⟩
  · rintro ⟨candidate, minor, ⟨isomorphism⟩⟩
    exact ⟨candidate✶, minor.dual,
      ⟨k4GraphCycleMatroid_iso_dual.trans isomorphism.dual⟩⟩

theorem graph_k4_excluded_dual_iff {Label : Type*} (source : Matroid Label) :
    (¬ ∃ candidate : Matroid Label, candidate ≤m source✶ ∧
      Nonempty (Matroid.Iso k4GraphCycleMatroid candidate)) ↔
    ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Matroid.Iso k4GraphCycleMatroid candidate) :=
  not_congr (graph_k4_minor_dual_iff source)

end BondalThomsen
