module

public import BondalThomsen.Matroid.Binary.ExcludedMinorReduction
public import BondalThomsen.Matroid.Binary.PointExhaustion
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace BondalThomsen

open Set Matrix

def binaryK4MissingPoint : Fin 3 → ZMod 2 := ![1, 1, 1]

theorem binaryK4Columns_injective :
    Function.Injective (k4RootMatrix (ZMod 2)).col := by
  intro first second equality
  have first_coordinate := congrFun equality 0
  have second_coordinate := congrFun equality 1
  have third_coordinate := congrFun equality 2
  fin_cases first <;> fin_cases second <;> simp_all [k4RootMatrix]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem binaryK4Columns_range : ∀ vector : Fin 3 → ZMod 2,
    (∃ edge, (k4RootMatrix (ZMod 2)).col edge = vector) ↔
      vector ≠ 0 ∧ vector ≠ binaryK4MissingPoint := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem binaryK4MissingPoint_matrix_normalization : ∀ vector : Fin 3 → ZMod 2,
    vector ≠ 0 → ∃ operation : Matrix (Fin 3) (Fin 3) (ZMod 2),
      Function.Bijective operation.mulVec ∧
        operation.mulVec vector = binaryK4MissingPoint := by
  decide +kernel

theorem binaryK4MissingPoint_linear_normalization {vector : Fin 3 → ZMod 2}
    (nonzero : vector ≠ 0) :
    ∃ change : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
      change vector = binaryK4MissingPoint := by
  obtain ⟨operation, bijective, normalized⟩ :=
    binaryK4MissingPoint_matrix_normalization vector nonzero
  refine ⟨LinearEquiv.ofBijective (Matrix.toLin' operation) ?_, ?_⟩
  · change Function.Bijective operation.mulVec
    exact bijective
  · simpa only [LinearEquiv.ofBijective_apply, Matrix.toLin'_apply] using normalized

theorem six_binary_points_normalize_to_k4 {Index : Type*}
    (points : Index → Fin 3 → ZMod 2) (nonzero : ∀ index, points index ≠ 0)
    (injective : Function.Injective points) (cardinality : Nat.card Index = 6) :
    ∃ change : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
      ∃ labels : Index ≃ Fin 6,
        ∀ index, change (points index) = (k4RootMatrix (ZMod 2)).col (labels index) := by
  classical
  obtain ⟨missing, missing_property, unique⟩ :=
    BinaryPointExhaustion.exists_unique_missing_of_six points nonzero injective cardinality
  obtain ⟨change, normalized_missing⟩ :=
    binaryK4MissingPoint_linear_normalization missing_property.1
  have column_exists (index : Index) :
      ∃ edge, (k4RootMatrix (ZMod 2)).col edge = change (points index) := by
    apply (binaryK4Columns_range _).mpr
    constructor
    · intro zero
      exact nonzero index (change.injective (zero.trans change.map_zero.symm))
    · intro equality
      have same : points index = missing := change.injective
        (equality.trans normalized_missing.symm)
      exact missing_property.2 ⟨index, same⟩
  let label : Index → Fin 6 := fun index => Classical.choose (column_exists index)
  have label_spec (index : Index) :
      (k4RootMatrix (ZMod 2)).col (label index) = change (points index) :=
    Classical.choose_spec (column_exists index)
  have label_injective : Function.Injective label := by
    intro first second equality
    apply injective
    apply change.injective
    rw [← label_spec first, ← label_spec second, equality]
  let : Finite Index := Finite.of_injective label label_injective
  have label_bijective : Function.Bijective label :=
    label_injective.bijective_of_nat_card_le (by simp [cardinality])
  exact ⟨change, Equiv.ofBijective label label_bijective,
    fun index => (label_spec index).symm⟩

end BondalThomsen

namespace Matroid

open Set BondalThomsen

variable {Label : Type*} {source : Matroid Label}

theorem Representable.exists_binary_rank_three_coordinates [source.Finite]
    (binary : source.Representable (ZMod 2)) (rank : source.eRank = 3) :
    Nonempty (source.Rep (ZMod 2) (Fin 3 → ZMod 2)) := by
  classical
  obtain ⟨representation⟩ := binary
  obtain ⟨basisSet, base⟩ := source.exists_isBase
  let : Fintype basisSet := base.finite.fintype
  have basis_card : Nat.card basisSet = 3 := by
    have equality := base.encard_eq_eRank
    rw [rank, ← base.finite.cast_ncard_eq] at equality
    exact_mod_cast equality
  let indices : basisSet ≃ Fin 3 := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using basis_card)
  exact ⟨(representation.standardRep base).compEquiv
    (LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : basisSet => ZMod 2) indices)⟩

theorem Rep.six_binary_coordinates_iso_k4 [source.Simple]
    (representation : source.Rep (ZMod 2) (Fin 3 → ZMod 2))
    (cardinality : source.E.ncard = 6) : Nonempty (Iso source k4Matroid) := by
  classical
  let points : source.E → Fin 3 → ZMod 2 := fun element => representation element.val
  have nonzero (element : source.E) : points element ≠ 0 :=
    (representation.binaryPoint element).property
  have points_injective : Function.Injective points := by
    intro first second equality
    apply representation.binaryPoint_injective
    exact Subtype.ext equality
  obtain ⟨change, labels, normalization⟩ :=
    six_binary_points_normalize_to_k4 points nonzero points_injective cardinality
  let normalized := representation.compEquiv change
  let ground_labels : source.E ≃ k4Matroid.E := labels.trans k4GroundEquiv
  refine ⟨⟨ground_labels, ?_⟩⟩
  intro selected
  have normalized_injective : Set.InjOn normalized (Subtype.val '' selected) := by
    rintro first ⟨first_ground, first_selected, rfl⟩
      second ⟨second_ground, second_selected, rfl⟩ equality
    have point_equality : points first_ground = points second_ground :=
      change.injective equality
    exact congrArg Subtype.val (points_injective point_equality)
  have image_eq : normalized '' (Subtype.val '' selected) =
      (k4RootMatrix (ZMod 2)).col '' (Subtype.val '' (ground_labels '' selected)) := by
    ext vector
    constructor
    · rintro ⟨element, ⟨ground_element, member, rfl⟩, rfl⟩
      refine ⟨(ground_labels ground_element).val,
        ⟨ground_labels ground_element, ⟨ground_element, member, rfl⟩, rfl⟩, ?_⟩
      exact (normalization ground_element).symm
    · rintro ⟨element, ⟨ground_element, ⟨original, member, rfl⟩, rfl⟩, rfl⟩
      exact ⟨original.val, ⟨original, member, rfl⟩, normalization original⟩
  rw [normalized.indep_iff, k4Matroid_indep_iff_field (ZMod 2),
    linearIndepOn_iff_image normalized_injective,
    linearIndepOn_iff_image binaryK4Columns_injective.injOn, image_eq]

theorem binary_simple_rank_three_six_iso_graph_k4 [source.Finite] [source.Simple]
    (binary : source.Representable (ZMod 2)) (rank : source.eRank = 3)
    (cardinality : source.E.ncard = 6) : Nonempty (Iso source k4GraphCycleMatroid) := by
  obtain ⟨representation⟩ := binary.exists_binary_rank_three_coordinates rank
  obtain ⟨isomorphism⟩ := representation.six_binary_coordinates_iso_k4 cardinality
  exact ⟨isomorphism.trans k4Matroid_iso_graphCycleMatroid⟩

theorem binary_simple_cosimple_six_iso_graph_k4 [source.Finite]
    [source.Simple] [source✶.Simple] (binary : source.Representable (ZMod 2))
    (size : source.E.ncard ≤ 6) (nonempty : source.E.Nonempty) :
    Nonempty (Iso source k4GraphCycleMatroid) := by
  have lower := binary_simple_cosimple_ground_encard_ge_six binary nonempty
  rw [← source.ground_finite.cast_ncard_eq] at lower
  have cardinality : source.E.ncard = 6 := by
    have lower_nat : 6 ≤ source.E.ncard := by exact_mod_cast lower
    omega
  have rank_lower : 3 ≤ source.eRank := by
    by_contra small
    have low_rank : source.eRank ≤ 2 :=
      (ENat.lt_add_one_iff (by simp)).mp (lt_of_not_ge small)
    have bound := binary_simple_rank_two_ground_card_le_three binary low_rank
    omega
  have corank_lower : 3 ≤ source✶.eRank := by
    by_contra small
    have low_corank : source✶.eRank ≤ 2 :=
      (ENat.lt_add_one_iff (by simp)).mp (lt_of_not_ge small)
    rcases binary_not_simple_cosimple_of_corank_le_two binary low_corank nonempty with
      not_simple | not_cosimple
    · exact not_simple inferInstance
    · exact not_cosimple inferInstance
  have rank_finite : source.eRank ≠ ⊤ := source.eRank_ne_top_iff.mpr inferInstance
  have corank_finite : source✶.eRank ≠ ⊤ := source✶.eRank_ne_top_iff.mpr inferInstance
  have sum : source.eRank.toNat + source✶.eRank.toNat = 6 := by
    have equality := congrArg ENat.toNat source.eRank_add_eRank_dual
    rw [ENat.toNat_add rank_finite corank_finite,
      ← source.ground_finite.cast_ncard_eq, ENat.toNat_natCast, cardinality] at equality
    exact equality
  have rank_nat_lower : 3 ≤ source.eRank.toNat := by
    exact ENat.toNat_le_toNat rank_lower rank_finite
  have corank_nat_lower : 3 ≤ source✶.eRank.toNat := by
    exact ENat.toNat_le_toNat corank_lower corank_finite
  have rank : source.eRank = 3 := by
    rw [← ENat.natCast_toNat rank_finite]
    exact_mod_cast (show source.eRank.toNat = 3 by omega)
  exact binary_simple_rank_three_six_iso_graph_k4 binary rank cardinality

theorem binary_six_element_k4_excluded_exists_elementary_reduction [source.Finite]
    (binary : source.Representable (ZMod 2)) (size : source.E.ncard ≤ 6)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso k4GraphCycleMatroid candidate))
    (nonempty : source.E.Nonempty) :
    ∃ reduced, ElementarySeriesParallelReduction source reduced := by
  apply exists_elementary_reduction_of_not_simple_or_dual
  by_contra obstruction
  have both : source.Simple ∧ source✶.Simple := by tauto
  let : source.Simple := both.1
  let : source✶.Simple := both.2
  obtain ⟨isomorphism⟩ := binary_simple_cosimple_six_iso_graph_k4 binary size nonempty
  exact excluded ⟨source, IsMinor.refl, ⟨isomorphism.symm⟩⟩

end Matroid
