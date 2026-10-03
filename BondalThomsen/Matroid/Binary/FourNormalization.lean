module

public import BondalThomsen.Matroid.Binary.EightElementObstruction
public import BondalThomsen.Matroid.Binary.SixElementCoverage

@[expose] public section

open Set Module
open scoped Classical

namespace Matroid

variable {Label Field Vector : Type*} [DivisionRing Field]
    [AddCommGroup Vector] [Module Field Vector] {source : Matroid Label}

theorem Rep.standardRep_basis_apply (representation : source.Rep Field Vector)
    {basisSet : Set Label} (base : source.IsBase basisSet) (element other : basisSet) :
    representation.standardRep base element.val other =
      if element = other then 1 else 0 := by
  have basis_value : (representation.isBasis_of_isBase base) element =
      representation.restrictSpan element.val := by
    apply Subtype.ext
    simp [Rep.isBasis_of_isBase, Basis.spanImage, Basis.map_apply,
      Basis.span_apply, Rep.restrictSpan]
    rfl
  change (representation.isBasis_of_isBase base).repr
    (representation.restrictSpan element.val) other = _
  rw [← basis_value, Basis.repr_self_apply]

end Matroid

namespace BondalThomsen

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem binaryFourNonbasisPoint_injective :
    Function.Injective binaryFourNonbasisPoint := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem binaryFourBasisPoint_injective :
    Function.Injective binaryFourBasisPoint := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem binaryFourNonbasisPoint_range : ∀ vector : Fin 4 → ZMod 2,
    (∃ index, binaryFourNonbasisPoint index = vector) ↔
      vector ≠ 0 ∧ ¬ ∃ coordinate, binaryFourBasisPoint coordinate = vector := by
  decide +kernel

theorem eight_binary_points_containing_basis_normalized
    (points : Finset (Fin 4 → ZMod 2)) (cardinality : points.card = 8)
    (nonzero : 0 ∉ points)
    (basis_subset : Finset.univ.image binaryFourBasisPoint ⊆ points) :
    ∃ selected : Finset (Fin 11), selected.card = 4 ∧
      binaryFourNormalizedPoints selected = points := by
  let selected := Finset.univ.filter (fun index => binaryFourNonbasisPoint index ∈ points)
  have image_eq : selected.image binaryFourNonbasisPoint =
      points \ Finset.univ.image binaryFourBasisPoint := by
    ext vector
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, selected]
    constructor
    · rintro ⟨index, member, rfl⟩
      exact ⟨member, (binaryFourNonbasisPoint_range _).mp ⟨index, rfl⟩ |>.2⟩
    · rintro ⟨member, not_basis⟩
      obtain ⟨index, same⟩ := (binaryFourNonbasisPoint_range vector).mpr
        ⟨(fun equal => nonzero (equal ▸ member)), not_basis⟩
      exact ⟨index, same.symm ▸ member, same⟩
  have basis_card : (Finset.univ.image binaryFourBasisPoint).card = 4 := by
    rw [Finset.card_image_of_injective _ binaryFourBasisPoint_injective]
    rfl
  have selected_card : selected.card = 4 := by
    rw [← Finset.card_image_of_injective selected binaryFourNonbasisPoint_injective,
      image_eq, Finset.card_sdiff_of_subset basis_subset, cardinality, basis_card]
  refine ⟨selected, selected_card, ?_⟩
  unfold binaryFourNormalizedPoints
  rw [image_eq, Finset.union_sdiff_of_subset basis_subset]

end BondalThomsen

namespace Matroid

open BondalThomsen

variable {Label : Type*} {source : Matroid Label}

theorem Representable.exists_binary_rank_four_basis_coordinates [source.Finite]
    (binary : source.Representable (ZMod 2)) (rank : source.eRank = 4) :
    ∃ representation : source.Rep (ZMod 2) (Fin 4 → ZMod 2),
      ∃ basis_labels : Fin 4 → source.E,
        ∀ coordinate, representation (basis_labels coordinate).val =
          binaryFourBasisPoint coordinate := by
  obtain ⟨representation⟩ := binary
  obtain ⟨basisSet, base⟩ := source.exists_isBase
  let : Fintype basisSet := base.finite.fintype
  have basis_card : Nat.card basisSet = 4 := by
    have equality := base.encard_eq_eRank
    rw [rank, ← base.finite.cast_ncard_eq] at equality
    exact_mod_cast equality
  let indices : basisSet ≃ Fin 4 := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using basis_card)
  let normalized := (representation.standardRep base).compEquiv
    (LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : basisSet => ZMod 2) indices)
  refine ⟨normalized, fun coordinate =>
    ⟨(indices.symm coordinate).val, base.subset_ground (indices.symm coordinate).property⟩, ?_⟩
  intro coordinate
  ext position
  change representation.standardRep base (indices.symm coordinate).val
    (indices.symm position) = _
  rw [Rep.standardRep_basis_apply]
  simp [binaryFourBasisPoint, eq_comm]

theorem Representable.exists_binary_eight_normalized_ground [source.Finite] [source.Simple]
    (binary : source.Representable (ZMod 2)) (rank : source.eRank = 4)
    (cardinality : source.E.ncard = 8) :
    ∃ representation : source.Rep (ZMod 2) (Fin 4 → ZMod 2),
      ∃ selected : Finset (Fin 11), selected.card = 4 ∧
        representation '' source.E = (binaryFourNormalizedPoints selected : Set _) := by
  obtain ⟨representation, basis_labels, basis_values⟩ :=
    binary.exists_binary_rank_four_basis_coordinates rank
  let points := (source.ground_finite.image representation).toFinset
  have injective : Set.InjOn representation source.E := by
    intro first first_member second second_member same
    exact congrArg Subtype.val
      (representation.binaryPoint_injective (Subtype.ext same) :
        (⟨first, first_member⟩ : source.E) = ⟨second, second_member⟩)
  have point_card : points.card = 8 := by
    have image_card : (representation '' source.E).ncard = 8 := by
      rw [injective.ncard_image, cardinality]
    have points_eq : points = (representation '' source.E).toFinset := by
      ext vector
      simp [points]
    rw [points_eq, ← Set.ncard_eq_toFinset_card']
    exact image_card
  have point_nonzero : 0 ∉ points := by
    intro member
    obtain ⟨element, element_member, zero⟩ :=
      (source.ground_finite.image representation).mem_toFinset.mp member
    exact (representation.binaryPoint ⟨element, element_member⟩).property zero
  have basis_subset : Finset.univ.image binaryFourBasisPoint ⊆ points := by
    intro vector member
    obtain ⟨coordinate, _, rfl⟩ := Finset.mem_image.mp member
    exact (source.ground_finite.image representation).mem_toFinset.mpr
      ⟨(basis_labels coordinate).val, (basis_labels coordinate).property,
        basis_values coordinate⟩
  obtain ⟨selected, selected_card, same⟩ :=
    eight_binary_points_containing_basis_normalized points point_card point_nonzero basis_subset
  refine ⟨representation, selected, selected_card, ?_⟩
  rw [same]
  exact (source.ground_finite.image representation).coe_toFinset.symm

end Matroid
