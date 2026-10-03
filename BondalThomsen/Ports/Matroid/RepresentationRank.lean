module

public import BondalThomsen.Ports.Matroid.StandardRepresentation
public import Mathlib.Combinatorics.Matroid.Rank.ENat

@[expose] public section

namespace Matroid

open Set Submodule

variable {Label Field Vector : Type*} [_root_.Field Field]
    [AddCommGroup Vector] [Module Field Vector] {matroid : Matroid Label}

theorem Rep.finrank_span_image_eq_eRk_toNat [matroid.RankFinite]
    (representation : matroid.Rep Field Vector) (selected : Set Label) :
    Module.finrank Field (span Field (representation '' selected)) =
      (matroid.eRk selected).toNat := by
  classical
  obtain ⟨basisSet, basis⟩ := matroid.exists_isBasis' selected
  obtain ⟨_, independent, contained⟩ := representation.isBasis'_iff.mp basis
  have finite_basis := basis.indep.finite
  let : Fintype (representation '' basisSet) := (finite_basis.image representation).fintype
  have spans : span Field (representation '' selected) =
      span Field (representation '' basisSet) :=
    le_antisymm (span_le.mpr contained) (span_mono (Set.image_mono basis.subset))
  rw [spans, finrank_span_set_eq_card independent.id_image,
    ← Set.ncard_eq_toFinset_card', independent.injOn.ncard_image,
    ← basis.encard_eq_eRk]
  rfl

theorem Rep.finrank_span_range_eq_eRank_toNat [matroid.RankFinite]
    (representation : matroid.Rep Field Vector) :
    Module.finrank Field (span Field (Set.range representation)) = matroid.eRank.toNat := by
  rw [← Set.image_univ, representation.finrank_span_image_eq_eRk_toNat]
  rw [matroid.eRk_eq_eRank (Set.subset_univ _)]

end Matroid
