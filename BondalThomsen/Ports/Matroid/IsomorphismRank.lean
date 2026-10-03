module

public import BondalThomsen.Ports.Matroid.Isomorphism
public import Mathlib.Combinatorics.Matroid.Rank.ENat

@[expose] public section

namespace Matroid

variable {Label OtherLabel : Type*} {matroid smaller : Matroid Label}
    {other : Matroid OtherLabel}

theorem Iso.eRank_le (isomorphism : Iso matroid other) : matroid.eRank ≤ other.eRank := by
  obtain ⟨basisSet, basis⟩ := matroid.exists_isBase
  have independent :=
    (isomorphism.indep_setImage_iff basis.subset_ground).mp basis.indep
  rw [← basis.encard_eq_eRank,
    Set.encard_congr (isomorphism.setEquiv basisSet basis.subset_ground)]
  exact independent.encard_le_eRank

theorem Iso.eRank_eq (isomorphism : Iso matroid other) : matroid.eRank = other.eRank :=
  le_antisymm isomorphism.eRank_le isomorphism.symm.eRank_le

theorem IsMinor.eRank_le (minor : smaller ≤m matroid) : smaller.eRank ≤ matroid.eRank := by
  obtain ⟨basisSet, basis⟩ := smaller.exists_isBase
  rw [← basis.encard_eq_eRank]
  exact (basis.indep.of_isMinor minor).encard_le_eRank

end Matroid
