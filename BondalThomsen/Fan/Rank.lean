module

public import BondalThomsen.Fan.Parallel
public import BondalThomsen.Fan.Completeness
public import BondalThomsen.Ports.Matroid.RepresentationRank

@[expose] public section

open Module Submodule Set
open scoped TensorProduct

namespace TauCeti.Toric.Fan

section Basic

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem rayRep_span_eq_top (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    span ℚ (Set.range fan.rayRep) = ⊤ := by
  apply top_unique
  rw [← (basis.baseChange ℚ).span_eq]
  apply span_mono
  rintro _ ⟨index, rfl⟩
  exact ⟨fan.basisRay basis cone_basis index, by simp⟩

theorem rayMatroid_eRank_toNat (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    fan.rayMatroid.eRank.toNat = dimension := by
  have rank := fan.rayRep.finrank_span_range_eq_eRank_toNat
  rw [fan.rayRep_span_eq_top basis cone_basis, finrank_top,
    finrank_eq_card_basis (basis.baseChange ℚ), Fintype.card_fin] at rank
  exact rank.symm

theorem rayMatroid_eRank (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    fan.rayMatroid.eRank = dimension := by
  have finite_rank := (fan.rayMatroid.eRank_ne_top_iff).mpr inferInstance
  have rank := fan.rayMatroid_eRank_toNat basis cone_basis
  exact (ENat.natCast_toNat finite_rank).symm.trans (congrArg Nat.cast rank)

end Basic

section Complete

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem rayMatroid_eRank_of_complete_regular (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin dimension) ℤ Lattice) : fan.rayMatroid.eRank = dimension := by
  obtain ⟨size, basis, cone_basis, _⟩ :=
    fan.exists_coneBasis_containing complete regular (0 : Ambient)
  have size_eq : size = dimension := by
    have basis_rank := finrank_eq_card_basis basis
    have reference_rank := finrank_eq_card_basis reference
    simp only [Fintype.card_fin] at basis_rank reference_rank
    omega
  subst size
  exact fan.rayMatroid_eRank basis cone_basis

theorem simplification_eRank_of_complete_regular (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (reference : Basis (Fin dimension) ℤ Lattice) {smaller : Matroid fan.Ray}
    (simplification : smaller.IsSimplification fan.rayMatroid) : smaller.eRank = dimension :=
  simplification.eRank_eq.trans (fan.rayMatroid_eRank_of_complete_regular complete regular reference)

end Complete

end TauCeti.Toric.Fan
