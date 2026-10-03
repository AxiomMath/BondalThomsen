module

public import BondalThomsen.Matroid.DeepMinorInduction
public import BondalThomsen.Matroid.RootMatroid
public import BondalThomsen.Fan.RankThreeRootNormalization
public import BondalThomsen.Matroid.K4RepresentationUniqueness

@[expose] public section

namespace BondalThomsen

open Module

universe latticeUniverse ambientUniverse

variable {Lattice : Type latticeUniverse} {Ambient : Type ambientUniverse}
    [AddCommGroup Lattice] [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem no_isomorphic_k4_minor_of_rankThree_exclusion
    (rank_three_exclusion : RankThreeDeepFanRestrictionExcluded.{latticeUniverse,
      ambientUniverse, 0} k4Matroid)
    (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) {candidate : Matroid fan.Ray}
    (isomorphism : Matroid.Iso k4Matroid candidate) : ¬ candidate ≤m fan.rayMatroid :=
  no_isomorphic_minor_of_rank_three_restriction_exclusion k4Matroid
    k4Matroid_simple k4Matroid_eRank rank_three_exclusion fan complete regular deep reference
      isomorphism

theorem k4_rankThree_exclusion_of_integral_equivalence
    (integral_equivalence : ∀ matrix : Matrix (Fin 3) (Fin 6) ℤ,
      matrix.IsTotallyUnimodular →
      rayMatroid (Field := ℚ) (fun edge row => (matrix row edge : ℚ)) = k4Matroid →
      ∃ operation : (Matrix (Fin 3) (Fin 3) ℤ)ˣ, ∃ signs : Fin 6 → ℤ,
        (∀ edge, signs edge = 1 ∨ signs edge = -1) ∧
        matrix = (operation : Matrix (Fin 3) (Fin 3) ℤ) * k4RootMatrix ℤ *
          Matrix.diagonal signs) :
    RankThreeDeepFanRestrictionExcluded.{latticeUniverse, ambientUniverse, 0} k4Matroid := by
  intro Lattice Ambient _ _ _ _ embedding fan complete regular deep reference candidate isomorphic
  obtain ⟨isomorphism⟩ := isomorphic
  intro restriction
  obtain ⟨size, basis, cone_basis, _⟩ := fan.exists_coneBasis_containing complete regular
    (0 : Ambient)
  have size_eq : size = 3 := by
    have reference_rank := finrank_eq_card_basis reference
    have cone_rank := finrank_eq_card_basis basis
    simp only [Fintype.card_fin] at reference_rank cone_rank
    omega
  subst size
  obtain ⟨operation, signs, signed, equality⟩ :=
    integral_equivalence (fan.k4SelectedMatrix basis isomorphism)
      ((fan.deep_rayMatrix_totallyUnimodular complete regular deep basis cone_basis).submatrix
        id (fan.k4SelectedRays isomorphism))
      (fan.k4SelectedMatrix_matroid basis restriction isomorphism)
  exact fan.no_k4Restriction_of_integral_equivalence complete regular deep reference basis
    restriction isomorphism operation signs signed equality

theorem k4_rankThree_exclusion :
    RankThreeDeepFanRestrictionExcluded.{latticeUniverse, ambientUniverse, 0} k4Matroid :=
  k4_rankThree_exclusion_of_integral_equivalence totallyUnimodular_k4_integral_equivalence

theorem no_isomorphic_k4_minor
    (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) {candidate : Matroid fan.Ray}
    (isomorphism : Matroid.Iso k4Matroid candidate) : ¬ candidate ≤m fan.rayMatroid :=
  no_isomorphic_k4_minor_of_rankThree_exclusion k4_rankThree_exclusion fan complete regular deep
    reference isomorphism

end BondalThomsen
