module

public import BondalThomsen.Fan.StarMinorTransfer
public import BondalThomsen.Matroid.RestrictionContraction
public import BondalThomsen.Ports.Matroid.IsomorphismRank

@[expose] public section

namespace BondalThomsen

open Module Set

universe latticeUniverse ambientUniverse forbiddenUniverse

def RankThreeDeepFanRestrictionExcluded {ForbiddenLabel : Type forbiddenUniverse}
    (forbidden : Matroid ForbiddenLabel) : Prop :=
  ∀ (Lattice : Type latticeUniverse) (Ambient : Type ambientUniverse)
    [AddCommGroup Lattice] [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] (embedding : Lattice →+ Ambient)
    (fan : TauCeti.Toric.Fan embedding),
    fan.IsComplete → fan.IsRegular → fan.IsDeep 3 →
    Basis (Fin 3) ℤ Lattice → ∀ candidate : Matroid fan.Ray,
    Nonempty (Matroid.Iso forbidden candidate) → ¬ candidate.IsRestriction fan.rayMatroid

theorem no_isomorphic_minor_of_rank_three_restriction_exclusion
    {ForbiddenLabel : Type forbiddenUniverse} (forbidden : Matroid ForbiddenLabel)
    (forbidden_simple : forbidden.Simple) (forbidden_rank : forbidden.eRank = 3)
    (rank_three_exclusion : RankThreeDeepFanRestrictionExcluded.{latticeUniverse,
      ambientUniverse, forbiddenUniverse} forbidden)
    {Lattice : Type latticeUniverse} {Ambient : Type ambientUniverse}
    [AddCommGroup Lattice] [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}
    (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) {candidate : Matroid fan.Ray}
    (isomorphism : Matroid.Iso forbidden candidate) : ¬ candidate ≤m fan.rayMatroid := by
  suffices induction_result : ∀ dimension : ℕ,
      ∀ (Lattice : Type latticeUniverse) (Ambient : Type ambientUniverse)
        [AddCommGroup Lattice] [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
        [FiniteDimensional ℝ Ambient] (embedding : Lattice →+ Ambient)
        (fan : TauCeti.Toric.Fan embedding),
        fan.IsComplete → fan.IsRegular → fan.IsDeep dimension →
        Basis (Fin dimension) ℤ Lattice → ∀ candidate : Matroid fan.Ray,
        Matroid.Iso forbidden candidate → ¬ candidate ≤m fan.rayMatroid by
    exact induction_result dimension Lattice Ambient embedding fan complete regular deep
      reference candidate isomorphism
  intro dimension
  induction dimension using Nat.strong_induction_on with
  | h dimension induction =>
    intro Lattice Ambient _ _ _ _ embedding fan complete regular deep reference candidate
      isomorphism minor
    have candidate_simple := isomorphism.simple forbidden_simple
    have candidate_rank : candidate.eRank = 3 :=
      isomorphism.eRank_eq.symm.trans forbidden_rank
    have source_rank := fan.rayMatroid_eRank_of_complete_regular complete regular reference
    have dimension_large : 3 ≤ dimension := by
      have comparison := minor.eRank_le
      rw [candidate_rank, source_rank] at comparison
      exact_mod_cast comparison
    have recurse : ∀ ray : fan.Ray, candidate ≤m fan.rayMatroid.contract {ray} → False := by
      intro ray contracted_minor
      let : IsClosed (Submodule.span ℝ {embedding ray.val} : Set Ambient) :=
        (Submodule.span ℝ {embedding ray.val}).closed_of_finiteDimensional
      obtain ⟨star_complete, star_regular, star_deep, rank_drop,
        transported, transported_minor, _, ⟨transport_iso⟩⟩ :=
        fan.simple_contraction_minor_star_induction complete regular deep reference ray
          contracted_minor candidate_simple
      obtain ⟨size, star_basis, star_cone_basis, _⟩ :=
        (fan.star ray).exists_coneBasis_containing star_complete star_regular
          (0 : fan.StarAmbient ray)
      have star_rank := (fan.star ray).rayMatroid_eRank star_basis star_cone_basis
      have star_dimension : size = dimension - 1 := by
        rw [star_rank, source_rank] at rank_drop
        simp only [ENat.toNat_natCast] at rank_drop
        omega
      subst size
      exact induction (dimension - 1) (by omega) (fan.StarLattice ray)
        (fan.StarAmbient ray) (fan.starEmbedding ray) (fan.star ray)
        star_complete star_regular star_deep star_basis transported
        (isomorphism.trans transport_iso) transported_minor
    obtain ⟨contracted, _, restriction, _⟩ := minor.exists_spanning_isRestriction_contract
    by_cases nonempty : contracted.Nonempty
    · obtain ⟨ray, member⟩ := nonempty
      exact recurse ray (Matroid.IsMinor.of_contract_mem restriction.isMinor member)
    · have contracted_empty : contracted = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
      rw [contracted_empty, Matroid.contract_empty] at restriction
      by_cases dimension_three : dimension = 3
      · subst dimension
        exact rank_three_exclusion Lattice Ambient embedding fan complete regular deep reference
          candidate ⟨isomorphism⟩ restriction
      · have rank_lt : candidate.eRank < fan.rayMatroid.eRank := by
          rw [candidate_rank, source_rank]
          exact_mod_cast (show 3 < dimension by omega)
        obtain ⟨ray, member, outside⟩ :=
          restriction.exists_notMem_closure_of_eRank_lt rank_lt
        exact recurse ray (restriction.isMinor_contract_of_notMem_closure member outside)

end BondalThomsen
