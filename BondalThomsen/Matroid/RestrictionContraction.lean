module

public import BondalThomsen.Ports.Matroid.MinorPresentation
public import Mathlib.Combinatorics.Matroid.Rank.ENat

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {matroid smaller : Matroid Label}
    {selected contracted : Set Label} {element : Label}

theorem contract_restrict_eq_of_notMem_closure
    (subset : selected ⊆ matroid.E) (member : element ∈ matroid.E)
    (outside : element ∉ matroid.closure selected) :
    (matroid.contract {element}).restrict selected = matroid.restrict selected := by
  have not_selected : element ∉ selected := by
    intro selected_member
    exact outside (matroid.mem_closure_of_mem selected_member subset)
  have nonloop : matroid.IsNonloop element := by
    rw [← indep_singleton]
    have empty_independent := matroid.empty_indep
    have outside_empty : element ∉ matroid.closure ∅ := by
      intro in_closure
      exact outside (matroid.closure_mono (empty_subset selected) in_closure)
    simpa using empty_independent.insert_indep_iff.mpr (Or.inl ⟨member, outside_empty⟩)
  apply ext_indep (by simp)
  intro independent_set contained
  rw [restrict_indep_iff, restrict_indep_iff]
  have contained_selected : independent_set ⊆ selected := contained
  rw [and_iff_left contained_selected, and_iff_left contained_selected,
    nonloop.contractElem_indep_iff]
  constructor
  · exact fun properties => properties.2.subset (subset_insert _ _)
  · intro independent
    have outside_independent : element ∉ matroid.closure independent_set := by
      intro in_closure
      exact outside (matroid.closure_mono contained_selected in_closure)
    exact ⟨fun in_set => not_selected (contained_selected in_set),
      independent.insert_indep_iff.mpr (Or.inl ⟨member, outside_independent⟩)⟩

theorem IsRestriction.isMinor_contract_of_notMem_closure
    (restriction : smaller.IsRestriction matroid) (member : element ∈ matroid.E)
    (outside : element ∉ matroid.closure smaller.E) :
    smaller ≤m matroid.contract {element} := by
  rw [← restriction.eq_restrict,
    ← contract_restrict_eq_of_notMem_closure restriction.subset member outside]
  exact (restrict_isRestriction _ _ (by
    intro chosen in_ground
    simp only [contract_ground, mem_sdiff, mem_singleton_iff]
    exact ⟨restriction.subset in_ground, fun equality => by
      subst chosen
      exact outside (matroid.mem_closure_of_mem in_ground restriction.subset)⟩)).isMinor

theorem IsRestriction.exists_notMem_closure_of_eRank_lt
    (restriction : smaller.IsRestriction matroid) (rank_lt : smaller.eRank < matroid.eRank) :
    ∃ element ∈ matroid.E, element ∉ matroid.closure smaller.E := by
  by_contra no_element
  push Not at no_element
  have closure_eq : matroid.closure smaller.E = matroid.E :=
    subset_antisymm (matroid.closure_subset_ground _) no_element
  have rank_eq : smaller.eRank = matroid.eRank := by
    rw [← restriction.eq_restrict, eRank_restrict,
      ← matroid.eRk_closure_eq, closure_eq, eRk_ground]
  exact (ne_of_lt rank_lt) rank_eq

theorem IsMinor.of_contract_mem (minor : smaller ≤m matroid.contract contracted)
    (member : element ∈ contracted) : smaller ≤m matroid.contract {element} := by
  have factorization : (matroid.contract {element}).contract (contracted \ {element}) =
      matroid.contract contracted := by
    rw [contract_contract]
    congr 1
    ext chosen
    simp only [mem_union, mem_singleton_iff, mem_sdiff]
    constructor
    · rintro (rfl | ⟨in_set, _⟩)
      · exact member
      · exact in_set
    · intro in_set
      by_cases same : chosen = element
      · exact Or.inl same
      · exact Or.inr ⟨in_set, same⟩
  exact minor.trans (factorization ▸ contract_isMinor (matroid.contract {element})
    (contracted \ {element}))

end Matroid
