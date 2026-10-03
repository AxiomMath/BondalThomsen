module

public import BondalThomsen.Fan.PrimitiveCollectionBoundary
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace BondalThomsen

theorem exists_minimalNonface_subset {Vertex : Type*}
    (complex : PreAbstractSimplicialComplex Vertex) (vertices : Finset Vertex)
    (nonempty : vertices.Nonempty) (nonface : vertices ∉ complex) :
    ∃ subset : Finset Vertex, subset ⊆ vertices ∧ IsMinimalNonface complex subset := by
  classical
  let candidates := vertices.powerset.filter fun subset => subset.Nonempty ∧ subset ∉ complex
  have candidate_member : vertices ∈ candidates := by
    simp [candidates, nonempty, nonface]
  obtain ⟨subset, subset_member, minimal⟩ := candidates.exists_min_image Finset.card
    ⟨vertices, candidate_member⟩
  have chosen := Finset.mem_filter.mp subset_member
  refine ⟨subset, Finset.mem_powerset.mp chosen.1, chosen.2.1, chosen.2.2, ?_⟩
  intro smaller smaller_nonempty proper
  by_contra smaller_nonface
  have smaller_member : smaller ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (proper.subset.trans (Finset.mem_powerset.mp chosen.1)),
      smaller_nonempty, smaller_nonface⟩
  exact (not_le_of_gt (Finset.card_lt_card proper)) (minimal smaller smaller_member)

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem exists_primitiveCollection_subset_of_noncone (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (nonempty : rays.Nonempty)
    (noncone : fan.finiteRayHull rays ∉ fan.cones) :
    ∃ primitive : Finset fan.Ray, primitive ⊆ rays ∧ fan.IsPrimitiveCollection primitive := by
  have nonface : rays ∉ fan.rayComplex regular := by
    intro member
    exact noncone member.2
  obtain ⟨primitive, subset, minimal⟩ := BondalThomsen.exists_minimalNonface_subset
    (fan.rayComplex regular) rays nonempty nonface
  exact ⟨primitive, subset,
    (fan.isPrimitiveCollection_iff_minimalNonface regular primitive).mpr minimal⟩

end TauCeti.Toric.Fan
