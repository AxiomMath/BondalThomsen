module

public import BondalThomsen.Matroid.DeepK4Exclusion
public import BondalThomsen.Matroid.K4GraphIdentification

@[expose] public section

namespace BondalThomsen

open Module

@[simp] theorem k4GraphCycleMatroid_ground : k4GraphCycleMatroid.E = Set.univ := by
  rw [← k4Matroid_mapEquiv_eq_graphCycleMatroid, Matroid.mapEquiv_ground_eq,
    k4Matroid_ground]
  simp

noncomputable def k4GraphGroundEquiv : k4Matroid.E ≃ k4GraphCycleMatroid.E :=
  k4GraphEdgeEquiv.subtypeEquiv (fun _ => by simp)

noncomputable def k4Matroid_iso_graphCycleMatroid :
    Matroid.Iso k4Matroid k4GraphCycleMatroid where
  toEquiv := k4GraphGroundEquiv
  indep_image_iff' selected := by
    have mapped_independence (subset : Set (⊤ : SimpleGraph (Fin 4)).edgeSet) :
        k4GraphCycleMatroid.Indep subset ↔
          k4Matroid.Indep (k4GraphEdgeEquiv.symm '' subset) := by
      rw [← k4Matroid_mapEquiv_eq_graphCycleMatroid, Matroid.mapEquiv_indep_iff]
    rw [mapped_independence]
    simp [k4GraphGroundEquiv, Set.image_image]

end BondalThomsen
