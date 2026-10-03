module

public import BondalThomsen.Toric.Surface.MoriDropOneIncidence

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Set BondalThomsen
open TauCeti.AlgebraicGeometry
open Filter
open scoped Topology

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace BondalThomsen

theorem nonnegative_on_unitInterval_of_local_midpoint_concavity
    (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 1))
    (left_nonnegative : 0 ≤ function 0) (right_nonnegative : 0 ≤ function 1)
    (local_midpoint : ∀ point ∈ Ioo (0 : ℝ) 1, ∃ radius : ℝ, 0 < radius ∧
      ∀ offset : ℝ, 0 < offset → offset < radius →
        (function (point - offset) + function (point + offset)) / 2 ≤ function point) :
    ∀ point ∈ Icc (0 : ℝ) 1, 0 ≤ function point := by
  obtain ⟨minimum, minimum_member, minimal⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) continuous
  have minimum_nonnegative : 0 ≤ function minimum := by
    by_contra not_nonnegative
    have negative : function minimum < 0 := lt_of_not_ge not_nonnegative
    let minimizers := {point : ℝ | point ∈ Icc (0 : ℝ) 1 ∧ function point = function minimum}
    have compact_minimizers : IsCompact minimizers := by
      have closed_minimizers : IsClosed minimizers :=
        isClosed_Icc.isClosed_eq continuous
          (continuousOn_const : ContinuousOn (fun _ : ℝ => function minimum) (Icc 0 1))
      exact isCompact_Icc.of_isClosed_subset closed_minimizers (fun _ member => member.1)
    obtain ⟨first_minimum, first_member, first_minimal⟩ := compact_minimizers.exists_isMinOn
      ⟨minimum, minimum_member, rfl⟩ continuous_id.continuousOn
    have first_negative : function first_minimum < 0 := by
      rw [first_member.2]
      exact negative
    have interior_member : first_minimum ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · by_contra not_positive
        have same : first_minimum = 0 := le_antisymm (le_of_not_gt not_positive) first_member.1.1
        rw [same] at first_negative
        linarith
      · by_contra not_less
        have same : first_minimum = 1 := le_antisymm first_member.1.2 (le_of_not_gt not_less)
        rw [same] at first_negative
        linarith
    obtain ⟨radius, radius_positive, midpoint⟩ := local_midpoint first_minimum interior_member
    let offset := min radius (min first_minimum (1 - first_minimum)) / 2
    have minimum_positive : 0 < min radius (min first_minimum (1 - first_minimum)) := by
      exact lt_min radius_positive (lt_min interior_member.1 (sub_pos.mpr interior_member.2))
    have offset_positive : 0 < offset := half_pos minimum_positive
    have offset_lt_radius : offset < radius :=
      (half_lt_self minimum_positive).trans_le (min_le_left _ _)
    have offset_lt_first : offset < first_minimum :=
      (half_lt_self minimum_positive).trans_le
        ((min_le_right _ _).trans (min_le_left _ _))
    have offset_lt_last : offset < 1 - first_minimum :=
      (half_lt_self minimum_positive).trans_le
        ((min_le_right _ _).trans (min_le_right _ _))
    have left_member : first_minimum - offset ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [first_member.1.1, first_member.1.2]
    have right_member : first_minimum + offset ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [first_member.1.1, first_member.1.2]
    have local_bound := midpoint offset offset_positive offset_lt_radius
    have left_bound := minimal left_member
    have right_bound := minimal right_member
    change function minimum ≤ function (first_minimum - offset) at left_bound
    change function minimum ≤ function (first_minimum + offset) at right_bound
    have same_value : function (first_minimum - offset) = function minimum := by
      rw [first_member.2] at local_bound
      linarith
    have earlier := first_minimal (show first_minimum - offset ∈ minimizers from
      ⟨left_member, same_value⟩)
    change first_minimum ≤ first_minimum - offset at earlier
    linarith
  intro point member
  exact minimum_nonnegative.trans (minimal member)

theorem unitIntervalChord_le_of_locally_concave
    (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 1))
    (locally_concave : ∀ point ∈ Ioo (0 : ℝ) 1,
      ∃ radius : ℝ, 0 < radius ∧ ConcaveOn ℝ (Metric.ball point radius) function) :
    ∀ point ∈ Icc (0 : ℝ) 1,
      (1 - point) * function 0 + point * function 1 ≤ function point := by
  let gap := fun point : ℝ => function point - ((1 - point) * function 0 + point * function 1)
  have gap_continuous : ContinuousOn gap (Icc (0 : ℝ) 1) :=
    continuous.sub
      (((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
        (continuousOn_id.mul continuousOn_const))
  have local_midpoint : ∀ point ∈ Ioo (0 : ℝ) 1, ∃ radius : ℝ, 0 < radius ∧
      ∀ offset : ℝ, 0 < offset → offset < radius →
        (gap (point - offset) + gap (point + offset)) / 2 ≤ gap point := by
    intro point member
    obtain ⟨radius, positive, concave⟩ := locally_concave point member
    refine ⟨radius, positive, ?_⟩
    intro offset offset_positive offset_small
    have left_member : point - offset ∈ Metric.ball point radius := by
      rw [Metric.mem_ball, Real.dist_eq]
      have negative : point - offset - point ≤ 0 := by linarith
      rw [abs_of_nonpos negative]
      linarith
    have right_member : point + offset ∈ Metric.ball point radius := by
      rw [Metric.mem_ball, Real.dist_eq]
      have positive : 0 ≤ point + offset - point := by linarith
      rw [abs_of_nonneg positive]
      linarith
    have midpoint := concave.2 left_member right_member
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    have center : (1 / 2 : ℝ) • (point - offset) + (1 / 2 : ℝ) • (point + offset) = point := by
      simp only [smul_eq_mul]
      ring
    rw [center] at midpoint
    simp only [smul_eq_mul] at midpoint
    dsimp only [gap]
    nlinarith
  have nonnegative := nonnegative_on_unitInterval_of_local_midpoint_concavity gap gap_continuous
    (by simp [gap]) (by simp [gap]) local_midpoint
  intro point member
  exact sub_nonneg.mp (nonnegative point member)

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable {𝕜} in
local instance surfaceSupportBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

local instance surfaceSupportRaySpanClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

end TauCeti.Toric.Fan
