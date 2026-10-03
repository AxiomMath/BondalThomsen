module

public import BondalThomsen.Cohomology.ConvexNerve.BarycentricHomotopy
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.PartitionOfUnity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open BondalThomsen.ClosedConvexNerveComparison
open scoped Classical

namespace BondalThomsen.ConvexNerveOpenNeighborhoods

variable {Index : Type} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem exists_thickening_empty_intersection (core : Set E) (patches : Index → Set E)
    (core_compact : IsCompact core) (patches_closed : ∀ index, IsClosed (patches index))
    (face : Finset Index)
    (empty_intersection : ¬ ∃ point ∈ core, ∀ index ∈ face, point ∈ patches index) :
    ∃ radius : ℝ, 0 < radius ∧
      ¬ ∃ point ∈ core, ∀ index ∈ face, point ∈ Metric.thickening radius (patches index) := by
  by_contra! every_radius
  let Radius := {radius : ℝ // 0 < radius}
  let : Nonempty Radius := ⟨⟨1, zero_lt_one⟩⟩
  let neighborhoods : Radius → Set E := fun radius =>
    core ∩ ⋂ index ∈ face, Metric.cthickening radius.val (patches index)
  have neighborhoods_closed : ∀ radius : Radius,
      IsClosed (⋂ index ∈ face, Metric.cthickening radius.val (patches index)) := by
    intro radius
    exact isClosed_iInter fun _ => isClosed_iInter fun _ => Metric.isClosed_cthickening
  have directed : Directed (· ⊇ ·) neighborhoods := by
    intro first second
    refine ⟨⟨min first.val second.val, lt_min first.property second.property⟩, ?_, ?_⟩
    · rintro point ⟨in_core, present⟩
      refine ⟨in_core, Set.mem_iInter₂.mpr fun index contains => ?_⟩
      exact Metric.cthickening_mono (min_le_left _ _) _
        (Set.mem_iInter₂.mp present index contains)
    · rintro point ⟨in_core, present⟩
      refine ⟨in_core, Set.mem_iInter₂.mpr fun index contains => ?_⟩
      exact Metric.cthickening_mono (min_le_right _ _) _
        (Set.mem_iInter₂.mp present index contains)
  have nonempty : ∀ radius : Radius, (neighborhoods radius).Nonempty := by
    intro radius
    obtain ⟨point, in_core, present⟩ := every_radius radius.val radius.property
    exact ⟨point, in_core, Set.mem_iInter₂.mpr fun index contains =>
      Metric.thickening_subset_cthickening _ _ (present index contains)⟩
  obtain ⟨point, present⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed neighborhoods directed nonempty
      (fun radius => core_compact.inter_right (neighborhoods_closed radius))
      (fun radius => core_compact.isClosed.inter (neighborhoods_closed radius))
  apply empty_intersection
  refine ⟨point, (Set.mem_iInter.mp present ⟨1, zero_lt_one⟩).1, ?_⟩
  intro index contains
  apply (patches_closed index).closure_subset
  rw [Metric.closure_eq_iInter_cthickening]
  exact Set.mem_iInter₂.mpr fun radius positive =>
    Set.mem_iInter₂.mp (Set.mem_iInter.mp present ⟨radius, positive⟩).2 index contains

omit [NormedSpace ℝ E] in
theorem exists_uniform_nerve_preserving_radius [Finite Index]
    (core : Set E) (patches : Index → Set E)
    (core_compact : IsCompact core) (patches_closed : ∀ index, IsClosed (patches index)) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ face : Finset Index,
      (∃ point ∈ core, ∀ index ∈ face, point ∈ Metric.thickening radius (patches index)) ↔
        ∃ point ∈ core, ∀ index ∈ face, point ∈ patches index := by
  have individual : ∀ face : Finset Index, ∃ radius : ℝ, 0 < radius ∧
      ((∃ point ∈ core, ∀ index ∈ face, point ∈ Metric.thickening radius (patches index)) →
        ∃ point ∈ core, ∀ index ∈ face, point ∈ patches index) := by
    intro face
    by_cases present : ∃ point ∈ core, ∀ index ∈ face, point ∈ patches index
    · exact ⟨1, zero_lt_one, fun _ => present⟩
    · obtain ⟨radius, positive, absent⟩ :=
        exists_thickening_empty_intersection core patches core_compact patches_closed face present
      exact ⟨radius, positive, fun intersection => (absent intersection).elim⟩
  choose radii positive preserves using individual
  let : Fintype (Finset Index) := Fintype.ofFinite _
  obtain ⟨least, _, minimal⟩ := Finset.univ.exists_min_image radii Finset.univ_nonempty
  refine ⟨radii least, positive least, fun face => ⟨?_, ?_⟩⟩
  · rintro ⟨point, in_core, present⟩
    apply preserves face
    exact ⟨point, in_core, fun index contains =>
      Metric.thickening_mono (minimal face (Finset.mem_univ face)) _ (present index contains)⟩
  · rintro ⟨point, in_core, present⟩
    exact ⟨point, in_core, fun index contains =>
      Metric.self_subset_thickening (positive least) _ (present index contains)⟩

def relativeOpenPatch (core : Set E) (patches : Index → Set E) (radius : ℝ) (index : Index) :
    Set core :=
  {point | point.val ∈ Metric.thickening radius (patches index)}

omit [NormedSpace ℝ E] in
theorem relativeOpenPatch_isOpen (core : Set E) (patches : Index → Set E)
    (radius : ℝ) (index : Index) : IsOpen (relativeOpenPatch core patches radius index) :=
  Metric.isOpen_thickening.preimage continuous_subtype_val

omit [NormedSpace ℝ E] in
theorem relativeOpenPatch_cover (core : Set E) (patches : Index → Set E)
    (cover : core ⊆ ⋃ index, patches index) (radius : ℝ) (positive : 0 < radius) :
    (⋃ index, relativeOpenPatch core patches radius index) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro point
  obtain ⟨index, present⟩ := Set.mem_iUnion.mp (cover point.property)
  exact Set.mem_iUnion.mpr ⟨index, Metric.self_subset_thickening positive _ present⟩

end BondalThomsen.ConvexNerveOpenNeighborhoods
