module

public import BondalThomsen.Matroid.Binary.K4ExcludedGeneralReduction
public import BondalThomsen.Matroid.Binary.SixElementCoverage

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label}
    {first second third completion otherCompletion : Label}

theorem Simple.isCircuit_triple_distinct [source.Simple]
    (triangle : source.IsCircuit {first, second, completion}) :
    first ≠ second ∧ first ≠ completion ∧ second ≠ completion := by
  have first_member : first ∈ source.E := triangle.subset_ground (by simp)
  have second_member : second ∈ source.E := triangle.subset_ground (by simp)
  have completion_member : completion ∈ source.E := triangle.subset_ground (by simp)
  have pairs := simple_iff_forall_pair_indep.mp (inferInstance : source.Simple)
  constructor
  · intro same
    subst second
    exact triangle.not_indep (by simpa using pairs first completion first_member completion_member)
  constructor
  · intro same
    subst completion
    exact triangle.not_indep (by simpa [Set.pair_comm] using pairs first second first_member second_member)
  · intro same
    subst completion
    exact triangle.not_indep (by simpa using pairs first second first_member second_member)

theorem Simple.triangle_completion_mem_closure [source.Simple]
    (triangle : source.IsCircuit {first, second, completion}) :
    completion ∈ source.closure {first, second} := by
  obtain ⟨_, first_distinct, second_distinct⟩ := Simple.isCircuit_triple_distinct triangle
  have member := triangle.mem_closure_sdiff_singleton_of_mem (by simp : completion ∈
    ({first, second, completion} : Set Label))
  have difference : ({first, second, completion} : Set Label) \ {completion} = {first, second} := by
    ext element
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  simpa only [difference] using member

theorem Simple.triangle_completion_notMem_independent_triple [source.Simple]
    (independent : source.Indep {first, second, third})
    (triangle : source.IsCircuit {first, second, completion}) :
    completion ∉ ({first, second, third} : Set Label) := by
  intro member
  have triangle_subset : ({first, second, completion} : Set Label) ⊆ {first, second, third} := by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨by simp, by simp, member⟩
  exact triangle.not_indep (independent.subset triangle_subset)

theorem Simple.triangle_completions_distinct [source.Simple]
    (independent : source.Indep {first, second, third}) (second_third : second ≠ third)
    (first_triangle : source.IsCircuit {first, second, completion})
    (second_triangle : source.IsCircuit {first, third, otherCompletion}) :
    completion ≠ otherCompletion := by
  intro same
  have first_closure := Simple.triangle_completion_mem_closure first_triangle
  have second_closure : completion ∈ source.closure {first, third} :=
    same ▸ Simple.triangle_completion_mem_closure second_triangle
  have union_independent : source.Indep (({first, second} : Set Label) ∪ {first, third}) :=
    independent.subset (by simp [Set.subset_def])
  have common : completion ∈ source.closure (({first, second} : Set Label) ∩ {first, third}) := by
    rw [union_independent.closure_inter_eq_inter_closure]
    exact ⟨first_closure, second_closure⟩
  have intersection : ({first, second} : Set Label) ∩ {first, third} = {first} := by
    ext element
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  rw [intersection] at common
  have nonloop : source.IsNonloop completion :=
    ((Simple.parallel_iff_eq (first_triangle.subset_ground (by simp : completion ∈
      ({first, second, completion} : Set Label)))).mpr rfl).1
  have first_nonloop : source.IsNonloop first :=
    ((Simple.parallel_iff_eq (first_triangle.subset_ground (by simp : first ∈
      ({first, second, completion} : Set Label)))).mpr rfl).1
  have parallel : source.Parallel completion first :=
    ⟨nonloop, first_nonloop, nonloop.closure_eq_of_mem_closure common⟩
  have equal := (Simple.parallel_iff_eq nonloop.mem_ground).mp parallel
  exact (Simple.isCircuit_triple_distinct first_triangle).2.1 equal.symm

structure TriangleFrame (source : Matroid Label) where
  first : Label
  second : Label
  third : Label
  firstSecond : Label
  firstThird : Label
  secondThird : Label
  independent : source.Indep {first, second, third}
  first_triangle : source.IsCircuit {first, second, firstSecond}
  second_triangle : source.IsCircuit {first, third, firstThird}
  third_triangle : source.IsCircuit {second, third, secondThird}

namespace TriangleFrame

variable (frame : TriangleFrame source)

def baseGround : Set Label := {frame.first, frame.second, frame.third}

def ground : Set Label :=
  insert frame.firstSecond (insert frame.firstThird (insert frame.secondThird frame.baseGround))

theorem ground_subset : frame.ground ⊆ source.E := by
  intro element member
  simp only [ground, baseGround, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact frame.first_triangle.subset_ground (by simp)
  · exact frame.second_triangle.subset_ground (by simp)
  · exact frame.third_triangle.subset_ground (by simp)
  · exact frame.independent.subset_ground (by simp)
  · exact frame.independent.subset_ground (by simp)
  · exact frame.independent.subset_ground (by simp)

theorem baseGround_subset : frame.baseGround ⊆ frame.ground := by
  exact (Set.subset_insert _ _).trans ((Set.subset_insert _ _).trans (Set.subset_insert _ _))

theorem completion_notMem_base [source.Simple] :
    frame.firstSecond ∉ frame.baseGround ∧ frame.firstThird ∉ frame.baseGround ∧
      frame.secondThird ∉ frame.baseGround := by
  have second_independent : source.Indep {frame.first, frame.third, frame.second} := by
    convert frame.independent using 1
    ext element
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have third_independent : source.Indep {frame.second, frame.third, frame.first} := by
    convert frame.independent using 1
    ext element
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  refine ⟨Simple.triangle_completion_notMem_independent_triple frame.independent frame.first_triangle,
    ?_, ?_⟩
  · have absent := Simple.triangle_completion_notMem_independent_triple
      second_independent frame.second_triangle
    intro member
    apply absent
    simp only [baseGround, Set.mem_insert_iff, Set.mem_singleton_iff] at member ⊢
    tauto
  · have absent := Simple.triangle_completion_notMem_independent_triple
      third_independent frame.third_triangle
    intro member
    apply absent
    simp only [baseGround, Set.mem_insert_iff, Set.mem_singleton_iff] at member ⊢
    tauto

theorem completions_distinct [source.Simple] :
    frame.firstSecond ≠ frame.firstThird ∧ frame.firstSecond ≠ frame.secondThird ∧
      frame.firstThird ≠ frame.secondThird := by
  have second_third := (Simple.isCircuit_triple_distinct frame.third_triangle).1
  have first_third := (Simple.isCircuit_triple_distinct frame.second_triangle).1
  have first_second := (Simple.isCircuit_triple_distinct frame.first_triangle).1
  have second_independent : source.Indep {frame.second, frame.first, frame.third} := by
    simpa only [Set.insert_comm] using frame.independent
  have third_independent : source.Indep {frame.third, frame.first, frame.second} := by
    convert frame.independent using 1
    ext element
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have first_rotated : source.IsCircuit {frame.second, frame.first, frame.firstSecond} := by
    simpa only [Set.insert_comm] using frame.first_triangle
  have second_rotated : source.IsCircuit {frame.third, frame.first, frame.firstThird} := by
    simpa only [Set.insert_comm] using frame.second_triangle
  have third_rotated : source.IsCircuit {frame.third, frame.second, frame.secondThird} := by
    simpa only [Set.insert_comm] using frame.third_triangle
  exact ⟨Simple.triangle_completions_distinct frame.independent second_third
    frame.first_triangle frame.second_triangle,
    Simple.triangle_completions_distinct second_independent first_third first_rotated frame.third_triangle,
    Simple.triangle_completions_distinct third_independent first_second second_rotated third_rotated⟩

theorem baseGround_encard [source.Simple] : frame.baseGround.encard = 3 := by
  have first_second := (Simple.isCircuit_triple_distinct frame.first_triangle).1
  have first_third := (Simple.isCircuit_triple_distinct frame.second_triangle).1
  have second_third := (Simple.isCircuit_triple_distinct frame.third_triangle).1
  rw [baseGround, Set.encard_insert_of_notMem (by simp [first_second, first_third]),
    Set.encard_insert_of_notMem (by simpa using second_third), Set.encard_singleton]
  rfl

theorem ground_finite : frame.ground.Finite := by
  unfold ground baseGround
  exact (((((Set.finite_singleton _).insert _).insert _).insert _).insert _).insert _

theorem ground_ncard [source.Simple] : frame.ground.ncard = 6 := by
  have absent := frame.completion_notMem_base
  have distinct := frame.completions_distinct
  have finite_base : frame.baseGround.Finite :=
    ((Set.finite_singleton _).insert _).insert _
  have base_count : frame.baseGround.ncard = 3 := by
    rw [Set.ncard_def, frame.baseGround_encard]
    rfl
  rw [ground, Set.ncard_insert_of_notMem (by simp [distinct.1, distinct.2.1, absent.1])
      ((finite_base.insert _).insert _),
    Set.ncard_insert_of_notMem (by simp [distinct.2.2, absent.2.1]) (finite_base.insert _),
    Set.ncard_insert_of_notMem absent.2.2 finite_base, base_count]

theorem ground_subset_closure_base [source.Simple] : frame.ground ⊆ source.closure frame.baseGround := by
  have first_closure := Simple.triangle_completion_mem_closure frame.first_triangle
  have second_closure := Simple.triangle_completion_mem_closure frame.second_triangle
  have third_closure := Simple.triangle_completion_mem_closure frame.third_triangle
  have first_subset : ({frame.first, frame.second} : Set Label) ⊆ frame.baseGround := by
    simp [baseGround, Set.subset_def]
  have second_subset : ({frame.first, frame.third} : Set Label) ⊆ frame.baseGround := by
    simp [baseGround, Set.subset_def]
  have third_subset : ({frame.second, frame.third} : Set Label) ⊆ frame.baseGround := by
    simp [baseGround, Set.subset_def]
  intro element member
  simp only [ground, Set.mem_insert_iff] at member
  rcases member with rfl | rfl | rfl | member
  · exact source.closure_mono first_subset first_closure
  · exact source.closure_mono second_subset second_closure
  · exact source.closure_mono third_subset third_closure
  · exact source.subset_closure frame.baseGround frame.independent.subset_ground member

theorem isBasis_ground [source.Simple] : source.IsBasis frame.baseGround frame.ground :=
  frame.independent.isBasis_of_subset_of_subset_closure frame.baseGround_subset
    frame.ground_subset_closure_base

theorem restriction_rank [source.Simple] : (source.restrict frame.ground).eRank = 3 := by
  rw [source.eRank_restrict, frame.isBasis_ground.eRk_eq_encard, frame.baseGround_encard]

theorem restriction_simple [source.Simple] : (source.restrict frame.ground).Simple := by
  apply simple_iff_forall_pair_indep.mpr
  intro first second first_member second_member
  rw [restrict_indep_iff]
  exact ⟨simple_iff_forall_pair_indep.mp (inferInstance : source.Simple) first second
    (frame.ground_subset first_member) (frame.ground_subset second_member),
    Set.pair_subset first_member second_member⟩

theorem restriction_iso_graph_k4 [source.Simple] (binary : source.Representable (ZMod 2)) :
    Nonempty (Iso (source.restrict frame.ground) BondalThomsen.k4GraphCycleMatroid) := by
  let : (source.restrict frame.ground).Finite := ⟨frame.ground_finite⟩
  let : (source.restrict frame.ground).Simple := frame.restriction_simple
  exact binary_simple_rank_three_six_iso_graph_k4 (binary.restrict frame.ground)
    frame.restriction_rank frame.ground_ncard

include frame in
theorem has_graph_k4_minor [source.Simple] (binary : source.Representable (ZMod 2)) :
    ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
  obtain ⟨isomorphism⟩ := frame.restriction_iso_graph_k4 binary
  exact ⟨source.restrict frame.ground,
    (source.restrict_isRestriction frame.ground frame.ground_subset).isMinor, ⟨isomorphism.symm⟩⟩

end TriangleFrame

theorem Simple.binary_triangle_completion_unique [source.Simple]
    (binary : source.Representable (ZMod 2))
    (first_triangle : source.IsCircuit {first, second, completion})
    (second_triangle : source.IsCircuit {first, second, otherCompletion}) :
    completion = otherCompletion := by
  classical
  by_contra distinct
  obtain ⟨first_second, first_completion, second_completion⟩ :=
    Simple.isCircuit_triple_distinct first_triangle
  obtain ⟨_, first_other, second_other⟩ := Simple.isCircuit_triple_distinct second_triangle
  let selected : Set Label := insert completion (insert otherCompletion {first, second})
  have pair_finite : ({first, second} : Set Label).Finite := (Set.finite_singleton _).insert _
  have selected_finite : selected.Finite := (pair_finite.insert _).insert _
  have selected_subset : selected ⊆ source.E := by
    intro element member
    simp only [selected, Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact first_triangle.subset_ground (by simp)
    · exact second_triangle.subset_ground (by simp)
    · exact first_triangle.subset_ground (by simp)
    · exact first_triangle.subset_ground (by simp)
  let : (source.restrict selected).Finite := ⟨selected_finite⟩
  let : (source.restrict selected).Simple := by
    apply simple_iff_forall_pair_indep.mpr
    intro first second first_member second_member
    rw [restrict_indep_iff]
    exact ⟨simple_iff_forall_pair_indep.mp (inferInstance : source.Simple) first second
      (selected_subset first_member) (selected_subset second_member),
      Set.pair_subset first_member second_member⟩
  have selected_closure : selected ⊆ source.closure {first, second} := by
    intro element member
    simp only [selected, Set.mem_insert_iff] at member
    rcases member with rfl | rfl | member
    · exact Simple.triangle_completion_mem_closure first_triangle
    · exact Simple.triangle_completion_mem_closure second_triangle
    · exact source.subset_closure _ (Set.pair_subset
        (first_triangle.subset_ground (by simp))
        (first_triangle.subset_ground (by simp))) member
  have rank : (source.restrict selected).eRank ≤ 2 := by
    calc
      (source.restrict selected).eRank = source.eRk selected := source.eRank_restrict selected
      _ ≤ source.eRk (source.closure {first, second}) := source.eRk_mono selected_closure
      _ = source.eRk {first, second} := source.eRk_closure_eq _
      _ ≤ ({first, second} : Set Label).encard := source.eRk_le_encard _
      _ = 2 := Set.encard_pair first_second
  have count : selected.ncard = 4 := by
    change (insert completion (insert otherCompletion ({first, second} : Set Label))).ncard = 4
    rw [Set.ncard_insert_of_notMem
      (by simp [distinct, Ne.symm first_completion, Ne.symm second_completion])
      (pair_finite.insert _),
      Set.ncard_insert_of_notMem (by simp [Ne.symm first_other, Ne.symm second_other])
        pair_finite, Set.ncard_pair first_second]
  have bound := binary_simple_rank_two_ground_card_le_three (binary.restrict selected) rank
  change selected.ncard ≤ 3 at bound
  omega

theorem ConnectedTriangleTriadProfile.two_triangles_of_connected_contract
    [source.Simple] (binary : source.Representable (ZMod 2))
    (profile : ConnectedTriangleTriadProfile source) {removed : Label}
    (removed_member : removed ∈ source.E) (connected : (source.contract {removed}).Connected) :
    ∃ first ∈ source.E \ {removed}, ∃ second ∈ source.E \ {removed},
      ∃ otherFirst ∈ source.E \ {removed}, ∃ otherSecond ∈ source.E \ {removed},
        first ≠ second ∧ otherFirst ≠ otherSecond ∧
        otherFirst ≠ first ∧ otherFirst ≠ second ∧
        otherSecond ≠ first ∧ otherSecond ≠ second ∧
        source.IsCircuit {removed, first, second} ∧
        source.IsCircuit {removed, otherFirst, otherSecond} := by
  obtain ⟨basepoint, member⟩ := connected.nonempty.ground_nonempty
  obtain ⟨first, first_member, second, second_member, distinct, _, _, triangle⟩ :=
    (profile removed removed_member).1 connected basepoint member
  obtain ⟨otherFirst, otherFirst_member, otherSecond, otherSecond_member, other_distinct,
    first_avoids, second_avoids, other_triangle⟩ :=
    (profile removed removed_member).1 connected first first_member
  have first_avoids_second : otherFirst ≠ second := by
    intro same
    subst otherFirst
    have rotated : source.IsCircuit {removed, second, first} := by
      convert triangle using 1
      ext element
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact second_avoids (Simple.binary_triangle_completion_unique binary other_triangle rotated)
  have second_avoids_second : otherSecond ≠ second := by
    intro same
    subst otherSecond
    have rotated : source.IsCircuit {removed, second, otherFirst} := by
      convert other_triangle using 1
      ext element
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have original_rotated : source.IsCircuit {removed, second, first} := by
      convert triangle using 1
      ext element
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact first_avoids (Simple.binary_triangle_completion_unique binary rotated original_rotated)
  exact ⟨first, first_member, second, second_member, otherFirst, otherFirst_member,
    otherSecond, otherSecond_member, distinct, other_distinct, first_avoids,
    first_avoids_second, second_avoids, second_avoids_second, triangle, other_triangle⟩

theorem Simple.isCircuit_triple_of_dep [source.Simple]
    (dependent : source.Dep {first, second, third}) : source.IsCircuit {first, second, third} := by
  have first_member : first ∈ source.E := dependent.subset_ground (by simp)
  have second_member : second ∈ source.E := dependent.subset_ground (by simp)
  have third_member : third ∈ source.E := dependent.subset_ground (by simp)
  have pairs := simple_iff_forall_pair_indep.mp (inferInstance : source.Simple)
  apply isCircuit_iff_dep_forall_sdiff_singleton_indep.mpr
  refine ⟨dependent, ?_⟩
  intro removed member
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl
  · apply (pairs second third second_member third_member).subset
    intro element member
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at member ⊢
    tauto
  · apply (pairs first third first_member third_member).subset
    intro element member
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at member ⊢
    tauto
  · apply (pairs first second first_member second_member).subset
    intro element member
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at member ⊢
    tauto

theorem Simple.binary_two_triangles_independent [source.Simple]
    (binary : source.Representable (ZMod 2))
    (first_triangle : source.IsCircuit {first, second, completion})
    (second_triangle : source.IsCircuit {first, third, otherCompletion})
    (third_avoids : third ≠ completion) : source.Indep {first, second, third} := by
  by_contra not_independent
  have ground_subset : ({first, second, third} : Set Label) ⊆ source.E :=
    Set.insert_subset (first_triangle.subset_ground (by simp))
      (Set.pair_subset (first_triangle.subset_ground (by simp))
        (second_triangle.subset_ground (by simp)))
  have triangle := Simple.isCircuit_triple_of_dep ((not_indep_iff ground_subset).mp not_independent)
  exact third_avoids (Simple.binary_triangle_completion_unique binary triangle first_triangle)

theorem ConnectedTriangleTriadProfile.independent_two_triangles_of_connected_contract
    [source.Simple] (binary : source.Representable (ZMod 2))
    (profile : ConnectedTriangleTriadProfile source) {removed : Label}
    (removed_member : removed ∈ source.E) (connected : (source.contract {removed}).Connected) :
    ∃ first ∈ source.E \ {removed}, ∃ second ∈ source.E \ {removed},
      ∃ otherFirst ∈ source.E \ {removed}, ∃ otherSecond ∈ source.E \ {removed},
        first ≠ second ∧ otherFirst ≠ otherSecond ∧
        otherFirst ≠ first ∧ otherFirst ≠ second ∧
        otherSecond ≠ first ∧ otherSecond ≠ second ∧
        source.Indep {removed, first, otherFirst} ∧
        source.IsCircuit {removed, first, second} ∧
        source.IsCircuit {removed, otherFirst, otherSecond} := by
  obtain ⟨first, first_member, second, second_member, otherFirst, otherFirst_member,
    otherSecond, otherSecond_member, distinct, other_distinct, first_avoids,
    first_avoids_second, second_avoids, second_avoids_second, triangle, other_triangle⟩ :=
    profile.two_triangles_of_connected_contract binary removed_member connected
  exact ⟨first, first_member, second, second_member, otherFirst, otherFirst_member,
    otherSecond, otherSecond_member, distinct, other_distinct, first_avoids,
    first_avoids_second, second_avoids, second_avoids_second,
    Simple.binary_two_triangles_independent binary triangle other_triangle first_avoids_second,
    triangle, other_triangle⟩

end Matroid
