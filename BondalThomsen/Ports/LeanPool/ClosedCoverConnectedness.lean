module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open scoped Classical

theorem IsPreconnected.transGen_of_finite_iUnion
    {Space Index : Type*} [TopologicalSpace Space] [Finite Index]
    {patches : Index → Set Space}
    (connected : IsPreconnected (⋃ index, patches index))
    (closed : ∀ index, IsClosed (patches index))
    (first second : Index) (firstNonempty : (patches first).Nonempty)
    (secondNonempty : (patches second).Nonempty) :
    Relation.TransGen (fun source target => (patches source ∩ patches target).Nonempty)
      first second := by
  by_contra notReachable
  let relation := fun source target : Index => (patches source ∩ patches target).Nonempty
  let reachable : Set Index := {index | Relation.TransGen relation first index}
  let leftRegion : Set Space := ⋃ index ∈ reachable, patches index
  let rightRegion : Set Space := ⋃ index ∈ reachableᶜ, patches index
  have leftClosed : IsClosed leftRegion :=
    (Set.toFinite reachable).isClosed_biUnion (fun index _ => closed index)
  have rightClosed : IsClosed rightRegion :=
    (Set.toFinite reachableᶜ).isClosed_biUnion (fun index _ => closed index)
  have split : (⋃ index, patches index) = leftRegion ∪ rightRegion :=
    iSup_split patches (· ∈ reachable)
  have disjoint : Disjoint leftRegion rightRegion := by
    rw [Set.disjoint_left]
    intro point onLeft onRight
    simp only [Set.mem_iUnion, exists_prop, Set.mem_compl_iff, leftRegion, rightRegion] at onLeft onRight
    obtain ⟨leftIndex, reachableLeft, containsLeft⟩ := onLeft
    obtain ⟨rightIndex, unreachableRight, containsRight⟩ := onRight
    exact unreachableRight (reachableLeft.tail ⟨point, containsLeft, containsRight⟩)
  obtain ⟨leftPoint, containsLeft⟩ := firstNonempty
  obtain ⟨rightPoint, containsRight⟩ := secondNonempty
  have firstReachable : first ∈ reachable := Relation.TransGen.single ⟨leftPoint, containsLeft, containsLeft⟩
  have leftOnLeft : leftPoint ∈ leftRegion := Set.mem_iUnion₂_of_mem firstReachable containsLeft
  have secondUnreachable : second ∉ reachable := notReachable
  have rightOnRight : rightPoint ∈ rightRegion := Set.mem_iUnion₂_of_mem secondUnreachable containsRight
  have cover : (⋃ index, patches index) ⊆ rightRegionᶜ ∪ leftRegionᶜ := by
    intro point covered
    rcases split.le covered with onLeft | onRight
    · exact Or.inl (fun onRight => Set.disjoint_left.mp disjoint onLeft onRight)
    · exact Or.inr (fun onLeft => Set.disjoint_left.mp disjoint onLeft onRight)
  have leftNonempty : ((⋃ index, patches index) ∩ rightRegionᶜ).Nonempty :=
    ⟨leftPoint, Set.mem_iUnion_of_mem first containsLeft,
      fun onRight => Set.disjoint_left.mp disjoint leftOnLeft onRight⟩
  have rightNonempty : ((⋃ index, patches index) ∩ leftRegionᶜ).Nonempty :=
    ⟨rightPoint, Set.mem_iUnion_of_mem second containsRight,
      fun onLeft => Set.disjoint_left.mp disjoint onLeft rightOnRight⟩
  obtain ⟨point, covered, notRight, notLeft⟩ := connected rightRegionᶜ leftRegionᶜ
    rightClosed.isOpen_compl leftClosed.isOpen_compl cover leftNonempty rightNonempty
  rcases split.le covered with onLeft | onRight
  · exact notLeft onLeft
  · exact notRight onRight
