module

public import BondalThomsen.Matroid.Binary.K4ExcludedGeneralReduction
public import BondalThomsen.DeepFan.ElementaryClassification
public import BondalThomsen.Matroid.ConnectedComponents
public import BondalThomsen.Matroid.ConnectedMatroidForestReconstruction

@[expose] public section

namespace Matroid

open Set

theorem disjointSigma_dual_eq {Label Component : Type*}
    (sources : Component → Matroid Label)
    (disjoint : Pairwise (fun first second => Disjoint (sources first).E (sources second).E)) :
    (Matroid.disjointSigma sources disjoint)✶ =
      Matroid.disjointSigma (fun component => (sources component)✶)
        (by simpa only [Matroid.dual_ground] using disjoint) := by
  apply Matroid.ext_isBase (by simp)
  intro selected subset_ground
  rw [dual_ground, disjointSigma_ground_eq] at subset_ground
  rw [dual_isBase_iff (by simpa only [disjointSigma_ground_eq] using subset_ground),
    disjointSigma_isBase_iff, disjointSigma_isBase_iff]
  have complement_subset : (⋃ component, (sources component).E) \ selected ⊆
      ⋃ component, (sources component).E := Set.sdiff_subset
  simp only [dual_ground]
  rw [disjointSigma_ground_eq, and_iff_left complement_subset, and_iff_left subset_ground]
  apply forall_congr'
  intro component
  rw [dual_isBase_iff Set.inter_subset_right]
  apply Iff.of_eq
  apply congrArg (sources component).IsBase
  ext label
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨_, absent⟩, member⟩
    exact ⟨member, fun contained => absent contained.1⟩
  · rintro ⟨member, absent⟩
    exact ⟨⟨⟨component, member⟩, fun contained => absent ⟨contained, member⟩⟩, member⟩

theorem disjointSigma_restrict_component {Label Component : Type*}
    (sources : Component → Matroid Label)
    (disjoint : Pairwise (fun first second => Disjoint (sources first).E (sources second).E))
    (component : Component) :
    (Matroid.disjointSigma sources disjoint).restrict (sources component).E = sources component := by
  apply Matroid.ext_indep (by simp)
  intro selected subset_ground
  change selected ⊆ (sources component).E at subset_ground
  rw [restrict_indep_iff, disjointSigma_indep_iff, and_iff_left subset_ground]
  have union_subset : selected ⊆ ⋃ component, (sources component).E :=
    subset_ground.trans (Set.subset_iUnion (fun component => (sources component).E) component)
  rw [and_iff_left union_subset]
  constructor
  · intro independent
    simpa only [Set.inter_eq_left.mpr subset_ground] using independent component
  · intro independent other
    by_cases same : other = component
    · subst other
      simpa only [Set.inter_eq_left.mpr subset_ground] using independent
    · have intersection_empty : selected ∩ (sources other).E = ∅ := by
        apply Set.disjoint_iff_inter_eq_empty.mp
        exact (disjoint same).symm.mono_left subset_ground
      rw [intersection_empty]
      exact (sources other).empty_indep

theorem componentMatroid_dual_eq {Label : Type*} (source : Matroid Label)
    (component : source.ConnectedComponent) :
    (source.componentMatroid component)✶ = source✶.restrict component.val := by
  have equality := congrArg (fun candidate : Matroid Label => candidate✶.restrict component.val)
    source.eq_componentMatroid_disjointSigma
  rw [equality, disjointSigma_dual_eq]
  exact (disjointSigma_restrict_component (fun component => (source.componentMatroid component)✶)
    (by simpa only [Matroid.dual_ground] using source.componentMatroid_pairwise_disjoint) component).symm

theorem component_parallel_of_pair {Label : Type*} {source : Matroid Label}
    (component : source.ConnectedComponent) {first second : Label}
    (parallel : (source.componentMatroid component).Parallel first second) :
    source.Parallel first second :=
  parallel.of_isRestriction
    (source.restrict_isRestriction component.val (source.component_subset_ground component))

theorem component_series_of_pair {Label : Type*} {source : Matroid Label}
    (component : source.ConnectedComponent) {first second : Label}
    (series : (source.componentMatroid component)✶.Parallel first second) :
    source✶.Parallel first second := by
  rw [source.componentMatroid_dual_eq component] at series
  exact series.of_isRestriction (source✶.restrict_isRestriction component.val
    (by simpa only [dual_ground] using source.component_subset_ground component))

theorem component_isColoop {Label : Type*} {source : Matroid Label}
    (component : source.ConnectedComponent) {element : Label}
    (coloop : (source.componentMatroid component).IsColoop element) : source.IsColoop element := by
  apply isColoop_iff_forall_mem_isBase.mpr
  intro basis property
  have component_basis : (source.componentMatroid component).IsBase
      (basis ∩ (source.componentMatroid component).E) := by
    have decomposition : (Matroid.disjointSigma source.componentMatroid
        source.componentMatroid_pairwise_disjoint).IsBase basis :=
      source.eq_componentMatroid_disjointSigma ▸ property
    exact (disjointSigma_isBase_iff.mp decomposition).1 component
  exact (coloop.mem_of_isBase component_basis).1

theorem connected_pair_exists_of_triangle_triad_minor_lemma {Label : Type*}
    (minor_lemma : BinaryConnectedTriangleTriadK4MinorLemma Label) {source : Matroid Label}
    [source.Finite] (connected : source.Connected) (binary : source.Representable (ZMod 2))
    (lower : 2 ≤ source.E.ncard)
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate)) :
    ∃ first second, first ≠ second ∧ (source.Parallel first second ∨ source✶.Parallel first second) := by
  classical
  let := source.ground_finite.to_subtype
  obtain ⟨marked, member⟩ := connected.nonempty.ground_nonempty
  by_cases two : source.E.ncard = 2
  · have nontrivial : source.E.Nontrivial := Set.one_lt_ncard_iff_nontrivial.mp (by omega)
    obtain ⟨other, other_member, distinct⟩ := nontrivial.exists_ne marked
    have pair_ground : source.E = {marked, other} := by
      exact (Set.eq_of_subset_of_ncard_le (Set.pair_subset member other_member)
        (by rw [two, Set.ncard_pair distinct.symm]) source.ground_finite).symm
    have circuit : source.IsCircuit {marked, other} := by
      obtain ⟨circuit, property, marked_circuit, other_circuit⟩ :=
        connected.exists_isCircuit_of_ne member other_member distinct.symm
      have equality : circuit = {marked, other} := Set.Subset.antisymm
        (property.subset_ground.trans pair_ground.subset) (Set.pair_subset marked_circuit other_circuit)
      exact equality ▸ property
    exact ⟨marked, other, distinct.symm, Or.inl (circuit.parallel_of_pair distinct.symm)⟩
  · have lower_three : 3 ≤ source.E.ncard := by omega
    obtain ⟨first, _, second, _, distinct, _, _, pair⟩ :=
      connected_binary_pair_avoiding_of_triangle_triad_minor_lemma minor_lemma connected binary
        lower_three excluded member
    exact ⟨first, second, distinct, pair⟩

theorem binary_k4_excluded_elementary_reducibility_of_triangle_triad_minor_lemma
    {Label : Type*} (minor_lemma : BinaryConnectedTriangleTriadK4MinorLemma Label) :
    BondalThomsen.BinaryK4ExcludedElementaryReducibility Label := by
  intro source finite_source binary excluded nonempty
  let := finite_source
  by_cases loopless : source.Loopless
  · let := loopless
    obtain ⟨element, member⟩ := nonempty
    let component : source.ConnectedComponent :=
      ⟨source.connectedComponentSet ⟨element, member⟩, ⟨⟨element, member⟩, rfl⟩⟩
    let smaller := source.componentMatroid component
    have connected : smaller.Connected := source.componentMatroid_connected component
    let : smaller.Loopless :=
      (source.restrict_isRestriction component.val (source.component_subset_ground component)).loopless
    have component_member : element ∈ smaller.E := connectedTo_self member
    by_cases singleton_size : smaller.E.ncard = 1
    · have ground_eq : smaller.E = {element} := by
        obtain ⟨only, ground⟩ := Set.ncard_eq_one.mp singleton_size
        have same : element = only := by simpa only [ground, Set.mem_singleton_iff] using component_member
        simpa only [← same] using ground
      have coloop : smaller.IsColoop element := by
        have independent := (Matroid.isNonloop_of_loopless component_member).indep
        have ground_base : smaller.IsBase smaller.E := ground_indep_iff_isBase.mp (ground_eq ▸ independent)
        apply isColoop_iff_forall_mem_isBase.mpr
        intro basis property
        have basis_eq := property.eq_of_subset_isBase ground_base property.subset_ground
        exact basis_eq.symm ▸ component_member
      exact ⟨source.delete {element}, .coloop element (component_isColoop component coloop)⟩
    · have positive := connected.nonempty.ground_nonempty.ncard_pos smaller.ground_finite
      have lower : 2 ≤ smaller.E.ncard := by omega
      have minor := (source.restrict_isRestriction component.val
        (source.component_subset_ground component)).isMinor
      have component_excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m smaller ∧
          Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
        rintro ⟨candidate, candidate_minor, isomorphism⟩
        exact excluded ⟨candidate, candidate_minor.trans minor, isomorphism⟩
      obtain ⟨first, second, distinct, pair⟩ :=
        connected_pair_exists_of_triangle_triad_minor_lemma minor_lemma connected
          (binary.of_isMinor minor) lower component_excluded
      rcases pair with parallel | series
      · exact ⟨source.delete {first}, .parallel first second distinct
          (component_parallel_of_pair component parallel)⟩
      · exact ⟨source.contract {first}, .series first second distinct
          (component_series_of_pair component series)⟩
  · apply exists_elementary_reduction_of_not_simple_or_dual
    left
    intro simple
    let := simple
    exact loopless (loopless_iff_forall_isNonloop.mpr (fun label member =>
      ((Simple.parallel_iff_eq member).mpr rfl).1))

theorem binary_exists_canonical_source_forest_of_triangle_triad_minor_lemma
    {Label : Type*} [DecidableEq Label]
    (minor_lemma : BinaryConnectedTriangleTriadK4MinorLemma Label) {source : Matroid Label}
    [source.Finite] [source.Loopless] (binary : source.Representable (ZMod 2))
    (excluded : ¬ ∃ candidate : Matroid Label, candidate ≤m source ∧
      Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate)) :
    Nonempty (BondalThomsen.ConnectedComponentForest source) := by
  apply exists_connectedComponentForest
  intro component lower
  have minor := (source.restrict_isRestriction component.val
    (source.component_subset_ground component)).isMinor
  have component_excluded : ¬ ∃ candidate : Matroid Label,
      candidate ≤m source.componentMatroid component ∧
        Nonempty (Iso BondalThomsen.k4GraphCycleMatroid candidate) := by
    rintro ⟨candidate, candidate_minor, isomorphism⟩
    exact excluded ⟨candidate, candidate_minor.trans minor, isomorphism⟩
  obtain ⟨marked, member⟩ := (source.componentMatroid_connected component).nonempty.ground_nonempty
  obtain ⟨target, size, _, _, _, _, _, _, trace⟩ :=
    connected_binary_marked_trace_of_triangle_triad_minor_lemma minor_lemma
      (source.componentMatroid_connected component) (binary.of_isMinor minor)
      lower component_excluded member
  exact ⟨marked, target, _, size, trace⟩

end Matroid
