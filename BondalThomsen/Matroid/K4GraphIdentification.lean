module

public import BondalThomsen.Matroid.RootMatroid
public import BondalThomsen.Matroid.UnimodularRepresentations
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace BondalThomsen

open Matrix Finset

def k4SelectedGraph (selected : Finset (Fin 6)) : SimpleGraph (Fin 4) where
  Adj source target := ∃ edge ∈ selected,
    (k4EdgeSource edge = source ∧ k4EdgeTarget edge = target) ∨
      (k4EdgeSource edge = target ∧ k4EdgeTarget edge = source)
  symm := ⟨by
    intro source target
    rintro ⟨edge, member, endpoints⟩
    exact ⟨edge, member, endpoints.symm⟩⟩
  loopless := ⟨by
    intro source
    rintro ⟨edge, _, endpoints⟩
    have distinct := (k4EdgeSource_lt_target edge).ne
    rcases endpoints with endpoints | endpoints <;>
      exact distinct (endpoints.1.trans endpoints.2.symm)⟩

instance (selected : Finset (Fin 6)) : DecidableRel (k4SelectedGraph selected).Adj := by
  unfold k4SelectedGraph
  infer_instance

def k4GraphEdge (edge : Fin 6) : Sym2 (Fin 4) :=
  s(k4EdgeSource edge, k4EdgeTarget edge)

theorem k4GraphEdge_injective : Function.Injective k4GraphEdge := by
  intro first second equality
  have endpoints := Sym2.eq_iff.mp equality
  fin_cases first <;> fin_cases second <;>
    simp_all [k4EdgeSource, k4EdgeTarget]

theorem k4GraphEdge_mem_edgeSet (edge : Fin 6) :
    k4GraphEdge edge ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet := by
  exact (SimpleGraph.mem_edgeSet _).mpr (k4EdgeSource_lt_target edge).ne

theorem k4GraphEdge_surjective :
    Function.Surjective (fun edge : Fin 6 =>
      (⟨k4GraphEdge edge, k4GraphEdge_mem_edgeSet edge⟩ :
        (⊤ : SimpleGraph (Fin 4)).edgeSet)) := by
  have exhaustive : ∀ unordered : Sym2 (Fin 4),
      unordered ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet →
        ∃ edge, k4GraphEdge edge = unordered := by
    intro unordered
    induction unordered using Sym2.inductionOn with
    | _ source target =>
      intro member
      have distinct : source ≠ target := (SimpleGraph.mem_edgeSet _).mp member
      obtain ⟨edge, endpoints⟩ := k4Edge_endpoints_exhaustive source target distinct
      exact ⟨edge, Sym2.eq_iff.mpr endpoints⟩
  rintro ⟨unordered, member⟩
  obtain ⟨edge, equality⟩ := exhaustive unordered member
  exact ⟨edge, Subtype.ext equality⟩

noncomputable def k4GraphEdgeEquiv : Fin 6 ≃ (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  Equiv.ofBijective (fun edge => ⟨k4GraphEdge edge, k4GraphEdge_mem_edgeSet edge⟩)
    ⟨fun _ _ equality => k4GraphEdge_injective (congrArg Subtype.val equality),
      k4GraphEdge_surjective⟩

@[simp] theorem k4GraphEdgeEquiv_val (edge : Fin 6) :
    (k4GraphEdgeEquiv edge).val = k4GraphEdge edge := rfl

def k4FiniteForest (selected : Finset (Fin 6)) : Prop :=
  (∀ mapping : Fin 3 → Fin 4, Function.Injective mapping →
    ¬∀ source target, (SimpleGraph.cycleGraph 3).Adj source target →
      (k4SelectedGraph selected).Adj (mapping source) (mapping target)) ∧
  (∀ mapping : Fin 4 → Fin 4, Function.Injective mapping →
    ¬∀ source target, (SimpleGraph.cycleGraph 4).Adj source target →
      (k4SelectedGraph selected).Adj (mapping source) (mapping target))

private theorem free_iff_no_copy_function {Source Target : Type*}
    (sourceGraph : SimpleGraph Source) (targetGraph : SimpleGraph Target) :
    sourceGraph.Free targetGraph ↔
      ∀ mapping : Source → Target, Function.Injective mapping →
        ¬∀ source target, sourceGraph.Adj source target →
          targetGraph.Adj (mapping source) (mapping target) := by
  constructor
  · intro free mapping injective preserves
    exact free ⟨⟨⟨mapping, fun adjacency => preserves _ _ adjacency⟩, injective⟩⟩
  · rintro noCopy ⟨copy⟩
    exact noCopy copy copy.injective (fun _ _ adjacency => copy.toHom.map_rel adjacency)

theorem k4FiniteForest_iff_isAcyclic (selected : Finset (Fin 6)) :
    k4FiniteForest selected ↔ (k4SelectedGraph selected).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  constructor
  · rintro ⟨noTriangle, noSquare⟩ size size_ge_three
    by_cases size_le_four : size ≤ 4
    · have alternatives : size = 3 ∨ size = 4 := by omega
      rcases alternatives with rfl | rfl
      · exact (free_iff_no_copy_function _ _).mpr noTriangle
      · exact (free_iff_no_copy_function _ _).mpr noSquare
    · rintro ⟨copy⟩
      have bound := Fintype.card_le_of_injective copy copy.injective
      simp only [Fintype.card_fin] at bound
      exact size_le_four bound
  · intro acyclic
    exact ⟨(free_iff_no_copy_function _ _).mp (acyclic 3 (by omega)),
      (free_iff_no_copy_function _ _).mp (acyclic 4 (by omega))⟩

def k4BinaryIndependent (selected : Finset (Fin 6)) : Prop :=
  ∀ coefficients : Fin 6 → ZMod 2,
    (∑ edge ∈ selected, coefficients edge • (k4RootMatrix (ZMod 2)).col edge) = 0 →
      ∀ edge ∈ selected, coefficients edge = 0

private instance (selected : Finset (Fin 6)) : Decidable (k4FiniteForest selected) := by
  unfold k4FiniteForest
  infer_instance

private instance (selected : Finset (Fin 6)) : Decidable (k4BinaryIndependent selected) := by
  unfold k4BinaryIndependent
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

theorem k4BinaryIndependent_iff_finiteForest :
    ∀ selected, k4BinaryIndependent selected ↔ k4FiniteForest selected := by
  decide +kernel

theorem k4BinaryIndependent_iff_linearIndepOn (selected : Finset (Fin 6)) :
    k4BinaryIndependent selected ↔
      LinearIndepOn (ZMod 2) (k4RootMatrix (ZMod 2)).col (selected : Set (Fin 6)) := by
  rw [linearIndepOn_iff']
  constructor
  · intro independent subset coefficients subset_selected zero_sum edge member
    let extended : Fin 6 → ZMod 2 := fun index =>
      if index ∈ subset then coefficients index else 0
    have extended_sum :
        (∑ index ∈ selected, extended index • (k4RootMatrix (ZMod 2)).col index) = 0 := by
      have subset_finset : subset ⊆ selected := subset_selected
      simpa [extended, ite_smul, Finset.sum_ite_mem, inter_eq_right.mpr subset_finset]
        using zero_sum
    have coefficient_zero := independent extended extended_sum edge (subset_selected member)
    simpa [extended, member] using coefficient_zero
  · intro independent coefficients zero_sum
    exact independent selected coefficients (by rfl) zero_sum

theorem k4_binary_linearIndepOn_iff_isAcyclic (selected : Finset (Fin 6)) :
    LinearIndepOn (ZMod 2) (k4RootMatrix (ZMod 2)).col (selected : Set (Fin 6)) ↔
      (k4SelectedGraph selected).IsAcyclic :=
  (k4BinaryIndependent_iff_linearIndepOn selected).symm.trans
    ((k4BinaryIndependent_iff_finiteForest selected).trans
      (k4FiniteForest_iff_isAcyclic selected))

private theorem k4RootMatrix_int_cast (Field : Type*) [_root_.Field Field] :
    (fun edge row => ((k4RootMatrix ℤ) row edge : Field)) = (k4RootMatrix Field).col := by
  funext edge row
  fin_cases row <;> fin_cases edge <;> simp [k4RootMatrix]

theorem k4Matroid_indep_iff_field (Field : Type*) [_root_.Field Field]
    (selected : Set (Fin 6)) :
    k4Matroid.Indep selected ↔ LinearIndepOn Field (k4RootMatrix Field).col selected := by
  have matroids := totallyUnimodular_cast_rayMatroid (Field := Field)
    (k4RootMatrix ℤ) k4RootMatrix_totallyUnimodular
  rw [k4RootMatrix_int_cast Field, k4RootMatrix_int_cast ℚ] at matroids
  change (rayMatroid (Field := ℚ) (k4RootMatrix ℚ).col).Indep selected ↔ _
  rw [← matroids, rayMatroid_indep_iff]

theorem k4Matroid_indep_iff_isAcyclic_finset (selected : Finset (Fin 6)) :
    k4Matroid.Indep (selected : Set (Fin 6)) ↔ (k4SelectedGraph selected).IsAcyclic :=
  (k4Matroid_indep_iff_field (ZMod 2) _).trans
    (k4_binary_linearIndepOn_iff_isAcyclic selected)

open Classical in

theorem k4Matroid_indep_iff_isAcyclic (selected : Set (Fin 6)) :
    k4Matroid.Indep selected ↔ (k4SelectedGraph selected.toFinset).IsAcyclic := by
  simpa using k4Matroid_indep_iff_isAcyclic_finset selected.toFinset

open Classical in

noncomputable def k4CycleMatroid : Matroid (Fin 6) :=
  k4Matroid.copyIndep Set.univ
    (fun selected => (k4SelectedGraph selected.toFinset).IsAcyclic)
    k4Matroid_ground.symm (fun selected => (k4Matroid_indep_iff_isAcyclic selected).symm)

@[simp] theorem k4CycleMatroid_ground : k4CycleMatroid.E = Set.univ := rfl

theorem k4Matroid_eq_cycleMatroid : k4Matroid = k4CycleMatroid := by
  apply Matroid.ext_indep (by simp)
  intro selected _
  exact k4Matroid_indep_iff_isAcyclic selected

noncomputable def k4GraphCycleMatroid : Matroid (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  k4CycleMatroid.mapEquiv k4GraphEdgeEquiv

theorem k4Matroid_mapEquiv_eq_graphCycleMatroid :
    k4Matroid.mapEquiv k4GraphEdgeEquiv = k4GraphCycleMatroid := by
  rw [k4Matroid_eq_cycleMatroid]
  rfl

end BondalThomsen
