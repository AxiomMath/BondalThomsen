module

public import BondalThomsen.Fan.RootObstruction
public import BondalThomsen.Matroid.UnimodularCompletion
public import BondalThomsen.Ports.Matroid.Simplification
public import BondalThomsen.Ports.Matroid.RepresentationRank

@[expose] public section

namespace BondalThomsen

open Matrix Module Submodule Set

def k4RootMatrix (Ring : Type*) [CommRing Ring] : Matrix (Fin 3) (Fin 6) Ring :=
  !![1, 0, 0, -1, -1, 0;
     0, 1, 0, 1, 0, -1;
     0, 0, 1, 0, 1, 1]

def k4EdgeSource : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

def k4EdgeTarget : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

theorem k4EdgeSource_lt_target (edge : Fin 6) : k4EdgeSource edge < k4EdgeTarget edge := by
  fin_cases edge <;> decide

theorem k4Edge_endpoints_exhaustive (source target : Fin 4) (distinct : source ≠ target) :
    ∃ edge, (k4EdgeSource edge = source ∧ k4EdgeTarget edge = target) ∨
      (k4EdgeSource edge = target ∧ k4EdgeTarget edge = source) := by
  revert source target
  decide

noncomputable def k4Matroid : Matroid (Fin 6) :=
  rayMatroid (Field := ℚ) (k4RootMatrix ℚ).col

def k4Rep : k4Matroid.Rep ℚ (Fin 3 → ℚ) :=
  Matroid.repOfRays (k4RootMatrix ℚ).col

@[simp] theorem k4Matroid_ground : k4Matroid.E = univ := rayMatroid_ground _

@[simp] theorem k4Matroid_indep_iff (selected : Set (Fin 6)) :
    k4Matroid.Indep selected ↔ LinearIndepOn ℚ (k4RootMatrix ℚ).col selected :=
  rayMatroid_indep_iff _ _

def k4BasisEdges : Fin 3 → Fin 6 := Fin.castAdd 3

theorem k4RootMatrix_basis_block (Ring : Type*) [CommRing Ring] :
    (k4RootMatrix Ring).submatrix id k4BasisEdges = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [k4RootMatrix, k4BasisEdges]

theorem k4RootMatrix_columns_nonzero (edge : Fin 6) : (k4RootMatrix ℚ).col edge ≠ 0 := by
  intro equality
  have coordinate0 := congrFun equality 0
  have coordinate1 := congrFun equality 1
  have coordinate2 := congrFun equality 2
  fin_cases edge <;> simp_all [k4RootMatrix]

theorem k4RootMatrix_smul_eq_imp_eq (first second : Fin 6) (scalar : ℚ)
    (equality : scalar • (k4RootMatrix ℚ).col first = (k4RootMatrix ℚ).col second) :
    first = second := by
  have coordinate0 := congrFun equality 0
  have coordinate1 := congrFun equality 1
  have coordinate2 := congrFun equality 2
  fin_cases first <;> fin_cases second <;> simp_all [k4RootMatrix]

theorem k4Matroid_simple : k4Matroid.Simple := by
  apply Matroid.simple_iff_forall_pair_indep.mpr
  intro first second _ _
  rw [k4Matroid_indep_iff]
  by_cases equal : first = second
  · subst second
    simpa only [Set.pair_eq_singleton] using
      (linearIndepOn_singleton_iff ℚ).mpr (k4RootMatrix_columns_nonzero first)
  · rw [linearIndepOn_pair_iff _ equal (k4RootMatrix_columns_nonzero first)]
    intro scalar equality
    exact equal (k4RootMatrix_smul_eq_imp_eq first second scalar equality)

theorem k4Rep_span_eq_top : span ℚ (Set.range k4Rep) = ⊤ := by
  have contained : Set.range (Pi.basisFun ℚ (Fin 3)) ⊆ Set.range k4Rep := by
    rintro _ ⟨index, rfl⟩
    refine ⟨k4BasisEdges index, ?_⟩
    ext row
    change k4RootMatrix ℚ row (k4BasisEdges index) = (Pi.basisFun ℚ (Fin 3)) index row
    have entry := congrFun (congrFun (k4RootMatrix_basis_block ℚ) row) index
    simpa [Matrix.one_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm] using entry
  apply top_unique
  rw [← (Pi.basisFun ℚ (Fin 3)).span_eq]
  exact span_mono contained

theorem k4Matroid_eRank : k4Matroid.eRank = 3 := by
  have rank := k4Rep.finrank_span_range_eq_eRank_toNat
  rw [k4Rep_span_eq_top, finrank_top, Module.finrank_pi, Fintype.card_fin] at rank
  have finite_rank : k4Matroid.eRank ≠ ⊤ := k4Matroid.eRank_ne_top_iff.mpr inferInstance
  exact (ENat.natCast_toNat finite_rank).symm.trans (congrArg Nat.cast rank.symm)

theorem k4RootMatrix_full_minors (columns : Fin 3 → Fin 6) :
    ((k4RootMatrix ℤ).submatrix id columns).det ∈ Set.range SignType.cast := by
  generalize first_eq : columns 0 = first
  generalize second_eq : columns 1 = second
  generalize third_eq : columns 2 = third
  fin_cases first <;> fin_cases second <;> fin_cases third <;>
    norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, first_eq, second_eq, third_eq,
      k4RootMatrix, SignType.range_eq]

theorem k4RootMatrix_totallyUnimodular : (k4RootMatrix ℤ).IsTotallyUnimodular := by
  apply totallyUnimodular_of_full_minors (k4RootMatrix ℤ) k4BasisEdges
  · intro row column
    have entry := congrFun (congrFun (k4RootMatrix_basis_block ℤ) row) column
    simpa [Matrix.one_apply] using entry
  · exact k4RootMatrix_full_minors

def k4RootLift (Ring : Type*) [CommRing Ring] : (Fin 3 → Ring) →ₗ[Ring] (Fin 4 → Ring) where
  toFun vector := ![-(vector 0 + vector 1 + vector 2), vector 0, vector 1, vector 2]
  map_add' first second := by
    ext vertex
    fin_cases vertex <;> simp; ring
  map_smul' scalar vector := by
    ext vertex
    fin_cases vertex <;> simp; ring

theorem k4RootLift_injective (Ring : Type*) [CommRing Ring] :
    Function.Injective (k4RootLift Ring) := by
  intro first second equality
  have coordinate1 := congrFun equality 1
  have coordinate2 := congrFun equality 2
  have coordinate3 := congrFun equality 3
  ext index
  fin_cases index <;> simp_all [k4RootLift]

theorem k4RootLift_column (edge : Fin 6) :
    k4RootLift ℝ ((k4RootMatrix ℝ).col edge) =
      directedRoot (k4EdgeSource edge) (k4EdgeTarget edge) := by
  ext vertex
  fin_cases edge <;> fin_cases vertex <;>
    norm_num [k4RootLift, k4RootMatrix, directedRoot, k4EdgeSource, k4EdgeTarget, Pi.single_apply]

end BondalThomsen
