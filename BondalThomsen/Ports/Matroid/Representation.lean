module

public import Mathlib.Combinatorics.Matroid.Minor.Order
public import Mathlib.Combinatorics.Matroid.Closure
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import BondalThomsen.Matroid.RayMatroid

@[expose] public section

open Set Submodule Function

namespace Matroid

variable {Label Field Vector : Type*} [DivisionRing Field]
    [AddCommGroup Vector] [Module Field Vector] {matroid : Matroid Label}
    {independentSet basisSet subset : Set Label} {element : Label}

@[ext] structure Rep (matroid : Matroid Label) (Field Vector : Type*)
    [Semiring Field] [AddCommMonoid Vector] [Module Field Vector] where
  to_fun : Label → Vector
  indep_iff' : ∀ subset, matroid.Indep subset ↔ LinearIndepOn Field to_fun subset

instance : FunLike (matroid.Rep Field Vector) Label Vector where
  coe representation := representation.to_fun
  coe_injective := by rintro ⟨first, _⟩ ⟨second, _⟩ equality; cases equality; rfl

theorem Rep.indep_iff (representation : matroid.Rep Field Vector) :
    matroid.Indep independentSet ↔ LinearIndepOn Field representation independentSet :=
  representation.indep_iff' independentSet

theorem Rep.onIndep (representation : matroid.Rep Field Vector)
    (independent : matroid.Indep independentSet) :
    LinearIndepOn Field representation independentSet :=
  representation.indep_iff.mp independent

theorem Rep.eq_zero_iff_not_indep (representation : matroid.Rep Field Vector) :
    representation element = 0 ↔ ¬matroid.Indep {element} := by
  simp [representation.indep_iff]

theorem Rep.eq_zero_of_notMem_ground (representation : matroid.Rep Field Vector)
    (outside : element ∉ matroid.E) : representation element = 0 := by
  rw [representation.eq_zero_iff_not_indep, indep_singleton]
  exact fun nonloop => outside nonloop.mem_ground

def Rep.ofGround (vectors : Label → Vector) (support : Function.support vectors ⊆ matroid.E)
    (independence : ∀ subset ⊆ matroid.E,
      matroid.Indep subset ↔ LinearIndepOn Field vectors subset) : matroid.Rep Field Vector where
  to_fun := vectors
  indep_iff' subset := (em (subset ⊆ matroid.E)).elim (independence subset)
    fun outside => iff_of_false (mt Indep.subset_ground outside)
      fun independent => outside fun _ member => support (independent.ne_zero member)

noncomputable def Rep.restrict (representation : matroid.Rep Field Vector)
    (subset : Set Label) : (matroid ↾ subset).Rep Field Vector := by
  classical
  refine Rep.ofGround (subset.indicator representation) (by simp) ?_
  intro independentSet contained
  have in_subset : independentSet ⊆ subset := by
    simpa only [restrict_ground_eq] using contained
  rw [restrict_indep_iff, and_iff_left in_subset, representation.indep_iff]
  exact linearIndepOn_congr (eqOn_indicator.symm.mono in_subset)

theorem Rep.isBasis'_iff (representation : matroid.Rep Field Vector) :
    matroid.IsBasis' basisSet subset ↔ basisSet ⊆ subset ∧
      LinearIndepOn Field representation basisSet ∧
      representation '' subset ⊆ span Field (representation '' basisSet) := by
  have downward ⦃smaller larger : Set Label⦄ :
      matroid.Indep larger ∧ larger ⊆ subset → smaller ⊆ larger →
        matroid.Indep smaller ∧ smaller ⊆ subset :=
    fun larger_properties contained =>
      ⟨larger_properties.1.subset contained, contained.trans larger_properties.2⟩
  simp only [IsBasis', maximal_iff_forall_insert downward, insert_subset_iff, not_and,
    image_subset_iff]
  simp +contextual only [representation.indep_iff, linearIndepOn_insert_iff, imp_false,
    and_imp, iff_def, true_and, not_true_eq_false, not_imp_not, forall_const, and_self]
  refine ⟨fun independent contained maximal selected member =>
    (em (selected ∈ basisSet)).elim (fun in_basis => ?_)
      fun outside => maximal selected outside member,
    fun contained independent spanning selected outside member => spanning member⟩
  exact mem_of_mem_of_subset in_basis <|
    (subset_preimage_image representation basisSet).trans (preimage_mono subset_span)

theorem Rep.mem_closure_iff (representation : matroid.Rep Field Vector)
    (in_ground : element ∈ matroid.E) :
    element ∈ matroid.closure subset ↔
      representation element ∈ span Field (representation '' subset) := by
  obtain ⟨basisSet, basis⟩ := matroid.exists_isBasis' subset
  have spans_equal : span Field (representation '' basisSet) =
      span Field (representation '' subset) :=
    (span_mono (image_mono basis.subset)).antisymm
      (span_le.mpr (representation.isBasis'_iff.mp basis).2.2)
  rw [← basis.closure_eq_closure, ← spans_equal, ← not_iff_not,
    (representation.onIndep basis.indep).notMem_span_iff,
    basis.indep.notMem_closure_iff, representation.indep_iff]

theorem Rep.closure_eq (representation : matroid.Rep Field Vector) (subset : Set Label) :
    matroid.closure subset =
      (representation ⁻¹' span Field (representation '' subset)) ∩ matroid.E := by
  ext element
  by_cases in_ground : element ∈ matroid.E
  · rw [representation.mem_closure_iff in_ground, mem_inter_iff,
      and_iff_left in_ground, mem_preimage, SetLike.mem_coe]
  simp [in_ground, notMem_subset (matroid.closure_subset_ground subset) in_ground]

theorem Rep.span_le_of_closure_subset (representation : matroid.Rep Field Vector)
    {first second : Set Label} (contained : matroid.closure first ⊆ matroid.closure second) :
    span Field (representation '' first) ≤ span Field (representation '' second) := by
  rw [span_le]
  rintro _ ⟨element, member, rfl⟩
  by_cases in_ground : element ∈ matroid.E
  · rw [representation.closure_eq second] at contained
    exact (contained (matroid.mem_closure_of_mem' member in_ground)).1
  · simp [representation.eq_zero_of_notMem_ground in_ground]

theorem Rep.span_closure_congr (representation : matroid.Rep Field Vector)
    {first second : Set Label} (equality : matroid.closure first = matroid.closure second) :
    span Field (representation '' first) = span Field (representation '' second) :=
  (representation.span_le_of_closure_subset equality.subset).antisymm
    (representation.span_le_of_closure_subset equality.symm.subset)

def Rep.contract (representation : matroid.Rep Field Vector) (contracted : Set Label) :
    (matroid ／ contracted).Rep Field
      (Vector ⧸ span Field (representation '' contracted)) where
  to_fun := (span Field (representation '' contracted)).mkQ ∘ representation
  indep_iff' subset := by
    obtain ⟨basisSet, basis⟩ := matroid.exists_isBasis' contracted
    by_cases disjoint : Disjoint contracted subset
    · rw [basis.contract_indep_iff, and_iff_left disjoint,
        ← representation.span_closure_congr basis.closure_eq_closure,
        (representation.onIndep basis.indep).quotient_iff_union
          (disjoint.mono_left basis.subset), representation.indep_iff, union_comm]
    obtain ⟨element, in_contracted, in_subset⟩ := not_disjoint_iff.mp disjoint
    refine iff_of_false
      (fun independent => disjoint (subset_sdiff.mp independent.subset_ground).2.symm)
      fun independent => independent.ne_zero in_subset ?_
    simpa using subset_span (mem_image_of_mem representation in_contracted)

noncomputable def Rep.delete (representation : matroid.Rep Field Vector)
    (deleted : Set Label) : (matroid ＼ deleted).Rep Field Vector :=
  matroid.delete_eq_restrict deleted ▸ representation.restrict (matroid.E \ deleted)

def repOfRays (vectors : Label → Vector) :
    (BondalThomsen.rayMatroid (Field := Field) vectors).Rep Field Vector where
  to_fun := vectors
  indep_iff' := BondalThomsen.rayMatroid_indep_iff vectors

end Matroid
