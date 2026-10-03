module

public import BondalThomsen.Ports.Matroid.Representation
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

@[expose] public section

open Set Submodule Function Module

noncomputable def Module.Basis.spanImage {Index Ring Vector : Type*} [Semiring Ring]
    [AddCommMonoid Vector] [Module Ring Vector] {vectors : Index → Vector}
    {subset : Set Index} (independent : LinearIndepOn Ring vectors subset) :
    Basis subset Ring (span Ring (vectors '' subset)) :=
  (Basis.span independent.linearIndependent).map <|
    LinearEquiv.ofEq _ _ (congrArg (span Ring) (by aesop))

theorem Function.ExtendByZero.linearMap_injective (Ring : Type*) {Index Other : Type*}
    [Semiring Ring] {inclusion : Index → Other} (injective : Function.Injective inclusion) :
    Function.Injective (Function.ExtendByZero.linearMap Ring inclusion) := by
  intro first second equality
  ext index
  have at_index := congrFun equality (inclusion index)
  simp only [ExtendByZero.linearMap_apply] at at_index
  rwa [injective.extend_apply, injective.extend_apply] at at_index

namespace Matroid

variable {Label Field Vector Other : Type*} [DivisionRing Field]
    [AddCommGroup Vector] [Module Field Vector] [AddCommGroup Other] [Module Field Other]
    {matroid : Matroid Label}

def Rep.comp (representation : matroid.Rep Field Vector) (mapping : Vector →ₗ[Field] Other)
    (injective : Disjoint (span Field (range representation)) mapping.ker) :
    matroid.Rep Field Other where
  to_fun := mapping ∘ representation
  indep_iff' subset := by
    rw [LinearMap.linearIndepOn_iff_of_injOn, representation.indep_iff]
    exact LinearMap.injOn_of_disjoint_ker (span_mono (image_subset_range ..)) injective

def Rep.comp' (representation : matroid.Rep Field Vector) (mapping : Vector →ₗ[Field] Other)
    (injective : mapping.ker = ⊥) : matroid.Rep Field Other :=
  representation.comp mapping (by simp [injective])

def Rep.compEquiv (representation : matroid.Rep Field Vector)
    (change : Vector ≃ₗ[Field] Other) : matroid.Rep Field Other :=
  representation.comp' change change.ker

def Rep.restrictSpan (representation : matroid.Rep Field Vector) :
    matroid.Rep Field (span Field (range representation)) where
  to_fun := codRestrict representation _ (fun _ => subset_span (mem_range_self _))
  indep_iff' subset := by
    rw [representation.indep_iff]
    refine ⟨fun independent => LinearIndependent.of_comp (Submodule.subtype _)
      (by simpa only [Function.comp_def, Set.codRestrict, Submodule.coe_subtype]
        using independent.linearIndependent),
      fun independent => independent.map' (Submodule.subtype _) (ker_subtype _)⟩

theorem Rep.span_spanning_eq (representation : matroid.Rep Field Vector)
    {subset : Set Label} (spanning : matroid.Spanning subset) :
    span Field (representation '' subset) = span Field (range representation) := by
  rw [← image_univ]
  apply representation.span_closure_congr
  simp [spanning.closure_eq]

noncomputable def Rep.isBasis_of_isBase (representation : matroid.Rep Field Vector)
    {basisSet : Set Label} (basis : matroid.IsBase basisSet) :
    Basis basisSet Field (span Field (range representation)) :=
  (Basis.spanImage (representation.onIndep basis.indep)).map <|
    LinearEquiv.ofEq _ _ (representation.span_spanning_eq basis.spanning)

noncomputable def Rep.standardRep' (representation : matroid.Rep Field Vector)
    {basisSet : Set Label} (basis : matroid.IsBase basisSet) :
    matroid.Rep Field (basisSet →₀ Field) :=
  representation.restrictSpan.compEquiv (representation.isBasis_of_isBase basis).repr

noncomputable def Rep.standardRep (representation : matroid.Rep Field Vector)
    {basisSet : Set Label} (basis : matroid.IsBase basisSet) :
    matroid.Rep Field (basisSet → Field) :=
  (representation.standardRep' basis).comp' Finsupp.lcoeFun (by
    apply LinearMap.ker_eq_bot.mpr
    intro first second equality
    exact Finsupp.ext (congrFun equality))

def Representable (matroid : Matroid Label) (Field : Type*) [Semiring Field] : Prop :=
  Nonempty (matroid.Rep Field (Label → Field))

theorem Rep.representable (representation : matroid.Rep Field Vector) :
    matroid.Representable Field := by
  obtain ⟨basisSet, basis⟩ := matroid.exists_isBase
  exact ⟨(representation.standardRep basis).comp'
    (ExtendByZero.linearMap Field ((↑) : basisSet → Label))
    (LinearMap.ker_eq_bot.mpr
      (ExtendByZero.linearMap_injective Field Subtype.val_injective))⟩

theorem Representable.contract (representable : matroid.Representable Field)
    (contracted : Set Label) : (matroid ／ contracted).Representable Field := by
  obtain ⟨representation⟩ := representable
  exact (representation.contract contracted).representable

theorem Representable.delete (representable : matroid.Representable Field)
    (deleted : Set Label) : (matroid ＼ deleted).Representable Field := by
  obtain ⟨representation⟩ := representable
  exact (representation.delete deleted).representable

theorem Representable.restrict (representable : matroid.Representable Field)
    (subset : Set Label) : (matroid ↾ subset).Representable Field := by
  obtain ⟨representation⟩ := representable
  exact (representation.restrict subset).representable

theorem Representable.of_isMinor (representable : matroid.Representable Field)
    {minor : Matroid Label} (is_minor : minor ≤m matroid) : minor.Representable Field := by
  obtain ⟨contracted, deleted, _, _, _, rfl⟩ := is_minor.exists_eq_contract_delete_disjoint
  exact (representable.contract contracted).delete deleted

end Matroid
