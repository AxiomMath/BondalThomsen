module

public import Mathlib.LinearAlgebra.Basis.Exact
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

namespace BondalThomsen

open Module

variable {Scalar Index Space : Type*} [CommRing Scalar] [IsDomain Scalar]
    [AddCommGroup Space] [Module Scalar Space] [DecidableEq Index]

noncomputable def basisRayQuotient (basis : Basis Index Scalar Space) (removed : Index) :
    Basis {index : Index // index ≠ removed} Scalar
      (Space ⧸ Submodule.span Scalar {basis removed}) := by
  let inclusion : Scalar →ₗ[Scalar] Space := LinearMap.id.smulRight (basis removed)
  let retraction := basis.coord removed
  let projection := (Submodule.span Scalar {basis removed}).mkQ
  have splitting : retraction ∘ₗ inclusion = LinearMap.id := by
    apply LinearMap.ext
    intro scalar
    simp [retraction, inclusion, Basis.coord_apply]
  have exact_sequence : Function.Exact inclusion projection := by
    intro vector
    change projection vector = 0 ↔ ∃ scalar, inclusion scalar = vector
    simp only [projection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_span_singleton
  have killed : ∀ index : {index : Index // index ≠ removed},
      retraction (basis index.val) = 0 := by
    intro index
    simp [retraction, Basis.coord_apply, Ne.symm index.property]
  have independent : LinearIndependent Scalar
      (retraction ∘ basis ∘ (fun _ : Unit => removed)) := by
    apply linearIndependent_unique_iff.mpr
    simp [retraction, Basis.coord_apply]
  have covers : Codisjoint
      (Set.range (Subtype.val : {index : Index // index ≠ removed} → Index))
      (Set.range (fun _ : Unit => removed)) := by
    rw [codisjoint_iff]
    change Set.range Subtype.val ∪ Set.range (fun _ : Unit => removed) = Set.univ
    apply Set.eq_univ_of_forall
    intro index
    by_cases same : index = removed
    · exact Or.inr ⟨(), same.symm⟩
    · exact Or.inl ⟨⟨index, same⟩, rfl⟩
  exact Basis.ofSplitExact splitting exact_sequence
    (Submodule.mkQ_surjective _) basis Subtype.val_injective killed independent covers

@[simp] theorem basisRayQuotient_apply (basis : Basis Index Scalar Space) (removed : Index)
    (index : {index : Index // index ≠ removed}) :
    basisRayQuotient basis removed index =
      (Submodule.span Scalar {basis removed}).mkQ (basis index.val) := by
  unfold basisRayQuotient
  exact Basis.ofSplitExact_apply ..

@[simp] theorem basisRayQuotient_repr (basis : Basis Index Scalar Space) (removed : Index)
    (vector : Space) (index : {index : Index // index ≠ removed}) :
    (basisRayQuotient basis removed).repr
      ((Submodule.span Scalar {basis removed}).mkQ vector) index =
      basis.repr vector index.val := by
  have equality : ((basisRayQuotient basis removed).coord index).comp
      (Submodule.span Scalar {basis removed}).mkQ = basis.coord index.val := by
    apply basis.ext
    intro original
    by_cases same : original = removed
    · subst original
      have killed : (Submodule.span Scalar {basis removed}).mkQ (basis removed) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton _)
      simp [killed, Basis.coord_apply, Ne.symm index.property]
    · rw [LinearMap.comp_apply, ← basisRayQuotient_apply basis removed ⟨original, same⟩]
      simp only [Basis.coord_apply, Basis.repr_self_apply]
      simp only [Subtype.ext_iff]
  exact DFunLike.congr_fun equality vector

noncomputable def basisVectorQuotient (basis : Basis Index Scalar Space) (removed : Index)
    (vector : Space) (equality : basis removed = vector) :
    Basis {index : Index // index ≠ removed} Scalar
      (Space ⧸ Submodule.span Scalar {vector}) :=
  (basisRayQuotient basis removed).map
    ((Submodule.span Scalar {basis removed}).quotEquivOfEq
      (Submodule.span Scalar {vector}) (congrArg (fun point => Submodule.span Scalar {point})
        equality))

@[simp] theorem basisVectorQuotient_apply (basis : Basis Index Scalar Space) (removed : Index)
    (vector : Space) (equality : basis removed = vector)
    (index : {index : Index // index ≠ removed}) :
    basisVectorQuotient basis removed vector equality index =
      (Submodule.span Scalar {vector}).mkQ (basis index.val) := by
  simp [basisVectorQuotient, Submodule.mkQ_apply]

@[simp] theorem basisVectorQuotient_repr (basis : Basis Index Scalar Space) (removed : Index)
    (vector : Space) (equality : basis removed = vector) (lifted : Space)
    (index : {index : Index // index ≠ removed}) :
    (basisVectorQuotient basis removed vector equality).repr
      ((Submodule.span Scalar {vector}).mkQ lifted) index = basis.repr lifted index.val := by
  subst vector
  have same_basis : basisVectorQuotient basis removed (basis removed) rfl =
      basisRayQuotient basis removed := by
    apply DFunLike.coe_injective
    funext selected
    rw [basisVectorQuotient_apply, basisRayQuotient_apply]
  rw [same_basis, basisRayQuotient_repr]

end BondalThomsen
