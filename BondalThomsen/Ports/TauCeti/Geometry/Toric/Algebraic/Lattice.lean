module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

@[expose] public section

namespace TauCeti.Toric

open scoped TensorProduct

section Basic

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

structure IsIntegralLattice (i : N →+ V) : Prop where

  free : Module.Free ℤ N

  finite : Module.Finite ℤ N

  isBaseChange : IsBaseChange ℝ i.toIntLinearMap

theorem isIntegralLattice_iff :
    IsIntegralLattice i ↔ Module.Free ℤ N ∧ Module.Finite ℤ N ∧
      ∃ e : ℝ ⊗[ℤ] N ≃ₗ[ℝ] V, ∀ n : N, e (1 ⊗ₜ[ℤ] n) = i n := by
  refine ⟨fun h ↦ ⟨h.free, h.finite, h.isBaseChange.equiv, fun n ↦ by simp⟩, ?_⟩
  rintro ⟨hfree, hfinite, e, he⟩
  exact ⟨hfree, hfinite, IsBaseChange.of_equiv e he⟩

theorem isIntegralLattice_of_basis {ι : Type*} [Finite ι] (b : Module.Basis ι ℤ N)
    (c : Module.Basis ι ℝ V) (hbc : ∀ j, i (b j) = c j) : IsIntegralLattice i := by
  obtain ⟨e, he⟩ : ∃ e : ℝ ⊗[ℤ] N ≃ₗ[ℝ] V, ∀ j, e (1 ⊗ₜ[ℤ] b j) = i (b j) := by
    refine ⟨(b.baseChange ℝ).equiv c (Equiv.refl ι), fun j ↦ ?_⟩
    rw [← Module.Basis.baseChange_apply ℝ b j, Module.Basis.equiv_apply]
    exact (hbc j).symm
  refine isIntegralLattice_iff.2
    ⟨Module.Free.of_basis b, Module.Finite.of_basis b, e, fun n ↦ ?_⟩
  exact LinearMap.congr_fun
    (b.ext fun j ↦ he j : (e.restrictScalars ℤ).comp (TensorProduct.mk ℤ ℝ N 1)
      = i.toIntLinearMap) n

theorem IsIntegralLattice.injective (h : IsIntegralLattice i) :
    Function.Injective i := by
  let _ := h.free
  obtain ⟨e, he⟩ := (isIntegralLattice_iff.1 h).2.2
  intro x y hxy
  refine Module.Flat.tensorProduct_mk_injective ℤ N ℝ (e.injective ?_)
  simpa only [TensorProduct.mk_apply, he] using hxy

theorem IsIntegralLattice.finrank_eq (h : IsIntegralLattice i) :
    Module.finrank ℤ N = Module.finrank ℝ V := by
  let _ := h.free
  rw [← Module.finrank_baseChange (R := ℝ) (S := ℤ) (M' := N),
    h.isBaseChange.equiv.finrank_eq]

theorem IsIntegralLattice.finiteDimensional (h : IsIntegralLattice i) :
    FiniteDimensional ℝ V := by
  let _ := h.finite
  exact Module.Finite.equiv h.isBaseChange.equiv

theorem IsIntegralLattice.range_eq_span {ι : Type*} (h : IsIntegralLattice i)
    (b : Module.Basis ι ℤ N) :
    LinearMap.range i.toIntLinearMap = Submodule.span ℤ (Set.range (h.isBaseChange.basis b)) := by
  rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span ℤ) (congrArg Set.range (funext fun j ↦ by
    simpa only [Function.comp_apply, AddMonoidHom.coe_toIntLinearMap] using
      (h.isBaseChange.basis_apply b j).symm))

end Basic

section Naturality

variable {N N' N'' V V' V'' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

noncomputable def IsIntegralLattice.extend (h : IsIntegralLattice i) (i' : N' →+ V')
    (f : N →+ N') : V →ₗ[ℝ] V' :=
  h.isBaseChange.lift (i'.toIntLinearMap.comp f.toIntLinearMap)

@[simp]
theorem IsIntegralLattice.extend_apply (h : IsIntegralLattice i) (i' : N' →+ V') (f : N →+ N')
    (n : N) : h.extend i' f (i n) = i' (f n) :=
  h.isBaseChange.lift_eq _ n

theorem IsIntegralLattice.eq_extend (h : IsIntegralLattice i) {f : N →+ N'} {g : V →ₗ[ℝ] V'}
    (hg : ∀ n, g (i n) = i' (f n)) : g = h.extend i' f :=
  h.isBaseChange.algHom_ext g (h.extend i' f) fun n ↦ by
    simp only [AddMonoidHom.coe_toIntLinearMap, hg, IsIntegralLattice.extend_apply]

@[simp]
theorem IsIntegralLattice.extend_id (h : IsIntegralLattice i) :
    h.extend i (AddMonoidHom.id N) = LinearMap.id :=
  (h.eq_extend fun _ ↦ rfl).symm

@[simp]
theorem IsIntegralLattice.extend_comp (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') (f' : N' →+ N'') :
    (h'.extend i'' f').comp (h.extend i' f) = h.extend i'' (f'.comp f) :=
  h.eq_extend (i' := i'') (f := f'.comp f) fun n ↦ by simp

noncomputable def IsIntegralLattice.realCharacter (h : IsIntegralLattice i) :
    (N →+ ℤ) →+ Module.Dual ℝ V :=
  (h.isBaseChange.toDual.comp (addMonoidHomLequivInt ℤ).toLinearMap).toAddMonoidHom

@[simp]
theorem IsIntegralLattice.realCharacter_apply (h : IsIntegralLattice i)
    (m : N →+ ℤ) (n : N) : h.realCharacter m (i n) = (m n : ℝ) := by
  simpa [IsIntegralLattice.realCharacter] using
    h.isBaseChange.toDual_comp_apply m.toIntLinearMap n

theorem IsIntegralLattice.eq_realCharacter (h : IsIntegralLattice i) {m : N →+ ℤ}
    {φ : Module.Dual ℝ V} (hφ : ∀ n, φ (i n) = (m n : ℝ)) : φ = h.realCharacter m :=
  h.isBaseChange.algHom_ext φ (h.realCharacter m) fun n ↦ by
    simp only [AddMonoidHom.coe_toIntLinearMap, hφ, IsIntegralLattice.realCharacter_apply]

theorem IsIntegralLattice.realCharacter_injective (h : IsIntegralLattice i) :
    Function.Injective h.realCharacter := by
  intro m m' hm
  ext n
  have hc : (m n : ℝ) = (m' n : ℝ) := by
    simpa using DFunLike.congr_fun hm (i n)
  exact Int.cast_injective hc

theorem IsIntegralLattice.realCharacter_comp (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (m : N' →+ ℤ) :
    h.realCharacter (m.comp f) = (h'.realCharacter m).comp g :=
  (h.eq_realCharacter fun n ↦ by simp [hfg]).symm

theorem IsIntegralLattice.prod (h : IsIntegralLattice i) (h' : IsIntegralLattice i') :
    IsIntegralLattice (i.prodMap i') := by
  let _ := h.free
  let _ := h'.free
  let _ := h.finite
  let _ := h'.finite
  exact ⟨inferInstance, inferInstance,
    IsBaseChange.prodMap i.toIntLinearMap i'.toIntLinearMap h.isBaseChange h'.isBaseChange⟩

end Naturality

section Discrete

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V}

theorem IsIntegralLattice.discreteTopology (h : IsIntegralLattice i) :
    DiscreteTopology (LinearMap.range i.toIntLinearMap) := by
  let _ := h.free
  let _ := h.finite
  rw [h.range_eq_span (Module.Free.chooseBasis ℤ N)]
  infer_instance

end Discrete

end TauCeti.Toric
