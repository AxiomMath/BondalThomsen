module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace Function.Embedding

theorem exists_equiv_sum_fin {α : Type*} {n : ℕ} (s : α ↪ Fin n) :
    ∃ (l : ℕ) (e : α ⊕ Fin l ≃ Fin n), ∀ a, e (Sum.inl a) = s a := by
  classical
  have _ : Fintype α := Fintype.ofInjective s s.injective
  exact ⟨Fintype.card {j : Fin n // j ∉ Set.range s},
    (Equiv.sumCongr (Equiv.ofInjective s s.injective) (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl fun j : Fin n ↦ j ∈ Set.range s), fun a ↦ by simp⟩

end Function.Embedding

