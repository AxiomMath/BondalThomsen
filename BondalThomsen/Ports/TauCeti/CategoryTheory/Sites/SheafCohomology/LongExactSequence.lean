module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

@[expose] public section

open CategoryTheory Abelian

universe w v u

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

namespace H

theorem map_injective {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f] :
    Function.Injective (map f 0) := by
  intro x y hxy
  apply (Ext.addEquiv₀ (C := Sheaf J AddCommGrpCat.{v})).injective
  rw [← cancel_mono f, ← addEquiv₀_map, ← addEquiv₀_map, hxy]

include hS

theorem exact_map_map (n : ℕ) : Function.Exact (map S.f n) (map S.g n) := by
  have := longSequence_exact₂' hS n
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

theorem exact_map_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (map S.g n₀) (δ hS n₀ n₁ h) := by
  have := longSequence_exact₃' hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

theorem exact_δ_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (δ hS n₀ n₁ h) (map S.f n₁) := by
  have := longSequence_exact₁' hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

end H

end Sheaf

end CategoryTheory
