module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

theorem epi_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (F.H' n₁ S.X₂)) (h₃ : Subsingleton (F.H' n₁ S.X₃)) :
    Epi (S.δ F n₀ n₁ h) := by
  have hg : S.toBiprod F n₁ = 0 :=
    ((biprod_isZero_iff _ _).2
      ⟨AddCommGrpCat.isZero_of_subsingleton _,
        AddCommGrpCat.isZero_of_subsingleton _⟩).eq_of_tgt _ _
  have hex := (S.sequence_exact F n₀ n₁ h).exact' 2 3 4
  exact hex.epi_f hg

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare
