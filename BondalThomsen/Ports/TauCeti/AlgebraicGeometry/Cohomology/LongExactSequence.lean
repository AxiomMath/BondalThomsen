module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.Sheaf
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

def cohomologyMap {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    Cohomology M n →+ Cohomology N n :=
  CategoryTheory.Sheaf.H.map ((toSheaf X).map f) n

@[simp]
lemma cohomologyFunctor_map {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (cohomologyFunctor X n).map f = AddCommGrpCat.ofHom (cohomologyMap f n) :=
  by
    rw [cohomologyMap.eq_def]
    rfl

@[simp]
lemma cohomologyZeroEquiv_cohomologyMap {M N : X.Modules} (f : M ⟶ N) (x : Cohomology M 0) :
    cohomologyZeroEquiv N (cohomologyMap f 0 x) = f.app ⊤ (cohomologyZeroEquiv M x) :=
  by
    have hx : (cohomologyFunctor X 0).map f x = cohomologyMap f 0 x := by
      exact congrArg
        (fun g : (cohomologyFunctor X 0).obj M ⟶ (cohomologyFunctor X 0).obj N ↦ g x)
        (cohomologyFunctor_map f 0)
    rw [← hx]
    exact cohomologyZeroEquiv_naturality f x

lemma sections_ladder {M N : X.Modules} (f : M ⟶ N) :
    (f.app ⊤).hom.comp (cohomologyZeroEquiv M) =
      (cohomologyZeroEquiv N : Cohomology N 0 →+ Γ(N, ⊤)).comp (cohomologyMap f 0) := by
  ext x
  exact (cohomologyZeroEquiv_cohomologyMap f x).symm

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS

def cohomologyδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Cohomology S.X₃ n₀ →+ Cohomology S.X₁ n₁ :=
  CategoryTheory.Sheaf.H.δ (shortExact_map_toSheaf hS) n₀ n₁ h

theorem exact_cohomologyMap_cohomologyMap (n : ℕ) :
    Function.Exact (cohomologyMap S.f n) (cohomologyMap S.g n) :=
  CategoryTheory.Sheaf.H.exact_map_map (shortExact_map_toSheaf hS) n

theorem exact_cohomologyMap_cohomologyδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyMap S.g n₀) (cohomologyδ hS n₀ n₁ h) :=
  CategoryTheory.Sheaf.H.exact_map_δ (shortExact_map_toSheaf hS) n₀ n₁ h

theorem exact_cohomologyδ_cohomologyMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyδ hS n₀ n₁ h) (cohomologyMap S.f n₁) :=
  CategoryTheory.Sheaf.H.exact_δ_map (shortExact_map_toSheaf hS) n₀ n₁ h

theorem exact_sections : Function.Exact ⇑(S.f.app ⊤) ⇑(S.g.app ⊤) :=
  Function.Exact.of_ladder_addEquiv_of_exact (cohomologyZeroEquiv S.X₁)
    (cohomologyZeroEquiv S.X₂) (cohomologyZeroEquiv S.X₃) (sections_ladder S.f)
    (sections_ladder S.g) (exact_cohomologyMap_cohomologyMap hS 0)

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
