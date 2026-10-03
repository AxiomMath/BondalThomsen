module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import BondalThomsen.Ports.TauCeti.Topology.Sheaves.Flasque

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

instance _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
    (M : X.Modules) [M.presheaf.IsFlasque] (n : ℕ) (U : X.Opens) :
    Subsingleton (cohomologyOn M (n + 1) U) := by
  let _ : TopCat.Presheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj := ‹M.presheaf.IsFlasque›
  exact TauCeti.Topology.subsingleton_H'_succ_of_isFlasque (X := X.toTopCat)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n U

instance _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque
    (M : X.Modules) [M.presheaf.IsFlasque] (n : ℕ) :
    Subsingleton (Cohomology M (n + 1)) := by
  let _ : TopCat.Presheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj := ‹M.presheaf.IsFlasque›
  exact TauCeti.Topology.subsingleton_H_succ_of_isFlasque (X := X.toTopCat)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n

section ShortExact

variable {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₂.presheaf.IsFlasque]

include hS

theorem cohomologyδ_surjective_of_isFlasque (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Surjective (cohomologyδ hS n₀ n₁ h) := by
  subst h
  intro x
  exact (exact_cohomologyδ_cohomologyMap hS n₀ (n₀ + 1) rfl x).mp
    (Subsingleton.elim _ _)

theorem cohomologyδ_injective_of_isFlasque (n : ℕ) :
    Function.Injective (cohomologyδ hS (n + 1) (n + 2) rfl) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_cohomologyMap_cohomologyδ hS (n + 1) (n + 2) rfl x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

end ShortExact

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
