module

public import BondalThomsen.Toric.Scheme.Integral
public import BondalThomsen.Derived.LineBundleGenericComposition

@[expose] public section

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem exists_invertibleSheafExt_ordering (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {Index : Type*} [Fintype Index]
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf
      (fan.algebraicRealization 𝕜 regular))
    (distinct_classes : Function.Injective (fun index =>
      TauCeti.AlgebraicGeometry.LineBundleClass.mk (line_bundles index)))
    (positive_vanishing : ∀ source target degree, 0 < degree →
      Subsingleton (Abelian.Ext (line_bundles source).obj (line_bundles target).obj degree)) :
    ∃ numbering : Index ≃ Fin (Fintype.card Index),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Abelian.Ext (line_bundles source).obj
          (line_bundles target).obj degree), extension = 0 := by
  obtain ⟨cone, member, _⟩ := fan.isComplete_iff.mp complete 0
  let := fan.algebraicRealization_isIntegral 𝕜 regular ⟨⟨cone, member⟩⟩
  exact BondalThomsen.exists_invertibleSheafExt_ordering_of_isIntegral
    (fan.scalarGlobalFunctionsEquiv 𝕜 complete regular) line_bundles
    (fun isomorphic => distinct_classes
      (TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mpr isomorphic))
    positive_vanishing

end TauCeti.Toric.Fan
