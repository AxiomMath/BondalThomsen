module

public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Generation
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Regular
public import Mathlib.Geometry.Convex.Cone.Simplicial

@[expose] public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

theorem ToricRay.iSup_toPointedCone (hσ : σ.FG) (hsal : (σ : ConvexCone ℝ V).Salient) :
    ⨆ ρ : ToricRay σ, ρ.toPointedCone = σ := by
  refine le_antisymm (iSup_le fun ρ ↦ ρ.1.isFaceOf.le) ?_
  obtain ⟨s, hs, hface⟩ := PointedCone.FG.exists_finset_hull_eq_isFaceOf hσ hsal
  refine hs.ge.trans (Submodule.span_le.2 fun v hv ↦ ?_)
  obtain ⟨hv0, hvσ⟩ := hface v hv
  let ρ : ToricRay σ :=
    ⟨⟨ℝ ∙₊ v, hs ▸ hvσ⟩, PointedCone.finrank_span_coe_hull_singleton hv0⟩
  exact SetLike.mem_coe.2
    (le_iSup (fun ρ : ToricRay σ ↦ ρ.toPointedCone) ρ (PointedCone.subset_hull rfl))

theorem IsToricCone.hull_primitiveGenerator (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) :
    PointedCone.hull ℝ (i '' Set.range (primitiveGenerator hi hσ)) = σ := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨_, ⟨ρ, rfl⟩, rfl⟩
    exact ρ.1.isFaceOf.le (primitiveGenerator_mem hi hσ ρ)
  · refine (ToricRay.iSup_toPointedCone hσ.fg hσ.salient).ge.trans (iSup_le fun ρ ↦ ?_)
    rw [ρ.eq_hull_singleton (hσ.salient.anti ρ.1.isFaceOf.le) (primitiveGenerator_mem hi hσ ρ)
      (by simpa using hi.injective.ne (primitiveGenerator_ne_zero hi hσ ρ))]
    exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨_, ⟨ρ, rfl⟩, rfl⟩)

theorem mem_dualSemigroup_iff_primitiveGenerator (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (m : N →+ ℤ) :
    m ∈ dualSemigroup hi σ ↔ ∀ ρ : ToricRay σ, 0 ≤ m (primitiveGenerator hi hσ ρ) := by
  have h := mem_dualSemigroup_hull_image hi (Set.range (primitiveGenerator hi hσ)) m
  rwa [hσ.hull_primitiveGenerator hi, Set.forall_mem_range] at h

theorem mem_dualSemigroup_iff_of_isPrimitiveGenerator (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) {v : ToricRay σ → N} (hv : ∀ ρ, IsPrimitiveGenerator i ρ (v ρ))
    (m : N →+ ℤ) : m ∈ dualSemigroup hi σ ↔ ∀ ρ : ToricRay σ, 0 ≤ m (v ρ) := by
  simp only [mem_dualSemigroup_iff_primitiveGenerator hi hσ, ← (hv _).eq_primitiveGenerator hi hσ]

theorem IsRegularCone.linearIndependent_primitiveGenerator (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) :
    LinearIndependent ℝ fun ρ : ToricRay σ ↦ i (primitiveGenerator hi hσ.toIsToricCone ρ) := by
  obtain ⟨n, b, r, hb⟩ := hσ.exists_basis
  have heq : (fun ρ : ToricRay σ ↦ i (primitiveGenerator hi hσ.toIsToricCone ρ)) =
      hi.isBaseChange.basis b ∘ r := by
    refine funext fun ρ ↦ ?_
    rw [Function.comp_apply, hi.isBaseChange.basis_apply b (r ρ),
      ((hb.isPrimitiveGenerator_apply ρ).eq_primitiveGenerator hi hσ.toIsToricCone)]
    rfl
  rw [heq]
  exact (hi.isBaseChange.basis b).linearIndependent.comp r r.injective

end TauCeti.Toric
