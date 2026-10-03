module

public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
import BondalThomsen.Ports.TauCeti.Data.Fin.Sum
@[expose] public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {σ τ : PointedCone ℝ V}

structure IsExtendingBasis (i : N →+ V) {σ : PointedCone ℝ V} {n : ℕ}
    (b : Module.Basis (Fin n) ℤ N) (r : ToricRay σ ↪ Fin n) : Prop where

  isPrimitiveGenerator_apply : ∀ ρ : ToricRay σ, IsPrimitiveGenerator i ρ (b (r ρ))

structure IsRegularCone (i : N →+ V) (σ : PointedCone ℝ V) : Prop extends IsToricCone i σ where

  exists_basis : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (r : ToricRay σ ↪ Fin n),
    IsExtendingBasis i b r

namespace IsRegularCone

theorem of_isFaceOf (hσ : IsRegularCone i σ) (hτ : τ.IsFaceOf σ) : IsRegularCone i τ := by
  obtain ⟨n, b, r, hb⟩ := hσ.exists_basis
  refine ⟨hσ.toIsToricCone.of_isFaceOf hτ, n, b, (ToricRay.faceEmbedding hτ).trans r,
    ⟨fun ρ ↦ ?_⟩⟩
  exact (isPrimitiveGenerator_faceEmbedding hτ ρ).1 (hb.isPrimitiveGenerator_apply _)

theorem face (hσ : IsRegularCone i σ) (F : σ.Face) : IsRegularCone i F.toPointedCone :=
  hσ.of_isFaceOf F.isFaceOf

end IsRegularCone

theorem IsRegularCone.prod {τ' : PointedCone ℝ V'} (hσ : IsRegularCone i σ)
    (hτ' : IsRegularCone i' τ') : IsRegularCone (i.prodMap i') (σ.prod τ') := by
  obtain ⟨n, b, r, hb⟩ := hσ.exists_basis
  obtain ⟨n', b', r', hb'⟩ := hτ'.exists_basis
  set B := (b.prod b').reindex finSumFinEquiv with hB
  have hBinl : ∀ k : Fin n, B (finSumFinEquiv (Sum.inl k)) = (b k, 0) := fun k ↦ by
    rw [hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply]; simp
  have hBinr : ∀ k : Fin n', B (finSumFinEquiv (Sum.inr k)) = (0, b' k) := fun k ↦ by
    rw [hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply]; simp
  refine ⟨hσ.toIsToricCone.prod hτ'.toIsToricCone, n + n', B,
    (ToricRay.prodSplit hσ.salient hτ'.salient).toEmbedding.trans
      ((r.sumMap r').trans finSumFinEquiv.toEmbedding),
    ⟨fun G ↦ ?_⟩⟩
  rcases hG : ToricRay.prodSplit hσ.salient hτ'.salient G with ρ | ρ
  · have hGρ : G = ToricRay.prodInl hτ'.salient ρ := by
      calc
        G = (ToricRay.prodSplit hσ.salient hτ'.salient).symm
            (ToricRay.prodSplit hσ.salient hτ'.salient G) :=
          ((ToricRay.prodSplit hσ.salient hτ'.salient).symm_apply_apply G).symm
        _ = (ToricRay.prodSplit hσ.salient hτ'.salient).symm (Sum.inl ρ) :=
          congrArg (ToricRay.prodSplit hσ.salient hτ'.salient).symm hG
        _ = ToricRay.prodInl hτ'.salient ρ :=
          ToricRay.prodSplit_symm_inl hσ.salient hτ'.salient ρ
    have hidx : ((ToricRay.prodSplit hσ.salient hτ'.salient).toEmbedding.trans
        ((r.sumMap r').trans finSumFinEquiv.toEmbedding)) G
        = finSumFinEquiv (Sum.inl (r ρ)) := by
      simp [hG]
    rw [hidx, hBinl, hGρ]
    exact (hb.isPrimitiveGenerator_apply ρ).prodInl hτ'.salient
  · have hGρ : G = ToricRay.prodInr hσ.salient ρ := by
      calc
        G = (ToricRay.prodSplit hσ.salient hτ'.salient).symm
            (ToricRay.prodSplit hσ.salient hτ'.salient G) :=
          ((ToricRay.prodSplit hσ.salient hτ'.salient).symm_apply_apply G).symm
        _ = (ToricRay.prodSplit hσ.salient hτ'.salient).symm (Sum.inr ρ) :=
          congrArg (ToricRay.prodSplit hσ.salient hτ'.salient).symm hG
        _ = ToricRay.prodInr hσ.salient ρ :=
          ToricRay.prodSplit_symm_inr hσ.salient hτ'.salient ρ
    have hidx : ((ToricRay.prodSplit hσ.salient hτ'.salient).toEmbedding.trans
        ((r.sumMap r').trans finSumFinEquiv.toEmbedding)) G
        = finSumFinEquiv (Sum.inr (r' ρ)) := by
      simp [hG]
    rw [hidx, hBinr, hGρ]
    exact (hb'.isPrimitiveGenerator_apply ρ).prodInr hσ.salient

namespace IsExtendingBasis

variable {n n' : ℕ} {b : Module.Basis (Fin n) ℤ N} {b' : Module.Basis (Fin n') ℤ N}
  {r : ToricRay σ ↪ Fin n} {r' : ToricRay σ ↪ Fin n'}

theorem isPrimitiveGenerator_reindex {ι : Type*} (hb : IsExtendingBasis i b r)
    (e : ToricRay σ ⊕ ι ≃ Fin n) (he : ∀ ρ, e (Sum.inl ρ) = r ρ) (ρ : ToricRay σ) :
    IsPrimitiveGenerator i ρ (b.reindex e.symm (Sum.inl ρ)) := by
  simpa [he ρ] using hb.isPrimitiveGenerator_apply ρ

theorem basis_apply_eq (hi : IsIntegralLattice i) (hb : IsExtendingBasis i b r)
    (hb' : IsExtendingBasis i b' r') (ρ : ToricRay σ)
    (hρ : (ρ.toPointedCone : ConvexCone ℝ V).Salient) :
    b (r ρ) = b' (r' ρ) :=
  (hb.isPrimitiveGenerator_apply ρ).unique hi hρ (hb'.isPrimitiveGenerator_apply ρ)

theorem repr_basis_apply (hi : IsIntegralLattice i) (hb : IsExtendingBasis i b r)
    (hb' : IsExtendingBasis i b' r') (ρ : ToricRay σ)
    (hρ : (ρ.toPointedCone : ConvexCone ℝ V).Salient) :
    b'.repr (b (r ρ)) = Finsupp.single (r' ρ) 1 := by
  rw [hb.basis_apply_eq hi hb' ρ hρ, Module.Basis.repr_self]

theorem toMatrix_apply (hi : IsIntegralLattice i) (hb : IsExtendingBasis i b r)
    (hb' : IsExtendingBasis i b' r') (ρ : ToricRay σ)
    (hρ : (ρ.toPointedCone : ConvexCone ℝ V).Salient)
    (j : Fin n') : b'.toMatrix b j (r ρ) = if j = r' ρ then 1 else 0 := by
  rw [Module.Basis.toMatrix_apply, hb.repr_basis_apply hi hb' ρ hρ, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

end IsExtendingBasis

namespace IsRegularCone

theorem exists_basis_sum (h : IsRegularCone i σ) :
    ∃ (l : ℕ) (b : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N),
  ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)) := by
  obtain ⟨n, b, r, hb⟩ := h.exists_basis
  obtain ⟨l, e, he⟩ := r.exists_equiv_sum_fin
  exact ⟨l, b.reindex e.symm, hb.isPrimitiveGenerator_reindex e he⟩

end IsRegularCone

namespace Fan

def IsRegular (Φ : Fan i) : Prop := ∀ ⦃σ⦄, σ ∈ Φ.cones → IsRegularCone i σ

@[simp]
theorem isRegular_iff {Φ : Fan i} :
    Φ.IsRegular ↔ ∀ σ ∈ Φ.cones, IsRegularCone i σ := Iff.rfl

end Fan

end TauCeti.Toric
