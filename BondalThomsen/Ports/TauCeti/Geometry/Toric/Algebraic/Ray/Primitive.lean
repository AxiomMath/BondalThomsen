module

public import BondalThomsen.Ports.TauCeti.Algebra.Module.Primitive
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Cone
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Lattice
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Basic

@[expose] public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

def IsPrimitiveGenerator (i : N →+ V) {σ : PointedCone ℝ V}
    (ρ : ToricRay σ) (v : N) : Prop :=
  i v ∈ ρ ∧ IsPrimitive v

theorem isPrimitiveGenerator_iff {ρ : ToricRay σ} {v : N} :
    IsPrimitiveGenerator i ρ v ↔ i v ∈ ρ ∧ IsPrimitive v :=
  Iff.rfl

namespace IsPrimitiveGenerator

variable {ρ : ToricRay σ} {v : N}

theorem mem (h : IsPrimitiveGenerator i ρ v) : i v ∈ ρ := h.1

theorem isPrimitive (h : IsPrimitiveGenerator i ρ v) : IsPrimitive v := h.2

theorem ne_zero (h : IsPrimitiveGenerator i ρ v) : v ≠ 0 := h.isPrimitive.ne_zero

end IsPrimitiveGenerator

@[simp]
theorem isPrimitiveGenerator_faceEmbedding {τ : PointedCone ℝ V} (hτ : τ.IsFaceOf σ)
    (ρ : ToricRay τ) {v : N} :
    IsPrimitiveGenerator i (ToricRay.faceEmbedding hτ ρ) v ↔ IsPrimitiveGenerator i ρ v := by
  simp [isPrimitiveGenerator_iff]

section Prod

variable {N' V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {τ : PointedCone ℝ V'}

theorem IsPrimitiveGenerator.prodInl {ρ : ToricRay σ} {v : N}
    (hρ : IsPrimitiveGenerator i ρ v) (hτ : (τ : ConvexCone ℝ V').Salient) :
    IsPrimitiveGenerator (i.prodMap i') (ToricRay.prodInl hτ ρ) (v, 0) := by
  refine isPrimitiveGenerator_iff.2 ⟨?_, ?_⟩
  · simpa using hρ.mem
  · obtain ⟨f, hf⟩ := isPrimitive_def.1 hρ.isPrimitive
    exact isPrimitive_def.2 ⟨f.comp (LinearMap.fst ℤ N N'), by simpa using hf⟩

theorem IsPrimitiveGenerator.prodInr {ρ : ToricRay τ} {v : N'}
    (hρ : IsPrimitiveGenerator i' ρ v) (hσ : (σ : ConvexCone ℝ V).Salient) :
    IsPrimitiveGenerator (i.prodMap i') (ToricRay.prodInr hσ ρ) (0, v) := by
  refine isPrimitiveGenerator_iff.2 ⟨?_, ?_⟩
  · simpa using hρ.mem
  · obtain ⟨f, hf⟩ := isPrimitive_def.1 hρ.isPrimitive
    exact isPrimitive_def.2 ⟨f.comp (LinearMap.snd ℤ N N'), by simpa using hf⟩

end Prod

theorem IsPrimitiveGenerator.unique {ρ : ToricRay σ} {v w : N} (hi : IsIntegralLattice i)
    (hρ : (ρ.toPointedCone : ConvexCone ℝ V).Salient)
    (hv : IsPrimitiveGenerator i ρ v) (hw : IsPrimitiveGenerator i ρ w) : v = w := by
  have hρeq : ρ.toPointedCone = PointedCone.hull ℝ {i v} :=
    ρ.eq_hull_singleton hρ hv.mem (by simpa using hi.injective.ne hv.ne_zero)
  have hwρ : i w ∈ ρ.toPointedCone := hw.mem
  rw [hρeq] at hwρ
  obtain ⟨a, ha, haw⟩ := PointedCone.mem_hull_singleton.mp hwρ
  obtain ⟨f, hfv⟩ := isPrimitive_def.mp hv.isPrimitive
  let g : V →ₗ[ℝ] ℝ := hi.extend (Int.castAddHom ℝ) f.toAddMonoidHom
  have hg (x : N) : g (i x) = (f x : ℝ) := by
    have hcast (z : ℤ) : (Int.castAddHom ℝ) z = (z : ℝ) := rfl
    have hcoe : f.toAddMonoidHom x = f x := rfl
    simpa only [g, hcast, hcoe] using
      hi.extend_apply (Int.castAddHom ℝ) f.toAddMonoidHom x
  have haInt : a = (f w : ℝ) := by
    have h := congrArg g haw
    rw [map_smul, hg, hg, hfv, Int.cast_one, smul_eq_mul, mul_one] at h
    exact h
  let k := f w
  have hk0 : 0 ≤ k := by exact_mod_cast haInt ▸ ha
  let m := k.toNat
  have hmk : (m : ℤ) = k := Int.toNat_of_nonneg hk0
  have ham : a = (m : ℝ) := by
    calc
      a = (k : ℝ) := haInt
      _ = (m : ℝ) := by exact_mod_cast hmk.symm
  have hwv : w = m • v := by
    apply hi.injective
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, ← ham, haw]
  exact (hwv.trans (by rw [hw.isPrimitive.eq_one_of_eq_nsmul hwv, one_nsmul])).symm

namespace IsToricCone

theorem existsUnique_primitiveGenerator {ρ : ToricRay σ}
    (hρ : IsToricCone i ρ.toPointedCone) (hi : IsIntegralLattice i) :
    ∃! v : N, IsPrimitiveGenerator i ρ v := by
  let _ := hi.free
  obtain ⟨n, hnρ, hn0⟩ := hρ.rational.exists_mem_ne_zero ρ.toPointedCone_ne_bot
  have hn : n ≠ 0 := fun h ↦ hn0 (by simp [h])
  obtain ⟨d, v, hd, hv, hnv⟩ := exists_eq_zsmul_isPrimitive hn
  have hdℝ : (0 : ℝ) < d := by exact_mod_cast hd
  have hvρ : i v ∈ ρ := by
    have hscaled := ρ.toPointedCone.smul_mem (inv_nonneg.mpr hdℝ.le) hnρ
    rw [hnv, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ,
      inv_smul_smul₀ hdℝ.ne'] at hscaled
    exact hscaled
  have hvgen : IsPrimitiveGenerator i ρ v := ⟨hvρ, hv⟩
  exact ⟨v, hvgen, fun _ hu ↦ (hvgen.unique hi hρ.salient hu).symm⟩

end IsToricCone

noncomputable def primitiveGenerator (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : N :=
  ((hσ.face ρ.1).existsUnique_primitiveGenerator hi).choose

theorem isPrimitiveGenerator_primitiveGenerator (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (ρ : ToricRay σ) :
    IsPrimitiveGenerator i ρ (primitiveGenerator hi hσ ρ) :=
  ((hσ.face ρ.1).existsUnique_primitiveGenerator hi).choose_spec.1

@[simp]
theorem primitiveGenerator_mem (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : i (primitiveGenerator hi hσ ρ) ∈ ρ :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ ρ).mem

@[simp]
theorem primitiveGenerator_isPrimitive (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : IsPrimitive (primitiveGenerator hi hσ ρ) :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ ρ).isPrimitive

@[simp]
theorem primitiveGenerator_ne_zero (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : primitiveGenerator hi hσ ρ ≠ 0 :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ ρ).ne_zero

theorem IsPrimitiveGenerator.eq_primitiveGenerator {ρ : ToricRay σ} {v : N}
    (hv : IsPrimitiveGenerator i ρ v)
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) :
    v = primitiveGenerator hi hσ ρ :=
  ((hσ.face ρ.1).existsUnique_primitiveGenerator hi).choose_spec.2 v hv

end TauCeti.Toric
