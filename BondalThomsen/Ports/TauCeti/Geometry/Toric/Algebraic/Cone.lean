module

public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Basic
public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Finite

@[expose] public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {σ τ : PointedCone ℝ V}

def IsLatticeRational (i : N →+ V) (σ : PointedCone ℝ V) : Prop :=
  ∃ s : Finset N, σ = PointedCone.hull ℝ (i '' (s : Set N))

@[simp]
theorem isLatticeRational_iff :
    IsLatticeRational i σ ↔ ∃ s : Finset N, σ = PointedCone.hull ℝ (i '' (s : Set N)) := (Iff.rfl)

theorem IsLatticeRational.fg (h : IsLatticeRational i σ) : σ.FG := by
  obtain ⟨s, rfl⟩ := h
  exact Submodule.fg_span ((s : Set N).toFinite.image i)

theorem IsLatticeRational.exists_mem_ne_zero (h : IsLatticeRational i σ) (hσ : σ ≠ ⊥) :
    ∃ v : N, i v ∈ σ ∧ i v ≠ 0 := by
  obtain ⟨s, rfl⟩ := h
  by_contra hcon
  refine hσ (le_antisymm (Submodule.span_le.2 ?_) bot_le)
  rintro _ ⟨v, hv, rfl⟩
  have hmem : i v ∈ PointedCone.hull ℝ (i '' (s : Set N)) := PointedCone.subset_hull ⟨v, hv, rfl⟩
  by_contra hne
  exact hcon ⟨v, hmem, fun h ↦ hne (by simp [h])⟩

theorem IsLatticeRational.sup (hσ : IsLatticeRational i σ) (hτ : IsLatticeRational i τ) :
    IsLatticeRational i (σ ⊔ τ) := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  obtain ⟨t, rfl⟩ := hτ
  refine ⟨s ∪ t, ?_⟩
  rw [Finset.coe_union, Set.image_union]
  exact (Submodule.span_union _ _).symm

structure IsToricCone (i : N →+ V) (σ : PointedCone ℝ V) : Prop where

  rational : IsLatticeRational i σ

  salient : (σ : ConvexCone ℝ V).Salient

theorem IsToricCone.fg (h : IsToricCone i σ) : σ.FG := h.rational.fg

theorem IsLatticeRational.of_isFaceOf (hσ : IsLatticeRational i σ) (hτ : τ.IsFaceOf σ) :
    IsLatticeRational i τ := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  let F : (PointedCone.hull ℝ (i '' (s : Set N))).Face := ⟨τ, hτ⟩
  refine ⟨s.filter fun v ↦ i v ∈ τ,
    (F.eq_hull_inter_of_eq_hull (i '' (s : Set N)) rfl).trans ?_⟩
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image, Finset.coe_filter, Finset.mem_coe]
  aesop

theorem IsToricCone.of_isFaceOf (hσ : IsToricCone i σ) (hτ : τ.IsFaceOf σ) : IsToricCone i τ :=
  ⟨hσ.rational.of_isFaceOf hτ, hσ.salient.anti fun _ hx ↦ hτ.le hx⟩

theorem IsToricCone.face (hσ : IsToricCone i σ) (F : σ.Face) :
    IsToricCone i F.toPointedCone :=
  hσ.of_isFaceOf F.isFaceOf

section Map

variable {f : N →+ N'} {g : V →ₗ[ℝ] V'}

theorem IsLatticeRational.map (hfg : ∀ n, g (i n) = i' (f n)) (hσ : IsLatticeRational i σ) :
    IsLatticeRational i' (PointedCone.map g σ) := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  refine ⟨s.image f, ?_⟩
  have hmap : PointedCone.map g (PointedCone.hull ℝ (i '' (s : Set N))) =
      PointedCone.hull ℝ (g '' (i '' (s : Set N))) := Submodule.map_span _ _
  rw [hmap, ← Set.image_comp]
  congr 1
  ext x
  simp only [Finset.coe_image, Set.mem_image, Function.comp_apply, Set.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨f v, ⟨v, hv, rfl⟩, (hfg v).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, hfg v⟩

theorem IsToricCone.map (hfg : ∀ n, g (i n) = i' (f n)) (hg : Function.Injective g)
    (hσ : IsToricCone i σ) : IsToricCone i' (PointedCone.map g σ) :=
  ⟨hσ.rational.map hfg, hσ.salient.map hg⟩

end Map

lemma image_prodMap_coe_product_union [DecidableEq (N × N')] (s : Finset N)
    (t : Finset N') :
    (i.prodMap i') ''
        ((s ×ˢ ({0} : Finset N') ∪ ({0} : Finset N) ×ˢ t : Finset (N × N')) : Set (N × N')) =
      LinearMap.inl ℝ V V' '' (i '' (s : Set N)) ∪
        LinearMap.inr ℝ V V' '' (i' '' (t : Set N')) := by
  ext ⟨x, y⟩
  simp only [AddMonoidHom.coe_prodMap, Finset.product_singleton, Finset.singleton_product,
    Finset.coe_union, Finset.coe_map, Function.Embedding.sectL_apply,
    Function.Embedding.sectR_apply, Set.mem_image, Set.mem_union, SetLike.mem_coe, Prod.exists,
    Prod.mk.injEq, existsAndEq, true_and, exists_eq_right_right, Prod.map_apply,
    LinearMap.coe_inl, LinearMap.coe_inr, exists_exists_and_eq_and]
  constructor
  · rintro ⟨a, b, hab, hxa, hyb⟩
    rcases hab with ⟨ha, rfl⟩ | ⟨hb, rfl⟩
    · exact Or.inl ⟨a, ha, hxa, by simpa using hyb⟩
    · exact Or.inr ⟨⟨b, hb, hyb⟩, by simpa using hxa⟩
  · rintro (⟨a, ha, hxa, hy⟩ | ⟨⟨b, hb, hyb⟩, hx⟩)
    · exact ⟨a, 0, Or.inl ⟨ha, rfl⟩, hxa, by simpa using hy⟩
    · exact ⟨0, b, Or.inr ⟨hb, rfl⟩, by simpa using hx, hyb⟩

theorem IsLatticeRational.prod {τ' : PointedCone ℝ V'} (hσ : IsLatticeRational i σ)
    (hτ' : IsLatticeRational i' τ') :
    IsLatticeRational (i.prodMap i') (σ.prod τ') := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  obtain ⟨t, rfl⟩ := hτ'
  refine ⟨s ×ˢ ({0} : Finset N') ∪ ({0} : Finset N) ×ˢ t, ?_⟩
  rw [image_prodMap_coe_product_union]
  exact LinearMap.span_inl_union_inr.symm

theorem IsToricCone.prod {τ' : PointedCone ℝ V'} (hσ : IsToricCone i σ)
    (hτ' : IsToricCone i' τ') : IsToricCone (i.prodMap i') (σ.prod τ') :=
  ⟨hσ.rational.prod hτ'.rational, hσ.salient.prod hτ'.salient⟩

end TauCeti.Toric
