module

public import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.UniformSpace.Real
public import BondalThomsen.Ports.TauCeti.AlgebraicTopology.SimplicialComplex.Basic

@[expose] public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

noncomputable def standardGeometricComplex (K : AbstractSimplicialComplex ι) :
    Geometry.SimplicialComplex ℝ (ι →₀ ℝ) :=
  Geometry.SimplicialComplex.onFinsupp K.toPreAbstractSimplicialComplex

noncomputable abbrev Realization (K : AbstractSimplicialComplex ι) : Type _ :=
  (standardGeometricComplex K).space

noncomputable abbrev StandardSimplex (σ : Finset ι) : Type _ :=
  convexHull ℝ (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ))

instance (σ : Finset ι) : TopologicalSpace (StandardSimplex σ) :=
  TopologicalSpace.induced (fun x : StandardSimplex σ => (x.1 : ι → ℝ)) inferInstance

theorem mem_standardGeometricComplex_faces_iff (K : AbstractSimplicialComplex ι)
    (τ : Finset (ι →₀ ℝ)) :
    τ ∈ (standardGeometricComplex K).faces ↔
      ∃ σ ∈ K, σ.image (fun v => Finsupp.single v (1 : ℝ)) = τ := by
  classical
  simp only [standardGeometricComplex, Geometry.SimplicialComplex.onFinsupp,
    Geometry.SimplicialComplex.ofAffineIndependent, PreAbstractSimplicialComplex.map,
    Set.mem_image]
  aesop

noncomputable def faceInclusion (K : AbstractSimplicialComplex ι) (σ : Face K) :
    StandardSimplex σ.1 → Realization K :=
  Set.inclusion (Geometry.SimplicialComplex.convexHull_subset_space
    (K := standardGeometricComplex K)
      ((mem_standardGeometricComplex_faces_iff K _).2 ⟨σ.1, σ.2, rfl⟩))

@[simp]
theorem faceInclusion_val (K : AbstractSimplicialComplex ι) (σ : Face K) (x : StandardSimplex σ.1) :
    (faceInclusion K σ x : ι →₀ ℝ) = x := by
  exact Set.coe_inclusion
    (Geometry.SimplicialComplex.convexHull_subset_space
      ((mem_standardGeometricComplex_faces_iff K _).2 ⟨σ.1, σ.2, rfl⟩)) x

instance (K : AbstractSimplicialComplex ι) : TopologicalSpace (Realization K) :=
  ⨆ σ : Face K, TopologicalSpace.coinduced (faceInclusion K σ) inferInstance

theorem continuous_faceInclusion (K : AbstractSimplicialComplex ι) (σ : Face K) :
    Continuous (faceInclusion K σ) :=
  continuous_iff_coinduced_le.2 (le_iSup (fun τ : Face K =>
    TopologicalSpace.coinduced (faceInclusion K τ) inferInstance) σ)

theorem continuous_iff_faceInclusion {K : AbstractSimplicialComplex ι}
    {X : Type*} [TopologicalSpace X] {f : Realization K → X} :
    Continuous f ↔ ∀ σ : Face K, Continuous (f ∘ faceInclusion K σ) := by
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

theorem image_single_mem_standardGeometricComplex_faces {K : AbstractSimplicialComplex ι}
    {σ : Finset ι} (hσ : σ ∈ K) :
    σ.image (fun v => Finsupp.single v (1 : ℝ)) ∈ (standardGeometricComplex K).faces :=
  (mem_standardGeometricComplex_faces_iff K _).2 ⟨σ, hσ, rfl⟩

theorem mem_realization_iff {K : AbstractSimplicialComplex ι} {x : ι →₀ ℝ} :
    x ∈ (standardGeometricComplex K).space ↔
      ∃ σ ∈ K, x ∈
        convexHull ℝ (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ)) := by
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨σ, hσ, rfl⟩ := (mem_standardGeometricComplex_faces_iff K τ).1 hτ
    exact ⟨σ, hσ, hx⟩
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ.image (fun v => Finsupp.single v (1 : ℝ)),
      image_single_mem_standardGeometricComplex_faces hσ, hx⟩

theorem StandardSimplex.nonneg {σ : Finset ι} (x : StandardSimplex σ) (v : ι) :
    0 ≤ x.1 v := by
  change x.1 ∈ {y : ι →₀ ℝ | 0 ≤ y v}
  exact convexHull_min (by
      intro y hy
      simp only [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨w, _, rfl⟩ := hy
      by_cases h : w = v <;> simp [h])
    (by
      intro y hy z hz a b ha hb hab
      simp only [Set.mem_ofPred_eq, Finsupp.add_apply, Finsupp.smul_apply] at hy hz ⊢
      exact add_nonneg (mul_nonneg ha hy) (mul_nonneg hb hz))
    x.2

theorem StandardSimplex.sum_eq_one {σ : Finset ι} (x : StandardSimplex σ) :
    x.1.sum (fun _ r => r) = 1 := by
  change x.1.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1
  change x.1 ∈
    {y : ι →₀ ℝ | y.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1}
  exact convexHull_min (by
      intro y hy
      simp only [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨v, _, rfl⟩ := hy
      simp)
    (by
      intro y hy z hz a b _ _ hab
      simp only [Set.mem_ofPred_eq] at hy hz ⊢
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_smul_index_linearMap', Finsupp.sum_smul_index_linearMap', hy, hz]
        simpa [smul_eq_mul] using hab
      all_goals simp)
    x.2

theorem StandardSimplex.support_subset {σ : Finset ι} (x : StandardSimplex σ) :
    x.1.support ⊆ σ := by
  change (x.1.support : Set ι) ⊆ (σ : Set ι)
  change x.1 ∈ Finsupp.supported ℝ ℝ (σ : Set ι)
  exact convexHull_min (by
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    simpa [Finsupp.mem_supported] using hv) (Finsupp.supported ℝ ℝ (σ : Set ι)).convex x.2

@[simp]
theorem mem_standardSimplex_iff {σ : Finset ι} {x : ι →₀ ℝ} :
    x ∈ convexHull ℝ
        ((fun v => Finsupp.single v (1 : ℝ)) '' (σ : Set ι)) ↔
      (∀ v, 0 ≤ x v) ∧ x.sum (fun _ r => r) = 1 ∧ x.support ⊆ σ := by
  constructor
  · intro hx
    rw [← Finset.coe_image] at hx
    let x' : StandardSimplex σ := ⟨x, hx⟩
    exact ⟨StandardSimplex.nonneg x', StandardSimplex.sum_eq_one x',
      StandardSimplex.support_subset x'⟩
  · rintro ⟨hnonneg, hsum, hsupp⟩
    have hsum' :
        x.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1 := by
      change x.sum (fun _ r => r) = 1
      exact hsum
    have hx := (convex_convexHull ℝ
        (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ))).sum_mem
      (fun v _ => hnonneg v) hsum'
      (fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.2 <|
        Finset.mem_image.2 ⟨v, hsupp hv, rfl⟩))
    have heq : (∑ i ∈ x.support, x i • Finsupp.single i (1 : ℝ)) = x := by
      simpa [Finsupp.sum] using x.sum_single
    rw [heq] at hx
    rw [Finset.coe_image] at hx
    exact hx

theorem StandardSimplex.mem_convexHull_support {σ : Finset ι} (x : StandardSimplex σ) :
    x.1 ∈ convexHull ℝ
      (x.1.support.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ)) := by
  have hx := (convex_convexHull ℝ _).sum_mem
    (fun v _ => StandardSimplex.nonneg x v)
    (by
      change x.1.sum (fun _ r => r) = 1
      exact StandardSimplex.sum_eq_one x)
    (fun v hv => subset_convexHull ℝ _ (by
      change Finsupp.single v 1 ∈
        (x.1.support.image (fun w => Finsupp.single w (1 : ℝ)) : Finset (ι →₀ ℝ))
      exact Finset.mem_image.2 ⟨v, hv, rfl⟩))
  have heq : (∑ i ∈ x.1.support, x.1 i • Finsupp.single i (1 : ℝ)) = x.1 := by
    simpa [Finsupp.sum] using x.1.sum_single
  rw [heq] at hx
  exact hx

theorem support_mem (K : AbstractSimplicialComplex ι) (x : Realization K) : x.1.support ∈ K := by
  obtain ⟨σ, hσ, hx⟩ := mem_realization_iff.1 x.2
  let hx' : StandardSimplex σ := ⟨x.1, hx⟩
  have hs : x.1.support ⊆ σ := by
    simpa [hx'] using StandardSimplex.support_subset hx'
  apply K.isRelLowerSet_faces.mem_of_le hσ
    hs
  exact
    (Finsupp.support_nonempty_iff.mpr <| by
      intro h
      have hs := StandardSimplex.sum_eq_one hx'
      have hs' : x.1.sum (fun _ r => r) = 1 := by
        simpa [hx'] using hs
      rw [h] at hs'
      simp at hs')

noncomputable def carrier (K : AbstractSimplicialComplex ι) (x : Realization K) : Face K :=
  ⟨x.1.support, support_mem K x⟩

@[simp]
theorem carrier_val (K : AbstractSimplicialComplex ι) (x : Realization K) :
    (carrier K x).1 = x.1.support :=
  (rfl)

theorem mem_convexHull_carrier (K : AbstractSimplicialComplex ι) (x : Realization K) :
    x.1 ∈ convexHull ℝ
      ((carrier K x).1.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ)) := by
  obtain ⟨σ, _, hx⟩ := mem_realization_iff.1 x.2
  rw [carrier_val]
  exact StandardSimplex.mem_convexHull_support ⟨x.1, hx⟩

theorem Realization.nonneg (K : AbstractSimplicialComplex ι) (x : Realization K) (v : ι) :
    0 ≤ x.1 v :=
  StandardSimplex.nonneg (σ := (carrier K x).1) ⟨x.1, mem_convexHull_carrier K x⟩ v

theorem single_mem_standardGeometricComplex_space (K : AbstractSimplicialComplex ι) (v : ι) :
    Finsupp.single v 1 ∈ (standardGeometricComplex K).space := by
  apply Geometry.SimplicialComplex.vertices_subset_space
  rw [Geometry.SimplicialComplex.mem_vertices]
  simpa using image_single_mem_standardGeometricComplex_faces (K.singleton_mem v)

noncomputable def vertex (K : AbstractSimplicialComplex ι) (v : ι) : Realization K :=
  ⟨Finsupp.single v 1, single_mem_standardGeometricComplex_space K v⟩

@[simp]
theorem vertex_val (K : AbstractSimplicialComplex ι) (v : ι) :
    (vertex K v : ι →₀ ℝ) = Finsupp.single v 1 :=
  (rfl)

instance realizationBotDiscreteTopology :
    DiscreteTopology (Realization (⊥ : AbstractSimplicialComplex ι)) := by
  classical
  rw [discreteTopology_iff_forall_isOpen]
  intro s
  rw [isOpen_iSup_iff]
  intro σ
  rw [isOpen_coinduced]
  obtain ⟨v, hv⟩ := σ.2
  have : Subsingleton (StandardSimplex σ.1) := by
    constructor
    intro x y
    apply Subtype.ext
    have hx : x.1 = Finsupp.single v 1 := by
      simpa only [hv, Finset.image_singleton, Finset.coe_singleton, convexHull_singleton,
        mem_singleton_iff] using x.2
    have hy : y.1 = Finsupp.single v 1 := by
      simpa only [hv, Finset.image_singleton, Finset.coe_singleton, convexHull_singleton,
        mem_singleton_iff] using y.2
    exact hx.trans hy.symm
  exact isOpen_discrete _

end AbstractSimplicialComplex
