module

public import Mathlib.AlgebraicGeometry.Gluing
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.FaceLocalization

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)

noncomputable def affineToricDiagram : Φ.cones ⥤ Scheme where
  obj σ := Φ.affineToricChart 𝕜 σ
  map {τ σ} f := faceAffineToricSchemeMap 𝕜 Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f))
  map_id _ := faceAffineToricSchemeMap_id 𝕜 _
  map_comp _ _ := (faceAffineToricSchemeMap_comp 𝕜 ..).symm

@[simp]
theorem affineToricDiagram_map {τ σ : Φ.cones} (f : τ ⟶ σ) :
    (Φ.affineToricDiagram 𝕜).map f =
      faceAffineToricSchemeMap 𝕜 Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f)) :=
  (rfl)

variable {Φ}

theorem isOpenImmersion_affineToricDiagram_map {τ σ : Φ.cones} (hσ : IsRegularCone i σ.1)
    (f : τ ⟶ σ) : IsOpenImmersion ((Φ.affineToricDiagram 𝕜).map f) := by
  rw [affineToricDiagram_map]
  exact hσ.isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _

theorem isLocallyDirected_affineToricDiagram (hΦ : Φ.IsRegular) :
    (Φ.affineToricDiagram 𝕜 ⋙ Scheme.forget).IsLocallyDirected := by
  refine ⟨fun {τ υ σ} fτ fυ xτ xυ h ↦ ?_⟩
  have hτσ := Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom fτ)
  have hυσ := Φ.isFaceOf_of_le σ.2 υ.2 (leOfHom fυ)
  have h' : faceAffineToricSchemeMap 𝕜 Φ.lattice hτσ xτ =
      faceAffineToricSchemeMap 𝕜 Φ.lattice hυσ xυ := h
  have hσ := isRegular_iff.1 hΦ _ σ.2
  have := hσ.isOpenImmersion_faceAffineToricSchemeMap 𝕜 Φ.lattice hτσ
  have := hσ.isOpenImmersion_faceAffineToricSchemeMap 𝕜 Φ.lattice hυσ
  obtain ⟨x, hx⟩ : faceAffineToricSchemeMap 𝕜 Φ.lattice hτσ xτ ∈
      Set.range (faceAffineToricSchemeMap 𝕜 Φ.lattice (hτσ.inf_left hυσ)) := by
    rw [hσ.range_faceAffineToricSchemeMap_inf 𝕜 Φ.lattice hτσ hυσ]
    exact ⟨⟨xτ, rfl⟩, ⟨xυ, h'.symm⟩⟩
  have hτ : faceAffineToricSchemeMap 𝕜 Φ.lattice (Φ.isFaceOf_of_le τ.2 (Φ.inf_mem τ.2 υ.2)
      inf_le_left) x = xτ := by
    apply (faceAffineToricSchemeMap 𝕜 Φ.lattice hτσ).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp, hx]
  have hυ : faceAffineToricSchemeMap 𝕜 Φ.lattice (Φ.isFaceOf_of_le υ.2 (Φ.inf_mem τ.2 υ.2)
      inf_le_right) x = xυ := by
    apply (faceAffineToricSchemeMap 𝕜 Φ.lattice hυσ).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp, hx, h']
  exact ⟨τ ⊓ υ, homOfLE (Subtype.coe_le_coe.1 inf_le_left),
    homOfLE (Subtype.coe_le_coe.1 inf_le_right), x, hτ, hυ⟩

variable (Φ)

noncomputable def algebraicRealization (hΦ : Φ.IsRegular) : Scheme :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit (Φ.affineToricDiagram 𝕜)

noncomputable def affineToricChartι (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    Φ.affineToricChart 𝕜 σ ⟶ Φ.algebraicRealization 𝕜 hΦ :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit.ι (Φ.affineToricDiagram 𝕜) σ

noncomputable def affineToricCocone (hΦ : Φ.IsRegular) :
    Cocone (Φ.affineToricDiagram 𝕜) :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit.cocone (Φ.affineToricDiagram 𝕜)

@[simp]
theorem affineToricCocone_ι_app (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    (Φ.affineToricCocone 𝕜 hΦ).ι.app σ = Φ.affineToricChartι 𝕜 hΦ σ :=
  by
    unfold affineToricCocone affineToricChartι
    rfl

noncomputable def isColimitAffineToricCocone (hΦ : Φ.IsRegular) :
    IsColimit (Φ.affineToricCocone 𝕜 hΦ) :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit.isColimit (Φ.affineToricDiagram 𝕜)

@[ext]
theorem algebraicRealization_hom_ext (hΦ : Φ.IsRegular) {X : Scheme}
    {g h : Φ.algebraicRealization 𝕜 hΦ ⟶ X}
    (H : ∀ σ, Φ.affineToricChartι 𝕜 hΦ σ ≫ g = Φ.affineToricChartι 𝕜 hΦ σ ≫ h) : g = h := by
  apply (Φ.isColimitAffineToricCocone 𝕜 hΦ).hom_ext
  intro σ
  rw [Fan.affineToricCocone_ι_app]
  exact H σ

variable {Φ}

variable {𝕜} in
instance isOpenImmersion_affineToricChartι (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    IsOpenImmersion (Φ.affineToricChartι 𝕜 hΦ σ) :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  inferInstanceAs (IsOpenImmersion (colimit.ι (Φ.affineToricDiagram 𝕜) σ))

@[reassoc (attr := simp)]
theorem faceAffineToricSchemeMap_comp_affineToricChartι (hΦ : Φ.IsRegular) {τ σ : Φ.cones}
    (h : τ.1.IsFaceOf σ.1) :
    faceAffineToricSchemeMap 𝕜 Φ.lattice h ≫ Φ.affineToricChartι 𝕜 hΦ σ =
      Φ.affineToricChartι 𝕜 hΦ τ :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  colimit.w (Φ.affineToricDiagram 𝕜) (homOfLE h.le)

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)

@[reassoc]
theorem affineToricOverlapLeft_comp_affineToricChartι (hΦ : Φ.IsRegular) (σ τ : Φ.cones) :
    Φ.affineToricOverlapLeft 𝕜 σ τ ≫ Φ.affineToricChartι 𝕜 hΦ σ =
      Φ.affineToricChartι 𝕜 hΦ (σ ⊓ τ) := by
  simpa only [affineToricOverlapLeft_def] using
    faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 hΦ
      (τ := σ ⊓ τ) (σ := σ)
      (Φ.inf_isFaceOf_left σ.2 τ.2)

@[reassoc]
theorem affineToricOverlapRight_comp_affineToricChartι (hΦ : Φ.IsRegular) (σ τ : Φ.cones) :
    Φ.affineToricOverlapRight 𝕜 σ τ ≫ Φ.affineToricChartι 𝕜 hΦ τ =
      Φ.affineToricChartι 𝕜 hΦ (σ ⊓ τ) := by
  simpa only [affineToricOverlapRight_def] using
    faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 hΦ
      (τ := σ ⊓ τ) (σ := τ)
      (Φ.inf_isFaceOf_right σ.2 τ.2)

theorem affineToricOverlap_comp_affineToricChartι (hΦ : Φ.IsRegular) (σ τ : Φ.cones) :
    Φ.affineToricOverlapLeft 𝕜 σ τ ≫ Φ.affineToricChartι 𝕜 hΦ σ =
      Φ.affineToricOverlapRight 𝕜 σ τ ≫ Φ.affineToricChartι 𝕜 hΦ τ := by
  rw [affineToricOverlapLeft_comp_affineToricChartι,
    affineToricOverlapRight_comp_affineToricChartι]

theorem exists_affineToricChartι_apply_eq (hΦ : Φ.IsRegular) (x : Φ.algebraicRealization 𝕜 hΦ) :
    ∃ (σ : Φ.cones) (y : Φ.affineToricChart 𝕜 σ), Φ.affineToricChartι 𝕜 hΦ σ y = x :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  Scheme.IsLocallyDirected.ι_jointly_surjective (Φ.affineToricDiagram 𝕜) x

theorem affineToricChartι_eq_affineToricChartι_iff (hΦ : Φ.IsRegular)
    {σ τ : Φ.cones} (x : Φ.affineToricChart 𝕜 σ) (y : Φ.affineToricChart 𝕜 τ) :
    Φ.affineToricChartι 𝕜 hΦ σ x = Φ.affineToricChartι 𝕜 hΦ τ y ↔
      ∃ z : Φ.affineToricOverlap 𝕜 σ τ,
        Φ.affineToricOverlapLeft 𝕜 σ τ z = x ∧ Φ.affineToricOverlapRight 𝕜 σ τ z = y := by
  have := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map 𝕜 (isRegular_iff.1 hΦ _ σ.2) f
  have := isLocallyDirected_affineToricDiagram 𝕜 hΦ
  let στ : Φ.cones := σ ⊓ τ
  refine ⟨fun h ↦ ?_, fun ⟨z, hzx, hzy⟩ ↦ ?_⟩
  · obtain ⟨κ, fσ, fτ, (w : Φ.affineToricChart 𝕜 κ), hwx, hwy⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (Φ.affineToricDiagram 𝕜)).1 h
    have hκ : κ.1.IsFaceOf στ.1 := Φ.isFaceOf_of_le στ.2 κ.2 (le_inf (leOfHom fσ) (leOfHom fτ))
    refine ⟨faceAffineToricSchemeMap 𝕜 Φ.lattice hκ w, ?_, ?_⟩
    · rw [affineToricOverlapLeft_def, ← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp]
      exact hwx
    · rw [affineToricOverlapRight_def, ← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp]
      exact hwy
  · rw [← hzx, ← hzy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      affineToricOverlapLeft_comp_affineToricChartι,
      affineToricOverlapRight_comp_affineToricChartι]

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanHom

universe u

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V}
  {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

noncomputable def affineToricChartMap (f : FanHom Φ Ψ) (σ : Φ.cones) :
    Φ.affineToricChart 𝕜 σ ⟶
      Ψ.affineToricChart 𝕜 ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ :=
  affineToricSchemeMap 𝕜 (σ := σ.1) (τ := f.leastCone σ.2)
    Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
    (show Set.MapsTo f.realMap (σ.1 : Set V) (f.leastCone σ.2 : Set V') from
      fun x hx ↦ f.map_le_leastCone σ.2 ⟨x, hx, rfl⟩)

theorem affineToricChartMap_def (f : FanHom Φ Ψ) (σ : Φ.cones) :
    f.affineToricChartMap 𝕜 σ =
      affineToricSchemeMap 𝕜 (σ := σ.1) (τ := f.leastCone σ.2)
        Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
        (show Set.MapsTo f.realMap (σ.1 : Set V) (f.leastCone σ.2 : Set V') from
          fun x hx ↦ f.map_le_leastCone σ.2 ⟨x, hx, rfl⟩) := by
  rfl

@[reassoc (attr := simp)]
theorem faceAffineToricSchemeMap_comp_affineToricChartMap (f : FanHom Φ Ψ)
    {τ σ : Φ.cones} (h : τ.1.IsFaceOf σ.1) :
    faceAffineToricSchemeMap 𝕜 Φ.lattice h ≫ f.affineToricChartMap 𝕜 σ =
      f.affineToricChartMap 𝕜 τ ≫ faceAffineToricSchemeMap 𝕜 Ψ.lattice
        (f.leastCone_isFaceOf (τ := τ.1) (σ := σ.1) σ.2 h) := by
  rw [affineToricChartMap_def, affineToricChartMap_def]
  rw [faceAffineToricSchemeMap_eq_affineToricSchemeMap,
    faceAffineToricSchemeMap_eq_affineToricSchemeMap]
  rw [affineToricSchemeMap_comp, affineToricSchemeMap_comp]
  simp

noncomputable def algebraicMapCocone (f : FanHom Φ Ψ) (hΨ : Ψ.IsRegular) :
    Cocone (Φ.affineToricDiagram 𝕜) where
  pt := Ψ.algebraicRealization 𝕜 hΨ
  ι :=
    { app := fun σ ↦ f.affineToricChartMap 𝕜 σ ≫
        Ψ.affineToricChartι 𝕜 hΨ ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
      naturality := by
        intro τ σ h
        dsimp [Fan.affineToricDiagram]
        simp only [Category.comp_id]
        rw [faceAffineToricSchemeMap_comp_affineToricChartMap_assoc]
        have hface := Fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 hΨ
          (τ := ⟨f.leastCone τ.2, f.leastCone_mem τ.2⟩)
          (σ := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩)
          (f.leastCone_isFaceOf (τ := τ.1) (σ := σ.1) σ.2
            (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom h)))
        simpa only [Category.assoc] using
          congrArg (fun g ↦ f.affineToricChartMap 𝕜 τ ≫ g) hface }

noncomputable def algebraicMap (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) :
    Φ.algebraicRealization 𝕜 hΦ ⟶ Ψ.algebraicRealization 𝕜 hΨ :=
  (Φ.isColimitAffineToricCocone 𝕜 hΦ).desc (f.algebraicMapCocone 𝕜 hΨ)

@[reassoc (attr := simp)]
theorem affineToricChartι_comp_algebraicMap (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular)
    (hΨ : Ψ.IsRegular) (σ : Φ.cones) :
    Φ.affineToricChartι 𝕜 hΦ σ ≫ f.algebraicMap 𝕜 hΦ hΨ =
      f.affineToricChartMap 𝕜 σ ≫
        Ψ.affineToricChartι 𝕜 hΨ ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ :=
  (Φ.isColimitAffineToricCocone 𝕜 hΦ).fac (f.algebraicMapCocone 𝕜 hΨ) σ

@[simp]
theorem algebraicMap_id (Φ : Fan i) (hΦ : Φ.IsRegular) :
    (FanHom.id Φ).algebraicMap 𝕜 hΦ hΦ = 𝟙 (Φ.algebraicRealization 𝕜 hΦ) := by
  apply Fan.algebraicRealization_hom_ext 𝕜 Φ hΦ
  intro σ
  rw [affineToricChartι_comp_algebraicMap]
  have hσleast : σ.1.IsFaceOf ((FanHom.id Φ).leastCone σ.2) :=
    Φ.isFaceOf_of_le ((FanHom.id Φ).leastCone_mem σ.2) σ.2
      (by simpa only [FanHom.id_realMap, PointedCone.map_id] using
        (FanHom.id Φ).map_le_leastCone σ.2)
  have hmap : (FanHom.id Φ).affineToricChartMap 𝕜 σ =
      faceAffineToricSchemeMap 𝕜 Φ.lattice hσleast := by
    rw [affineToricChartMap_def, faceAffineToricSchemeMap_eq_affineToricSchemeMap]
    simp only [FanHom.id_latticeMap, FanHom.id_realMap]
  rw [hmap, Fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 (Φ := Φ) hΦ
    (τ := σ) (σ := ⟨(FanHom.id Φ).leastCone σ.2, (FanHom.id Φ).leastCone_mem σ.2⟩)
    hσleast]
  simp

section

variable {N'' : Type u} {V'' : Type*} [AddCommGroup N''] [AddCommGroup V''] [Module ℝ V'']
  {i'' : N'' →+ V''} {Ω : Fan i''}

theorem algebraicMap_comp (g : FanHom Ψ Ω) (f : FanHom Φ Ψ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hΩ : Ω.IsRegular) :
    (g.comp f).algebraicMap 𝕜 hΦ hΩ = f.algebraicMap 𝕜 hΦ hΨ ≫ g.algebraicMap 𝕜 hΨ hΩ := by
  apply Fan.algebraicRealization_hom_ext 𝕜 Φ hΦ
  intro σ
  let τ : Ψ.cones := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
  let υ : Ω.cones := ⟨g.leastCone τ.2, g.leastCone_mem τ.2⟩
  let κ : Ω.cones := ⟨(g.comp f).leastCone σ.2, (g.comp f).leastCone_mem σ.2⟩
  have hκ_le_υ : κ.1 ≤ υ.1 := by
    apply (g.comp f).leastCone_le σ.2 (g.leastCone_mem τ.2)
    rw [FanHom.comp_realMap, ← PointedCone.map_map]
    exact (Submodule.map_mono (f.map_le_leastCone σ.2)).trans (g.map_le_leastCone τ.2)
  have hκυ : κ.1.IsFaceOf υ.1 := Ω.isFaceOf_of_le υ.2 κ.2 hκ_le_υ
  have hchart :
      (g.comp f).affineToricChartMap 𝕜 σ ≫ faceAffineToricSchemeMap 𝕜 Ω.lattice hκυ =
        f.affineToricChartMap 𝕜 σ ≫ g.affineToricChartMap 𝕜 τ := by
    rw [affineToricChartMap_def, affineToricChartMap_def, affineToricChartMap_def,
      faceAffineToricSchemeMap_eq_affineToricSchemeMap]
    rw [affineToricSchemeMap_comp, affineToricSchemeMap_comp]
    simp [FanHom.comp_latticeMap, FanHom.comp_realMap]
  rw [affineToricChartι_comp_algebraicMap]
  rw [affineToricChartι_comp_algebraicMap_assoc]
  rw [affineToricChartι_comp_algebraicMap]
  rw [← Fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 hΩ hκυ]
  rw [← Category.assoc, hchart]
  simp only [τ, υ, Category.assoc]

end

end FanHom

end Toric

end TauCeti
