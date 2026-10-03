module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import BondalThomsen.Ports.TauCeti.Algebra.MonoidAlgebra.Localization
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.AffineScheme
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Face

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric

universe u

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ : PointedCone ℝ V}

variable {τ υ : PointedCone ℝ V}

noncomputable def faceAffineCoordinateRingMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) : affineCoordinateRing 𝕜 hi σ →ₐ[𝕜] (affineCoordinateRing 𝕜) hi τ :=
  affineCoordinateRingMap 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
    fun _ hx ↦ hτσ.le hx

@[simp]
theorem faceAffineCoordinateRingMap_single (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) (m : dualSemigroup hi σ) (z : 𝕜) :
    faceAffineCoordinateRingMap 𝕜 hi hτσ (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd ⟨m, dualSemigroup_anti hi hτσ.le m.2⟩) z := by
  rw [faceAffineCoordinateRingMap]
  convert affineCoordinateRingMap_single 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id
    (fun _ ↦ rfl) (fun _ hx ↦ hτσ.le hx) m z using 1
  apply congrArg (fun u ↦ MonoidAlgebra.single (ofAdd u) z)
  apply Subtype.ext
  exact (coe_dualSemigroupMap_id hi (fun _ hx ↦ hτσ.le hx) m).symm

@[simp]
theorem faceAffineCoordinateRingMap_id (hi : IsIntegralLattice i) :
    faceAffineCoordinateRingMap 𝕜 hi (PointedCone.IsFaceOf.refl σ) =
      AlgHom.id 𝕜 (affineCoordinateRing 𝕜 hi σ) :=
  affineCoordinateRingMap_id 𝕜 hi σ

noncomputable def faceAffineToricSchemeMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) : affineToricScheme 𝕜 hi τ ⟶ affineToricScheme 𝕜 hi σ :=
  affineToricSchemeMap 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
    (show Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) (τ : Set V) (σ : Set V) from
      fun _ hx ↦ hτσ.le hx)

theorem faceAffineToricSchemeMap_def (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap 𝕜 hi hτσ =
      Spec.map (CommRingCat.ofHom (faceAffineCoordinateRingMap 𝕜 hi hτσ).toRingHom) :=
  by
    rw [faceAffineToricSchemeMap, faceAffineCoordinateRingMap]
    exact affineToricSchemeMap_def 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      (fun _ hx ↦ hτσ.le hx)

theorem faceAffineToricSchemeMap_eq_affineToricSchemeMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap 𝕜 hi hτσ =
      affineToricSchemeMap 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        (show Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) (τ : Set V) (σ : Set V) from
          fun _ hx ↦ hτσ.le hx) := by
  rw [faceAffineToricSchemeMap_def, affineToricSchemeMap_def]
  congr 1

@[simp]
theorem faceAffineToricSchemeMap_id (hi : IsIntegralLattice i) :
    faceAffineToricSchemeMap 𝕜 hi (PointedCone.IsFaceOf.refl σ) =
      𝟙 (affineToricScheme 𝕜 hi σ) := by
  rw [faceAffineToricSchemeMap_def, faceAffineCoordinateRingMap_id]
  exact Spec.map_id _

@[simp]
theorem faceAffineToricSchemeMap_comp (hi : IsIntegralLattice i)
    (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    faceAffineToricSchemeMap 𝕜 hi hυτ ≫ faceAffineToricSchemeMap 𝕜 hi hτσ =
      faceAffineToricSchemeMap 𝕜 hi (hυτ.trans hτσ) := by
  simp only [faceAffineToricSchemeMap]
  exact affineToricSchemeMap_comp 𝕜 hi hi hi (AddMonoidHom.id N) (AddMonoidHom.id N)
    LinearMap.id LinearMap.id (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ hx ↦ hυτ.le hx) (fun _ hx ↦ hτσ.le hx)

theorem isLocalization_away_affineCoordinateRingMap_inf_ker (hi : IsIntegralLattice i)
    (hσ : σ.FG) (m : dualSemigroup hi σ) :
    letI := (affineCoordinateRingMap 𝕜
      (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ) hi hi
      (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)).toRingHom.toAlgebra
    IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : 𝕜))
      (affineCoordinateRing 𝕜 hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) := by
  set F := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))
  have hmaps : Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) F σ := fun _ hx ↦ hx.1
  set f := AddMonoidHom.toMultiplicative
    (dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) hmaps)
  have hf : ∀ u, ((toAdd (f u) : dualSemigroup hi F) : N →+ ℤ) = toAdd u := fun u ↦
    coe_dualSemigroupMap_id hi hmaps _
  have hring : (affineCoordinateRingMap 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      hmaps).toRingHom = MonoidAlgebra.mapDomainRingHom 𝕜 f := by
    have halg : affineCoordinateRingMap 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        hmaps = MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜 f := by
      refine MonoidAlgebra.algHom_ext (fun u ↦ ?_) (Subsingleton.elim _ _)
      obtain ⟨u, rfl⟩ := ofAdd.surjective u
      simp [f]
    rw [halg]
    ext <;> simp
  rw [hring]
  refine MonoidAlgebra.isLocalization_away_mapDomainRingHom 𝕜 f ?_ (ofAdd m) ?_ ?_
  · intro u v huv
    apply toAdd.injective
    apply Subtype.ext
    rw [← hf, ← hf, huv]
  ·
    refine IsUnit.of_mul_eq_one (ofAdd ⟨-(m : N →+ ℤ), neg_mem_dualSemigroup_inf_ker hi σ m⟩) ?_
    apply toAdd.injective
    apply Subtype.ext
    simp [hf]
  · intro y
    obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ m.2 (toAdd y).2
    refine ⟨n, ofAdd ⟨_, hn⟩, ?_⟩
    apply toAdd.injective
    apply Subtype.ext
    simp [hf]

theorem isOpenImmersion_affineToricSchemeMap_inf_ker {N : Type u} [AddCommGroup N]
    {i : N →+ V} (hi : IsIntegralLattice i) (hσ : σ.FG) (m : dualSemigroup hi σ) :
    IsOpenImmersion (affineToricSchemeMap 𝕜
      (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ)
      hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)) := by
  let := (affineCoordinateRingMap 𝕜
    (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ)
    hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)).toRingHom.toAlgebra
  have := isLocalization_away_affineCoordinateRingMap_inf_ker 𝕜 hi hσ m
  have h := IsOpenImmersion.of_isLocalization
    (S := affineCoordinateRing 𝕜 hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))
    (MonoidAlgebra.single (ofAdd m) (1 : 𝕜))
  rw [RingHom.algebraMap_toAlgebra] at h
  convert h using 1
  exact affineToricSchemeMap_def 𝕜 ..

theorem range_faceAffineToricSchemeMap_of_eq (hi : IsIntegralLattice i) (hσ : σ.FG)
    (hτσ : τ.IsFaceOf σ) (m : dualSemigroup hi σ)
    (hm : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ) :
    Set.range (faceAffineToricSchemeMap 𝕜 hi hτσ) =
      (PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd m) (1 : 𝕜)) :
        Set (PrimeSpectrum (affineCoordinateRing 𝕜 hi σ))) := by
  subst hm
  let := (faceAffineCoordinateRingMap 𝕜 hi hτσ).toRingHom.toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : 𝕜))
      (affineCoordinateRing 𝕜 hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
    isLocalization_away_affineCoordinateRingMap_inf_ker 𝕜 hi hσ m
  rw [faceAffineToricSchemeMap_def]
  exact PrimeSpectrum.localization_away_comap_range _ _

namespace IsRegularCone

variable {τ : PointedCone ℝ V}

theorem exists_isLocalization_away_faceAffineCoordinateRingMap (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (hτ : τ.IsFaceOf σ) :
    ∃ m : dualSemigroup hi σ,
      letI := (faceAffineCoordinateRingMap 𝕜 hi hτ).toRingHom.toAlgebra
      IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : 𝕜))
        (affineCoordinateRing 𝕜 hi τ) := by
  obtain ⟨m, hm, rfl⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  have hh : hτ = PointedCone.isFaceOf_inf_ker
      ((mem_dualSemigroup hi m).1 hm) := Subsingleton.elim _ _
  subst hτ
  refine ⟨⟨m, hm⟩, ?_⟩
  rw [faceAffineCoordinateRingMap]
  exact isLocalization_away_affineCoordinateRingMap_inf_ker 𝕜 hi hσ.fg ⟨m, hm⟩

theorem isOpenImmersion_faceAffineToricSchemeMap {N : Type u} [AddCommGroup N] {i : N →+ V}
    (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) (hτ : τ.IsFaceOf σ) :
    IsOpenImmersion (faceAffineToricSchemeMap 𝕜 hi hτ) := by
  obtain ⟨m, hm, rfl⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  have hh : hτ = PointedCone.isFaceOf_inf_ker
      ((mem_dualSemigroup hi m).1 hm) := Subsingleton.elim _ _
  subst hτ
  rw [faceAffineToricSchemeMap_def, faceAffineCoordinateRingMap]
  convert isOpenImmersion_affineToricSchemeMap_inf_ker 𝕜 hi hσ.fg ⟨m, hm⟩ using 1
  exact (affineToricSchemeMap_def 𝕜 ..).symm

theorem range_faceAffineToricSchemeMap_inf (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {υ : PointedCone ℝ V} (hτ : τ.IsFaceOf σ) (hυ : υ.IsFaceOf σ) :
    Set.range (faceAffineToricSchemeMap 𝕜 hi (hτ.inf_left hυ)) =
      Set.range (faceAffineToricSchemeMap 𝕜 hi hτ) ∩ Set.range (faceAffineToricSchemeMap 𝕜 hi hυ) := by
  obtain ⟨m₁, hm₁, h₁⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  obtain ⟨m₂, hm₂, h₂⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hυ
  have hmul : MonoidAlgebra.single (ofAdd (⟨m₁, hm₁⟩ + ⟨m₂, hm₂⟩ : dualSemigroup hi σ)) (1 : 𝕜) =
      MonoidAlgebra.single (ofAdd ⟨m₁, hm₁⟩) 1 * MonoidAlgebra.single (ofAdd ⟨m₂, hm₂⟩) 1 := by
    rw [MonoidAlgebra.single_mul_single, ofAdd_add, mul_one]
  rw [range_faceAffineToricSchemeMap_of_eq 𝕜 hi hσ.fg hτ ⟨m₁, hm₁⟩ h₁,
    range_faceAffineToricSchemeMap_of_eq 𝕜 hi hσ.fg hυ ⟨m₂, hm₂⟩ h₂,
    range_faceAffineToricSchemeMap_of_eq 𝕜 hi hσ.fg _ (⟨m₁, hm₁⟩ + ⟨m₂, hm₂⟩)
      (by rw [AddSubmonoid.coe_add, map_add, PointedCone.inf_ker_add
        ((mem_dualSemigroup hi m₁).1 hm₁) ((mem_dualSemigroup hi m₂).1 hm₂), h₁, h₂]),
    hmul, PrimeSpectrum.basicOpen_mul]
  exact TopologicalSpace.Opens.coe_inf ..

end IsRegularCone

namespace Fan

variable (Φ : Fan i)

noncomputable abbrev affineToricChart (σ : Φ.cones) : Scheme :=
  affineToricScheme 𝕜 Φ.lattice σ

noncomputable abbrev affineToricOverlap (σ τ : Φ.cones) : Scheme :=
  affineToricScheme 𝕜 Φ.lattice (σ.1 ⊓ τ.1)

noncomputable def affineToricOverlapLeft (σ τ : Φ.cones) :
    Φ.affineToricOverlap 𝕜 σ τ ⟶ Φ.affineToricChart 𝕜 σ :=
  faceAffineToricSchemeMap 𝕜 Φ.lattice
    (Φ.inf_isFaceOf_left σ.property τ.property)

noncomputable def affineToricOverlapRight (σ τ : Φ.cones) :
    Φ.affineToricOverlap 𝕜 σ τ ⟶ Φ.affineToricChart 𝕜 τ :=
  faceAffineToricSchemeMap 𝕜 Φ.lattice
    (Φ.inf_isFaceOf_right σ.property τ.property)

@[simp]
theorem affineToricOverlapLeft_def (σ τ : Φ.cones) :
    Φ.affineToricOverlapLeft 𝕜 σ τ =
      faceAffineToricSchemeMap 𝕜 Φ.lattice (Φ.inf_isFaceOf_left σ.property τ.property) := by
  rw [affineToricOverlapLeft]

@[simp]
theorem affineToricOverlapRight_def (σ τ : Φ.cones) :
    Φ.affineToricOverlapRight 𝕜 σ τ =
      faceAffineToricSchemeMap 𝕜 Φ.lattice (Φ.inf_isFaceOf_right σ.property τ.property) := by
  rw [affineToricOverlapRight]

theorem isOpenImmersion_affineToricOverlapLeft (σ τ : Φ.cones)
    (hσ : IsRegularCone i σ.1) :
    IsOpenImmersion (Φ.affineToricOverlapLeft 𝕜 σ τ) :=
  hσ.isOpenImmersion_faceAffineToricSchemeMap 𝕜 Φ.lattice
    (Φ.inf_isFaceOf_left σ.property τ.property)

theorem isOpenImmersion_affineToricOverlapRight (σ τ : Φ.cones)
    (hτ : IsRegularCone i τ.1) :
    IsOpenImmersion (Φ.affineToricOverlapRight 𝕜 σ τ) :=
  hτ.isOpenImmersion_faceAffineToricSchemeMap 𝕜 Φ.lattice
    (Φ.inf_isFaceOf_right σ.property τ.property)

end Fan

end TauCeti.Toric
