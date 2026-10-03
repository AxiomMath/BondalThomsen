module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric

universe u

variable {V V' V'' : Type*} [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'} {υ : PointedCone ℝ V''}

section CoordinateRing

variable {N N' N'' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

abbrev affineCoordinateRing (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :=
  MonoidAlgebra 𝕜 (Multiplicative (dualSemigroup hi σ))

noncomputable def affineCoordinateRingMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) :
    affineCoordinateRing 𝕜 hi' τ →ₐ[𝕜] (affineCoordinateRing 𝕜) hi σ :=
  MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜
    (AddMonoidHom.toMultiplicative (dualSemigroupMap hi hi' f g hfg hστ))

@[simp]
theorem affineCoordinateRingMap_single (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ)
    (m : dualSemigroup hi' τ) (z : 𝕜) :
    affineCoordinateRingMap 𝕜 hi hi' f g hfg hστ
        (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd (dualSemigroupMap hi hi' f g hfg hστ m)) z := by
  simp [affineCoordinateRingMap]

@[simp]
theorem affineCoordinateRingMap_id (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    affineCoordinateRingMap 𝕜 hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        (fun _ hx ↦ hx) = AlgHom.id 𝕜 (affineCoordinateRing 𝕜 hi σ) := by
  simp only [affineCoordinateRingMap, dualSemigroupMap_id, AddMonoidHom.toMultiplicative_id,
    MonoidAlgebra.mapDomainAlgHom_id]

@[simp]
theorem affineCoordinateRingMap_comp (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (hi'' : IsIntegralLattice i'')
    (f : N →+ N') (f' : N' →+ N'') (g : V →ₗ[ℝ] V') (g' : V' →ₗ[ℝ] V'')
    (hfg : ∀ n, g (i n) = i' (f n)) (hf'g' : ∀ n, g' (i' n) = i'' (f' n))
    (hστ : Set.MapsTo g σ τ) (hτυ : Set.MapsTo g' τ υ) :
    (affineCoordinateRingMap 𝕜 hi hi' f g hfg hστ).comp
        (affineCoordinateRingMap 𝕜 hi' hi'' f' g' hf'g' hτυ) =
      affineCoordinateRingMap 𝕜 hi hi'' (f'.comp f) (g'.comp g)
        (fun n ↦ by simp [hfg, hf'g']) (hτυ.comp hστ) := by
  have hcomp :
      AddMonoidHom.toMultiplicative
          ((dualSemigroupMap hi hi' f g hfg hστ).comp
            (dualSemigroupMap hi' hi'' f' g' hf'g' hτυ)) =
        (AddMonoidHom.toMultiplicative (dualSemigroupMap hi hi' f g hfg hστ)).comp
          (AddMonoidHom.toMultiplicative (dualSemigroupMap hi' hi'' f' g' hf'g' hτυ)) := by
    apply MonoidHom.ext
    intro m
    simp only [MonoidHom.comp_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd]
  rw [affineCoordinateRingMap, affineCoordinateRingMap, affineCoordinateRingMap,
    dualSemigroupMap_comp hi hi' hi'' f f' g g' hfg hf'g' hστ hτυ, hcomp,
    ← MonoidAlgebra.mapDomainAlgHom_comp]

end CoordinateRing

section Scheme

variable {N N' N'' : Type u} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

noncomputable abbrev affineToricScheme (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    Scheme :=
  Spec (.of (affineCoordinateRing 𝕜 hi σ))

noncomputable def affineToricSchemeMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) :
    affineToricScheme 𝕜 hi σ ⟶ affineToricScheme 𝕜 hi' τ :=
  Spec.map (CommRingCat.ofHom (affineCoordinateRingMap 𝕜 hi hi' f g hfg hστ).toRingHom)

theorem affineToricSchemeMap_def (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) :
    affineToricSchemeMap 𝕜 hi hi' f g hfg hστ =
      Spec.map (CommRingCat.ofHom (affineCoordinateRingMap 𝕜 hi hi' f g hfg hστ).toRingHom) :=
  (rfl)

@[simp]
theorem affineToricSchemeMap_comp (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (hi'' : IsIntegralLattice i'')
    (f : N →+ N') (f' : N' →+ N'') (g : V →ₗ[ℝ] V') (g' : V' →ₗ[ℝ] V'')
    (hfg : ∀ n, g (i n) = i' (f n)) (hf'g' : ∀ n, g' (i' n) = i'' (f' n))
    (hστ : Set.MapsTo g σ τ) (hτυ : Set.MapsTo g' τ υ) :
    affineToricSchemeMap 𝕜 hi hi' f g hfg hστ ≫
        affineToricSchemeMap 𝕜 hi' hi'' f' g' hf'g' hτυ =
      affineToricSchemeMap 𝕜 hi hi'' (f'.comp f) (g'.comp g)
        (fun n ↦ by simp [hfg, hf'g']) (hτυ.comp hστ) := by
  rw [affineToricSchemeMap, affineToricSchemeMap, affineToricSchemeMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg CommRingCat.ofHom <| congrArg AlgHom.toRingHom
    (affineCoordinateRingMap_comp 𝕜 hi hi' hi'' f f' g g' hfg hf'g' hστ hτυ)

end Scheme

end TauCeti.Toric
