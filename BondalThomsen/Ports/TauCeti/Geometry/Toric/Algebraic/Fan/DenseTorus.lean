module

public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DenseTorus
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

noncomputable abbrev denseTorus (Φ : Fan i) : Scheme :=
  denseTorusScheme 𝕜 Φ.lattice

noncomputable def botCone (Φ : Fan i) (hΦ₀ : Nonempty Φ.cones) : Φ.cones :=
  ⟨⊥, Φ.bot_mem hΦ₀.some.property⟩

noncomputable def denseTorusι (Φ : Fan i) (hΦ : Φ.IsRegular)
    (hΦ₀ : Nonempty Φ.cones) : Φ.denseTorus 𝕜 ⟶ Φ.algebraicRealization 𝕜 hΦ :=
  Φ.affineToricChartι 𝕜 hΦ (botCone Φ hΦ₀)

variable {𝕜} in
instance isOpenImmersion_denseTorusι (Φ : Fan i) (hΦ : Φ.IsRegular)
    (hΦ₀ : Nonempty Φ.cones) : IsOpenImmersion (Φ.denseTorusι 𝕜 hΦ hΦ₀) :=
  Φ.isOpenImmersion_affineToricChartι hΦ (botCone Φ hΦ₀)

theorem denseTorusι_eq (Φ : Fan i) (hΦ : Φ.IsRegular)
    (hΦ₀ hΦ₁ : Nonempty Φ.cones) :
    Φ.denseTorusι 𝕜 hΦ hΦ₀ = Φ.denseTorusι 𝕜 hΦ hΦ₁ := by
  let σ : Φ.cones := botCone Φ hΦ₀
  have hσ : (Nonempty.intro σ) = hΦ₀ := by rfl
  rw [← hσ]

theorem denseTorusι_face (Φ : Fan i) (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    Φ.denseTorusι 𝕜 hΦ (Nonempty.intro σ) =
      faceAffineToricSchemeMap 𝕜 Φ.lattice
          ((Φ.isToricCone σ.2).salient.bot_isFaceOf) ≫
        Φ.affineToricChartι 𝕜 hΦ σ := by
  have hbot : (⊥ : PointedCone ℝ V).IsFaceOf σ.1 :=
    (Φ.isToricCone σ.2).salient.bot_isFaceOf
  symm
  simpa [denseTorusι, denseTorus, denseTorusScheme, botCone] using
    (faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 (Φ := Φ) hΦ
      (τ := botCone Φ (Nonempty.intro σ)) (σ := σ) hbot)

end TauCeti.Toric.Fan
