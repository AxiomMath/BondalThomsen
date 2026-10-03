module

public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.AffineScheme

@[expose] public section

open AlgebraicGeometry Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

noncomputable abbrev denseTorusScheme (hi : IsIntegralLattice i) : Scheme :=
  affineToricScheme 𝕜 hi (⊥ : PointedCone ℝ V)

noncomputable def denseTorusDualEquiv (hi : IsIntegralLattice i) :
    dualSemigroup hi (⊥ : PointedCone ℝ V) ≃+ (N →+ ℤ) where
  toFun := Subtype.val
  invFun m := ⟨m, by simp⟩
  left_inv m := rfl
  right_inv m := rfl
  map_add' := fun _ _ => rfl

noncomputable def denseTorusCoordinateRingEquiv (hi : IsIntegralLattice i) :
    affineCoordinateRing 𝕜 hi (⊥ : PointedCone ℝ V) ≃ₐ[𝕜]
      MonoidAlgebra 𝕜 (Multiplicative (N →+ ℤ)) :=
  MonoidAlgebra.domCongr (R := 𝕜) (A := 𝕜) (denseTorusDualEquiv hi).toMultiplicative

@[simp]
theorem denseTorusDualEquiv_apply (hi : IsIntegralLattice i)
    (m : dualSemigroup hi (⊥ : PointedCone ℝ V)) :
    denseTorusDualEquiv hi m = (m : N →+ ℤ) := by
  simp [denseTorusDualEquiv]

@[simp]
theorem denseTorusCoordinateRingEquiv_single (hi : IsIntegralLattice i)
    (m : dualSemigroup hi (⊥ : PointedCone ℝ V)) (z : 𝕜) :
    denseTorusCoordinateRingEquiv 𝕜 hi (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd (m : N →+ ℤ)) z := by
  simp [denseTorusCoordinateRingEquiv, MonoidAlgebra.domCongr_single,
    denseTorusDualEquiv_apply]

end TauCeti.Toric
