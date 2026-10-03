module

public import BondalThomsen.ProjectiveBundle.Fan
public import BondalThomsen.Toric.Scheme.LocalFactorial
public import BondalThomsen.Toric.Scheme.Separated
public import BondalThomsen.Toric.Divisor.DivisorLineBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory Module

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ProjectiveBundle

variable {rows baseDimension columns : ℕ}

noncomputable def scheme (matrix : Matrix (Fin rows) (Fin columns) ℤ) : Scheme :=
  (fan (baseDimension := baseDimension) matrix).algebraicRealization 𝕜 (fan_isRegular matrix)

noncomputable def schemeStructureMap (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    scheme 𝕜 (baseDimension := baseDimension) matrix ⟶ Spec (CommRingCat.of 𝕜) :=
  (fan (baseDimension := baseDimension) matrix).structureMap 𝕜 (fan_isRegular matrix)

theorem ambient_finrank (rows baseDimension columns : ℕ) :
    finrank ℝ (Ambient rows baseDimension columns) = rows * baseDimension + columns := by
  simp [Ambient, Coordinate]

theorem schemeStructureMap_smoothOfRelativeDimension
    (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    SmoothOfRelativeDimension (rows * baseDimension + columns)
      (schemeStructureMap 𝕜 (baseDimension := baseDimension) matrix) := by
  rw [← ambient_finrank rows baseDimension columns]
  exact (fan matrix).structureMap_smoothOfRelativeDimension 𝕜
    (fan_isComplete matrix) (fan_isRegular matrix)

theorem scheme_isIntegral (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    IsIntegral (scheme 𝕜 (baseDimension := baseDimension) matrix) :=
  (fan matrix).algebraicRealization_isIntegral 𝕜 (fan_isRegular matrix)
    ((fan matrix).completeFan_nonemptyCones (fan_isComplete matrix))

noncomputable def schemeInvariantDivisorLineBundle (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (divisor : (fan (baseDimension := baseDimension) matrix).InvariantRayDivisor) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf (scheme 𝕜 (baseDimension := baseDimension) matrix) :=
  (fan matrix).invariantDivisorLineBundle 𝕜 (fan_isComplete matrix) (fan_isRegular matrix) divisor

end BondalThomsen.ProjectiveBundle
