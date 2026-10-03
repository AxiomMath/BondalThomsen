module

public import BondalThomsen.Toric.Frobenius.FrobeniusFinite
public import BondalThomsen.Toric.Frobenius.MultiplicationPolynomialBasis
public import BondalThomsen.Fan.Completeness
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def basisConeMultiplicationAlgebraEquiv (fan : Fan embedding) (degree : ℕ)
    {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice) :
    letI : Algebra (MvPolynomial (Fin dimension) 𝕜)
        (affineCoordinateRing 𝕜 fan.lattice
          (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :=
      ((fan.toricMultiplicationRing 𝕜 degree _).toRingHom.comp
        (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm.toRingHom).toAlgebra
    letI : Algebra (MvPolynomial (Fin dimension) 𝕜) (MvPolynomial (Fin dimension) 𝕜) :=
      (MvPolynomial.expand degree).toRingHom.toAlgebra
    (affineCoordinateRing 𝕜) fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ≃ₐ[
        MvPolynomial (Fin dimension) 𝕜] MvPolynomial (Fin dimension) 𝕜 := by
  letI : Algebra (MvPolynomial (Fin dimension) 𝕜)
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :=
    ((fan.toricMultiplicationRing 𝕜 degree _).toRingHom.comp
      (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm.toRingHom).toAlgebra
  letI : Algebra (MvPolynomial (Fin dimension) 𝕜) (MvPolynomial (Fin dimension) 𝕜) :=
    (MvPolynomial.expand degree).toRingHom.toAlgebra
  apply AlgEquiv.ofRingEquiv (f := (fan.basisConeCoordinateRingEquiv 𝕜 basis).toRingEquiv)
  intro polynomial
  change fan.basisConeCoordinateRingEquiv 𝕜 basis
      (fan.toricMultiplicationRing 𝕜 degree _
        ((fan.basisConeCoordinateRingEquiv 𝕜 basis).symm polynomial)) =
    MvPolynomial.expand degree polynomial
  rw [fan.toricMultiplicationRing_basisCone_expand 𝕜, AlgEquiv.apply_symm_apply]

noncomputable def basisConeMultiplicationLinearEquiv (fan : Fan embedding) (degree : ℕ)
    {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice) :
    letI : Algebra (MvPolynomial (Fin dimension) 𝕜)
        (affineCoordinateRing 𝕜 fan.lattice
          (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :=
      ((fan.toricMultiplicationRing 𝕜 degree _).toRingHom.comp
        (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm.toRingHom).toAlgebra
    letI : Algebra (MvPolynomial (Fin dimension) 𝕜) (MvPolynomial (Fin dimension) 𝕜) :=
      (MvPolynomial.expand degree).toRingHom.toAlgebra
    (affineCoordinateRing 𝕜) fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ≃ₗ[
        MvPolynomial (Fin dimension) 𝕜]
      RestrictScalars (MvPolynomial (Fin dimension) 𝕜) (MvPolynomial (Fin dimension) 𝕜)
        (MvPolynomial (Fin dimension) 𝕜) := by
  letI : Algebra (MvPolynomial (Fin dimension) 𝕜)
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :=
    ((fan.toricMultiplicationRing 𝕜 degree _).toRingHom.comp
      (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm.toRingHom).toAlgebra
  letI : Algebra (MvPolynomial (Fin dimension) 𝕜) (MvPolynomial (Fin dimension) 𝕜) :=
    (MvPolynomial.expand degree).toRingHom.toAlgebra
  refine
    { (fan.basisConeCoordinateRingEquiv 𝕜 basis).toAddEquiv.trans
        (RestrictScalars.addEquiv (MvPolynomial (Fin dimension) 𝕜)
          (MvPolynomial (Fin dimension) 𝕜) (MvPolynomial (Fin dimension) 𝕜)).symm with
      map_smul' := ?_ }
  intro scalar polynomial
  change fan.basisConeCoordinateRingEquiv 𝕜 basis
      (fan.toricMultiplicationRing 𝕜 degree _
        ((fan.basisConeCoordinateRingEquiv 𝕜 basis).symm scalar) * polynomial) =
    MvPolynomial.expand degree scalar * fan.basisConeCoordinateRingEquiv 𝕜 basis polynomial
  rw [map_mul, fan.toricMultiplicationRing_basisCone_expand 𝕜, AlgEquiv.apply_symm_apply]

end TauCeti.Toric.Fan
