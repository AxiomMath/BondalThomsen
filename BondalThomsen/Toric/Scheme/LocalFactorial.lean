module

public import BondalThomsen.Toric.Scheme.Dimension
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory Module

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem basisConeCoordinateRing_uniqueFactorization (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    UniqueFactorizationMonoid (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :=
  MulEquiv.uniqueFactorizationMonoid
    (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm.toMulEquiv inferInstance

end TauCeti.Toric.Fan
