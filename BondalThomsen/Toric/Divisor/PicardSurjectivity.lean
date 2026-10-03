module

public import BondalThomsen.Toric.Scheme.LocalFactorial
public import BondalThomsen.Toric.Scheme.LaurentUnits
public import BondalThomsen.Toric.Scheme.Integral
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem affineCoordinateRing_uniqueFactorization (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones) :
    UniqueFactorizationMonoid (affineCoordinateRing 𝕜 fan.lattice cone.val) := by
  obtain ⟨dimension, basis, cone_basis, face⟩ :=
    fan.exists_coneBasis_above complete regular cone.val cone.property
  let := fan.basisConeCoordinateRing_uniqueFactorization 𝕜 basis
  obtain ⟨character, localized⟩ :=
    IsRegularCone.exists_isLocalization_away_faceAffineCoordinateRingMap 𝕜 fan.lattice
      (regular cone_basis) face
  let := (faceAffineCoordinateRingMap 𝕜 fan.lattice face).toRingHom.toAlgebra
  let := localized
  exact UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.powers (MonoidAlgebra.single (Multiplicative.ofAdd character) (1 : 𝕜)))
    (affineCoordinateRing 𝕜 fan.lattice cone.val)

theorem denseTorusCoordinateRing_uniqueFactorization (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    UniqueFactorizationMonoid (affineCoordinateRing 𝕜 fan.lattice (⊥ : PointedCone ℝ Ambient)) := by
  obtain ⟨cone, member, _⟩ := fan.isComplete_iff.mp complete (0 : Ambient)
  exact fan.affineCoordinateRing_uniqueFactorization 𝕜 complete regular
    (fan.botCone ⟨⟨cone, member⟩⟩)

end TauCeti.Toric.Fan
