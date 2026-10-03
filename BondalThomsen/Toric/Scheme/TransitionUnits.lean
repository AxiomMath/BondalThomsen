module

public import BondalThomsen.Toric.Divisor.CartierData
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.FaceLocalization

@[expose] public section

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric

open Multiplicative

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def dualCharacterUnit (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    (Multiplicative (dualSemigroup lattice cone))ˣ where
  val := ofAdd ⟨character, positive⟩
  inv := ofAdd ⟨-character, negative⟩
  val_inv := by
    change (⟨character, positive⟩ : dualSemigroup lattice cone) + ⟨-character, negative⟩ = 0
    apply Subtype.ext
    exact add_neg_cancel character
  inv_val := by
    change (⟨-character, negative⟩ : dualSemigroup lattice cone) + ⟨character, positive⟩ = 0
    apply Subtype.ext
    exact neg_add_cancel character

noncomputable def toricMonomialUnit (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    (affineCoordinateRing 𝕜 lattice cone)ˣ :=
  Units.map (MonoidAlgebra.of 𝕜 _) (dualCharacterUnit lattice cone character positive negative)

@[simp] theorem toricMonomialUnit_val (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    (toricMonomialUnit 𝕜 lattice cone character positive negative : affineCoordinateRing 𝕜 lattice cone) =
      MonoidAlgebra.single (ofAdd (⟨character, positive⟩ : dualSemigroup lattice cone)) 1 := rfl

theorem toricMonomialUnit_face_restriction (lattice : IsIntegralLattice embedding)
    {cone face : PointedCone ℝ Ambient} (face_of : face.IsFaceOf cone)
    (character : Lattice →+ ℤ) (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    Units.map (faceAffineCoordinateRingMap 𝕜 lattice face_of).toMonoidHom
        (toricMonomialUnit 𝕜 lattice cone character positive negative) =
      toricMonomialUnit 𝕜 lattice face character
        (dualSemigroup_anti lattice face_of.le positive)
        (dualSemigroup_anti lattice face_of.le negative) := by
  apply Units.ext
  change faceAffineCoordinateRingMap 𝕜 lattice face_of
      (MonoidAlgebra.single (ofAdd (⟨character, positive⟩ : dualSemigroup lattice cone)) 1) = _
  rw [faceAffineCoordinateRingMap_single]
  rfl

theorem toricMonomialUnit_add (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (first second : Lattice →+ ℤ)
    (first_positive : first ∈ dualSemigroup lattice cone)
    (first_negative : -first ∈ dualSemigroup lattice cone)
    (second_positive : second ∈ dualSemigroup lattice cone)
    (second_negative : -second ∈ dualSemigroup lattice cone) :
    toricMonomialUnit 𝕜 lattice cone first first_positive first_negative *
        toricMonomialUnit 𝕜 lattice cone second second_positive second_negative =
      toricMonomialUnit 𝕜 lattice cone (first + second)
        ((dualSemigroup lattice cone).add_mem first_positive second_positive)
        (by simpa only [neg_add] using
          (dualSemigroup lattice cone).add_mem first_negative second_negative) := by
  apply Units.ext
  simp only [Units.val_mul, toricMonomialUnit_val, MonoidAlgebra.single_mul_single, one_mul]
  rfl

namespace Fan

open Module Set

noncomputable def coneDivisorTransitionUnit (fan : TauCeti.Toric.Fan embedding)
    {firstDimension secondDimension : ℕ}
    (first : Basis (Fin firstDimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin secondDimension) ℤ Lattice) (second_cone : fan.IsConeBasis second)
    (divisor : fan.InvariantRayDivisor) :
    (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
        PointedCone.hull ℝ (Set.range (fun index => embedding (second index)))))ˣ :=
  let memberships := fan.coneDivisorCharacter_transition_dualSemigroup first first_cone
    second second_cone divisor
  (toricMonomialUnit 𝕜) fan.lattice _
    (fan.coneDivisorCharacter first first_cone divisor -
      fan.coneDivisorCharacter second second_cone divisor) memberships.1 memberships.2

end Fan

end TauCeti.Toric
