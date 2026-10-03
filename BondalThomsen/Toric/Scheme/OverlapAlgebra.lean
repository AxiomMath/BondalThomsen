module

public import BondalThomsen.Fan.CompleteFanCharacters
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.FaceLocalization
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative
open scoped TensorProduct

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def overlapTensorMap (fan : Fan embedding) (first second : fan.cones) :
    affineCoordinateRing 𝕜 fan.lattice first.val ⊗[𝕜] (affineCoordinateRing 𝕜) fan.lattice second.val →ₐ[𝕜]
      (affineCoordinateRing 𝕜) fan.lattice (first.val ⊓ second.val) :=
  Algebra.TensorProduct.productMap
    (faceAffineCoordinateRingMap 𝕜 fan.lattice (fan.inf_isFaceOf_left first.property second.property))
    (faceAffineCoordinateRingMap 𝕜 fan.lattice (fan.inf_isFaceOf_right first.property second.property))

theorem overlap_character_decomposition (fan : Fan embedding) (first second : fan.cones)
    (character : dualSemigroup fan.lattice (first.val ⊓ second.val)) :
    ∃ first_character : dualSemigroup fan.lattice first.val,
      ∃ second_character : dualSemigroup fan.lattice second.val,
        (first_character : Lattice →+ ℤ) + second_character = character := by
  have member : (character : Lattice →+ ℤ) ∈
      dualSemigroup fan.lattice first.val ⊔ dualSemigroup fan.lattice second.val := by
    rw [← fan.dualSemigroup_inf_eq_sup first.property second.property]
    exact character.property
  rw [AddSubmonoid.mem_sup] at member
  obtain ⟨first_character, first_member, second_character, second_member, same⟩ := member
  exact ⟨⟨first_character, first_member⟩, ⟨second_character, second_member⟩, same⟩

theorem overlap_monomial_mem_tensor_range (fan : Fan embedding) (first second : fan.cones)
    (character : dualSemigroup fan.lattice (first.val ⊓ second.val)) :
    MonoidAlgebra.single (ofAdd character) (1 : 𝕜) ∈ (fan.overlapTensorMap 𝕜 first second).range := by
  obtain ⟨first_character, second_character, same⟩ :=
    fan.overlap_character_decomposition first second character
  refine ⟨MonoidAlgebra.single (ofAdd first_character) 1 ⊗ₜ[𝕜]
    MonoidAlgebra.single (ofAdd second_character) 1, ?_⟩
  change (fan.overlapTensorMap 𝕜 first second)
    (MonoidAlgebra.single (ofAdd first_character) 1 ⊗ₜ[𝕜]
      MonoidAlgebra.single (ofAdd second_character) 1) = _
  rw [overlapTensorMap, Algebra.TensorProduct.productMap_apply_tmul,
    faceAffineCoordinateRingMap_single, faceAffineCoordinateRingMap_single,
    MonoidAlgebra.single_mul_single]
  congr 1
  · apply congrArg ofAdd
    exact Subtype.ext same
  · simp

theorem overlapTensorMap_surjective (fan : Fan embedding) (first second : fan.cones) :
    Function.Surjective (fan.overlapTensorMap 𝕜 first second) := by
  apply (AlgHom.range_eq_top _).mp
  apply top_unique
  intro polynomial
  change True → polynomial ∈ (fan.overlapTensorMap 𝕜 first second).range
  rw [true_implies]
  induction polynomial using MonoidAlgebra.induction_on with
  | of character =>
    change MonoidAlgebra.single character 1 ∈ _
    exact fan.overlap_monomial_mem_tensor_range 𝕜 first second (toAdd character)
  | add first_polynomial second_polynomial first_member second_member =>
    exact (fan.overlapTensorMap 𝕜 first second).range.add_mem first_member second_member
  | smul coefficient polynomial member =>
    exact (fan.overlapTensorMap 𝕜 first second).range.smul_mem member coefficient

end TauCeti.Toric.Fan
