module

public import BondalThomsen.Toric.Divisor.EffectiveHom
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Collection.SectionThree.Equivalences

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

open scoped Classical

theorem invariantClassInvertibleSheaf_iso_divisor (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    Nonempty ((fan.invariantClassInvertibleSheaf 𝕜 complete regular
      (fan.invariantRayDivisorClass divisor)).obj ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) := by
  rw [← TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff,
    fan.invariantClassInvertibleSheaf_class 𝕜, fan.invariantDivisorPicardRealization_apply 𝕜]
  rfl

set_option maxHeartbeats 800000 in

theorem primitiveFloorPair_nonzeroHom (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (left : Finset fan.Ray) (pairing moved : Lattice →+ ℚ)
    (difference : fan.floorRayDivisor moved - fan.floorRayDivisor pairing =
      fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ left then -1 else 0)) :
    ∃ morphism : (fan.invariantClassInvertibleSheaf 𝕜 complete regular
        (fan.floorRayDivisorClass moved)).obj ⟶
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular
        (fan.floorRayDivisorClass pairing)).obj, morphism ≠ 0 := by
  classical
  let effective_divisor := fan.invariantDivisorOfCoefficients
    (fun ray => if ray ∈ left then 1 else 0)
  have effective : ∀ ray, 0 ≤ effective_divisor ray := by
    intro ray
    simp only [effective_divisor, invariantDivisorOfCoefficients_apply]
    split_ifs <;> omega
  have negative : fan.invariantDivisorOfCoefficients
      (fun ray => if ray ∈ left then -1 else 0) = -effective_divisor := by
    ext ray
    simp only [effective_divisor, invariantDivisorOfCoefficients_apply, Finsupp.neg_apply]
    split_ifs <;> rfl
  have moved_eq : fan.floorRayDivisor moved = fan.floorRayDivisor pairing - effective_divisor := by
    rw [negative] at difference
    exact sub_eq_iff_eq_add.mp difference |>.trans (neg_add_eq_sub _ _)
  let statement : fan.InvariantRayDivisor → Prop := fun source => ∃ morphism :
    (fan.invariantDivisorLineBundle 𝕜 complete regular source).obj ⟶
      (fan.invariantDivisorLineBundle 𝕜 complete regular (fan.floorRayDivisor pairing)).obj,
      morphism ≠ 0
  have effective_hom : statement (fan.floorRayDivisor pairing - effective_divisor) :=
    fan.invariantDivisorEffective_sub_nonzeroHom 𝕜 complete regular
      (fan.floorRayDivisor pairing) effective_divisor effective
  have actual_hom : statement (fan.floorRayDivisor moved) := moved_eq.symm ▸ effective_hom
  obtain ⟨morphism, nonzero⟩ := actual_hom
  obtain ⟨source_iso⟩ := fan.invariantClassInvertibleSheaf_iso_divisor 𝕜 complete regular
    (fan.floorRayDivisor moved)
  obtain ⟨target_iso⟩ := fan.invariantClassInvertibleSheaf_iso_divisor 𝕜 complete regular
    (fan.floorRayDivisor pairing)
  refine ⟨source_iso.hom ≫ morphism ≫ target_iso.inv, ?_⟩
  intro equality
  apply nonzero
  have inner_zero : morphism ≫ target_iso.inv = 0 :=
    zero_of_epi_comp source_iso.hom equality
  exact zero_of_comp_mono target_iso.inv inner_zero

def PrimitiveFloorPairPositiveExt (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  ∀ left : Finset fan.Ray, fan.IsPrimitiveCollection left →
    ∀ pairing moved : Lattice →+ ℚ,
    fan.floorRayDivisor moved - fan.floorRayDivisor pairing =
      fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ left then -1 else 0) →
    ∃ extension : Ext
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular (fan.floorRayDivisorClass pairing)).obj
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular (fan.floorRayDivisorClass moved)).obj
      (left.card - 1), extension ≠ 0

theorem primitiveFloorPairSheafComparison_of_positiveExt (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (positive_obstruction : fan.PrimitiveFloorPairPositiveExt 𝕜 complete regular) :
    BondalThomsen.PrimitiveFloorPairSheafComparison fan (fan.algebraicRealization 𝕜 regular)
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular) := by
  intro left primitive pairing moved difference
  exact ⟨fan.primitiveFloorPair_nonzeroHom 𝕜 complete regular left pairing moved difference,
    positive_obstruction left primitive pairing moved difference⟩

end TauCeti.Toric.Fan
