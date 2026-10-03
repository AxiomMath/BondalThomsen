module

public import BondalThomsen.Collection.BondalThomsenCommonDenominator
public import BondalThomsen.Collection.BondalThomsenFaithful
public import BondalThomsen.Toric.Frobenius.MultiplicationFiniteLocallyFree
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable def biproductFiberRegroupIso
    {Category : Type*} [CategoryTheory.Category Category] [Preadditive Category]
    [HasFiniteBiproducts Category] {Index Class : Type} [Fintype Index] [Fintype Class]
    (classify : Index → Class) (objects : Class → Category) :
    (⨁ fun member : Class => ⨁ fun _ : {index // classify index = member} => objects member) ≅
      (⨁ fun index => objects (classify index)) := by
  classical
  let indexing := Equiv.sigmaFiberEquiv classify
  refine biproductBiproductIso (fun member => {index // classify index = member})
    (fun member _ => objects member) ≪≫ ?_
  refine biproduct.mapIso (fun pair => eqToIso ?_) ≪≫
    biproduct.reindex indexing (fun index => objects (classify index))
  exact congrArg objects pair.2.property.symm

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient}

local instance (source : Scheme) : HasFiniteBiproducts source.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

noncomputable def floorDivisorClassInvertibleSheafIso
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (pairing : Lattice →+ ℚ) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular (fan.floorRayDivisor pairing)).obj ≅
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular
        (fan.bondalThomsenClassOfPairing pairing).val).obj := by
  apply Classical.choice
  apply TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mp
  rw [fan.invariantClassInvertibleSheaf_class 𝕜]
  change TauCeti.AlgebraicGeometry.LineBundleClass.mk _ =
    Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular
      (fan.invariantRayDivisorClass (fan.floorRayDivisor pairing)))
  rw [fan.invariantDivisorPicardRealization_apply 𝕜]
  rfl

noncomputable def residueLineBundleBiproductRegroupIso
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ) :
    (⨁ fun residue : Fin (Module.finrank ℤ Lattice) → Fin degree =>
      (fan.invariantDivisorLineBundle 𝕜 complete regular
        (fan.floorRayDivisor ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp
          (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue)))).obj) ≅
      (⨁ fun member : fan.BondalThomsenClass =>
        ⨁ fun _ : {residue : Fin (Module.finrank ℤ Lattice) → Fin degree //
          fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree residue = member} =>
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj) := by
  classical
  exact biproduct.mapIso (fun residue => fan.floorDivisorClassInvertibleSheafIso 𝕜
    complete regular ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp
      (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue))) ≪≫
    (BondalThomsen.biproductFiberRegroupIso
      (fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree)
      (fun member => (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj)).symm

def ToricMultiplicationResidueDecomposition
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  ∀ degree : ℕ, 0 < degree →
    Nonempty ((fan.toricMultiplicationPushforward 𝕜 regular degree) ≅
      (⨁ fun residue : Fin (Module.finrank ℤ Lattice) → Fin degree =>
        (fan.invariantDivisorLineBundle 𝕜 complete regular
          (fan.floorRayDivisor ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp
            (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue)))).obj))

noncomputable def residueLineBundleBiproductFinRegroupIso
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ) :
    (⨁ fun residue : Fin (Module.finrank ℤ Lattice) → Fin degree =>
      (fan.invariantDivisorLineBundle 𝕜 complete regular
        (fan.floorRayDivisor ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp
          (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue)))).obj) ≅
      (⨁ fun member : fan.BondalThomsenClass =>
        ⨁ fun _ : Fin (Fintype.card
          {residue : Fin (Module.finrank ℤ Lattice) → Fin degree //
            fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree residue = member}) =>
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj) := by
  classical
  refine fan.residueLineBundleBiproductRegroupIso 𝕜 complete regular degree ≪≫
    biproduct.mapIso (fun member => ?_)
  exact biproduct.reindex (Fintype.equivFin _)
    (fun _ => (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj)

theorem toricMultiplicationPushforward_positive_collection_multiplicities
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (thomsen : fan.ToricMultiplicationResidueDecomposition 𝕜 complete regular) :
    ∃ degree : ℕ, 0 < degree ∧ ∃ multiplicity : fan.BondalThomsenClass → ℕ,
      (∀ member, 0 < multiplicity member) ∧
      (∑ member, multiplicity member) = degree ^ Module.finrank ℤ Lattice ∧
      Nonempty ((fan.toricMultiplicationPushforward 𝕜 regular degree) ≅
        (⨁ fun member : fan.BondalThomsenClass =>
          ⨁ fun _ : Fin (multiplicity member) =>
            (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj)) := by
  classical
  obtain ⟨degree, positive, multiplicities_positive⟩ :=
    fan.residueBondalThomsenClass_positive_multiplicities
  refine ⟨degree, positive, fun member =>
    Fintype.card {residue : Fin (Module.finrank ℤ Lattice) → Fin degree //
      fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree residue = member},
    multiplicities_positive, fan.residueBondalThomsenClass_sum_multiplicities degree, ?_⟩
  exact ⟨(thomsen degree positive).some ≪≫
    fan.residueLineBundleBiproductFinRegroupIso 𝕜 complete regular degree⟩

end TauCeti.Toric.Fan
