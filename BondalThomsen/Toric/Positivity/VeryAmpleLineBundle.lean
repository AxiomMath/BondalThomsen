module

public import BondalThomsen.Toric.Scheme.ValuationConeSelection
public import BondalThomsen.DeepFan.StarDeep
public import BondalThomsen.Toric.Positivity.StrictSupportProjectivity
public import BondalThomsen.Toric.Projective.DegreeOneDescent
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory Module

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

def VeryAmpleOverField {schemeModel : Scheme}
    (structureMap : schemeModel ⟶ Spec (CommRingCat.of 𝕜))
    (lineBundle : TauCeti.AlgebraicGeometry.InvertibleSheaf schemeModel) : Prop :=
  ∃ Index : Type, Finite Index ∧
    ∃ embedding : schemeModel ⟶ polynomialDegreeOneProj 𝕜 Index,
      IsImmersion embedding ∧ embedding ≫ polynomialProjStructureMap 𝕜 Index = structureMap ∧
      Nonempty ((Scheme.Modules.pullback embedding).obj
        (polynomialProjDegreeOneSheaf 𝕜 Index) ≅ lineBundle.obj)

def HasVeryAmplePowerOverField {schemeModel : Scheme}
    (structureMap : schemeModel ⟶ Spec (CommRingCat.of 𝕜))
    (lineBundle : TauCeti.AlgebraicGeometry.InvertibleSheaf schemeModel) : Prop :=
  ∃ exponent : ℕ, 0 < exponent ∧
    ∃ powerBundle : TauCeti.AlgebraicGeometry.InvertibleSheaf schemeModel,
      TauCeti.AlgebraicGeometry.LineBundleClass.mk powerBundle =
        TauCeti.AlgebraicGeometry.LineBundleClass.mk lineBundle ^ exponent ∧
      VeryAmpleOverField 𝕜 structureMap powerBundle

theorem veryAmpleOverField_of_closedImmersion {schemeModel : Scheme}
    (structureMap : schemeModel ⟶ Spec (CommRingCat.of 𝕜))
    (lineBundle : TauCeti.AlgebraicGeometry.InvertibleSheaf schemeModel)
    (Index : Type) [Finite Index] (embedding : schemeModel ⟶ polynomialDegreeOneProj 𝕜 Index)
    (closed : IsClosedImmersion embedding)
    (overBase : embedding ≫ polynomialProjStructureMap 𝕜 Index = structureMap)
    (pullbackIso : Nonempty ((Scheme.Modules.pullback embedding).obj
      (polynomialProjDegreeOneSheaf 𝕜 Index) ≅ lineBundle.obj)) :
    VeryAmpleOverField 𝕜 structureMap lineBundle := by
  let := closed
  exact ⟨Index, inferInstance, embedding, inferInstance, overBase, pullbackIso⟩

theorem VeryAmpleOverField.of_iso {schemeModel : Scheme}
    {structureMap : schemeModel ⟶ Spec (CommRingCat.of 𝕜)}
    {first second : TauCeti.AlgebraicGeometry.InvertibleSheaf schemeModel}
    (veryAmple : VeryAmpleOverField 𝕜 structureMap first) (comparison : first.obj ≅ second.obj) :
    VeryAmpleOverField 𝕜 structureMap second := by
  obtain ⟨Index, finite, embedding, immersion, overBase, ⟨pullbackIso⟩⟩ := veryAmple
  exact ⟨Index, finite, embedding, immersion, overBase, ⟨pullbackIso ≪≫ comparison⟩⟩

end

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem invariantDivisorLineBundleClass_nsmul
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (multiple : ℕ) :
    TauCeti.AlgebraicGeometry.LineBundleClass.mk
        (fan.invariantDivisorLineBundle 𝕜 complete regular (multiple • divisor)) =
      TauCeti.AlgebraicGeometry.LineBundleClass.mk
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) ^ multiple := by
  have multiple_class := congrArg Additive.toMul
    (show fan.invariantDivisorPicardRealization 𝕜 complete regular
        (fan.invariantRayDivisorClass (multiple • divisor)) =
      multiple • fan.invariantDivisorPicardRealization 𝕜 complete regular
        (fan.invariantRayDivisorClass divisor) by rw [map_nsmul, map_nsmul])
  simpa only [fan.invariantDivisorPicardRealization_apply 𝕜 complete regular,
    toMul_nsmul, toMul_ofMul] using multiple_class

end TauCeti.Toric.Fan
