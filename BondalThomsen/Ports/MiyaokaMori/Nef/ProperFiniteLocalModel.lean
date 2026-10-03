module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LocalizedFiniteExtension
public import BondalThomsen.Ports.MiyaokaMori.Nef.AffineFiniteNeighborhood
public import BondalThomsen.Ports.MiyaokaMori.Nef.AffineFiberTransport
public import BondalThomsen.Ports.MiyaokaMori.Nef.LatticeDeterminantOrder

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Classical AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

@[reducible] def functionFieldAlgebra {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target] (morphism : source ⟶ target)
    (hp : morphism.base (genericPoint source) = genericPoint target) : Algebra target.functionField source.functionField :=
  ((target.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
    morphism.stalkMap (genericPoint source)).hom.toAlgebra

@[reducible] def stalkToFunctionFieldAlgebraOfHom {source target : Scheme.{u}} [IsIntegral source] [IsIntegral target]
    (morphism : source ⟶ target) (hp : morphism.base (genericPoint source) = genericPoint target) (targetPoint : target) :
    Algebra (target.presheaf.stalk targetPoint) source.functionField :=
  ((functionFieldAlgebra morphism hp).algebraMap.comp
    (algebraMap (target.presheaf.stalk targetPoint) target.functionField)).toAlgebra

theorem exists_finite_local_model {source target : Scheme.{u}} [IsIntegral source]
    [IsIntegral target] [IsLocallyNoetherian source] [IsLocallyNoetherian target]
    (morphism : source ⟶ target) [IsProper morphism]
    (hp : morphism.base (genericPoint source) = genericPoint target)
    (hfin : (morphism.residueFieldMap (genericPoint source)).hom.Finite) (targetPoint : target)
    (hz : Order.coheight targetPoint = 1) :
    letI := functionFieldAlgebra morphism hp
    letI := stalkToFunctionFieldAlgebraOfHom morphism hp targetPoint
    ∃ (modelRing : Type u) (_ : CommRing modelRing) (_ : IsDomain modelRing) (_ : Algebra (target.presheaf.stalk targetPoint) modelRing)
      (_ : FaithfulSMul (target.presheaf.stalk targetPoint) modelRing) (_ : Module.Finite (target.presheaf.stalk targetPoint) modelRing)
      (_ : Algebra modelRing source.functionField) (_ : IsFractionRing modelRing source.functionField)
      (_ : IsScalarTower (target.presheaf.stalk targetPoint) modelRing source.functionField)
      (fiberEquivalence : MaximalSpectrum modelRing ≃ {point : source // morphism.base point = targetPoint}),
      ∀ maximalPoint : MaximalSpectrum modelRing,
        Order.coheight (fiberEquivalence maximalPoint).1 = 1 ∧
        maximalPoint.asIdeal.inertiaDeg (target.presheaf.stalk targetPoint) =
          morphism.residueDegree (fiberEquivalence maximalPoint).1 ∧
        ∀ element : modelRing, element ≠ 0 → source.ord (algebraMap modelRing source.functionField element) (fiberEquivalence maximalPoint).1 =
          ((Ring.ord (Localization.AtPrime maximalPoint.asIdeal) (algebraMap modelRing _ element)).toNat : ℤ) := by
  classical
  let algKL : Algebra target.functionField source.functionField := functionFieldAlgebra morphism hp
  let algAL : Algebra (target.presheaf.stalk targetPoint) source.functionField :=
    stalkToFunctionFieldAlgebraOfHom morphism hp targetPoint
  have hdimz : ringKrullDim (target.presheaf.stalk targetPoint) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hz]; rfl
  obtain ⟨region, hU, hzU, hW, hfinapp⟩ := exists_affine_finite_neighbourhood morphism hp hfin targetPoint hdimz
  have hηU : genericPoint target ∈ region := genericPoint_mem_of_nonempty region ⟨targetPoint, hzU⟩
  have hηW : genericPoint source ∈ morphism ⁻¹ᵁ region := by
    show morphism.base _ ∈ region
    rw [hp]; exact hηU
  have : Nonempty region := ⟨⟨targetPoint, hzU⟩⟩
  have : Nonempty (morphism ⁻¹ᵁ region) := ⟨⟨_, hηW⟩⟩
  let algRC : Algebra Γ(target, region) Γ(source, morphism ⁻¹ᵁ region) := (morphism.app region).hom.toAlgebra
  have hinj : Function.Injective (algebraMap Γ(target, region) Γ(source, morphism ⁻¹ᵁ region)) := by
    have := appLE_injective_of_genericPoint morphism hp region (morphism ⁻¹ᵁ region) le_rfl hηW
    rwa [← Scheme.Hom.app_eq_appLE] at this
  have : Module.Finite Γ(target, region) Γ(source, morphism ⁻¹ᵁ region) := hfinapp
  have : IsNoetherianRing Γ(target, region) := IsLocallyNoetherian.component_noetherian ⟨region, hU⟩
  let basePrime : Ideal Γ(target, region) := (hU.primeIdealOf ⟨targetPoint, hzU⟩).asIdeal
  let algRA : Algebra Γ(target, region) (target.presheaf.stalk targetPoint) := target.presheaf.algebra_section_stalk ⟨targetPoint, hzU⟩
  have hlocA : IsLocalization.AtPrime (target.presheaf.stalk targetPoint) basePrime := hU.isLocalization_stalk ⟨targetPoint, hzU⟩
  have h𝔭 : basePrime.height = 1 := by
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height basePrime (target.presheaf.stalk targetPoint)
    rw [hdimz] at h1
    exact_mod_cast h1.symm
  have hfracC : IsFractionRing Γ(source, morphism ⁻¹ᵁ region) source.functionField :=
    functionField_isFractionRing_of_isAffineOpen source _ hW
  let algAB := FiniteLocalModel.algAB Γ(source, morphism ⁻¹ᵁ region) basePrime (target.presheaf.stalk targetPoint)
  let algBL := FiniteLocalModel.algBL Γ(source, morphism ⁻¹ᵁ region) basePrime source.functionField hinj
  have hRL : (algebraMap (target.presheaf.stalk targetPoint) source.functionField).comp
      (algebraMap Γ(target, region) (target.presheaf.stalk targetPoint)) =
      (algebraMap Γ(source, morphism ⁻¹ᵁ region) source.functionField).comp
        (algebraMap Γ(target, region) Γ(source, morphism ⁻¹ᵁ region)) := by
    ext scalar
    show stalkMapOfEq morphism hp (algebraMap (target.presheaf.stalk targetPoint) target.functionField
      (target.presheaf.germ region targetPoint hzU scalar)) = _
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    exact stalkMapOfEq_germ morphism hp region hηU scalar
  let fiberEquivalence : MaximalSpectrum (FiniteLocalModel.LocB Γ(source, morphism ⁻¹ᵁ region) basePrime) ≃ {point : source // morphism.base point = targetPoint} :=
    (FiniteLocalModel.maxEquiv Γ(source, morphism ⁻¹ᵁ region) basePrime (target.presheaf.stalk targetPoint)).trans
      (fiberEquiv morphism hU hW hzU)
  refine ⟨FiniteLocalModel.LocB Γ(source, morphism ⁻¹ᵁ region) basePrime, inferInstance,
    FiniteLocalModel.isDomain_B _ basePrime hinj, algAB,
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (FiniteLocalModel.injective_AB _ basePrime (target.presheaf.stalk targetPoint) hinj),
    FiniteLocalModel.finite_AB _ basePrime _, algBL,
    FiniteLocalModel.isFractionRing_BL _ basePrime _ hinj,
    FiniteLocalModel.tower_ABL _ basePrime _ _ hinj hRL, fiberEquivalence, ?_⟩
  intro maximalPoint
  have := maximalPoint.isMaximal
  let coordinatePrime : PrimeSpectrum Γ(source, morphism ⁻¹ᵁ region) :=
    ⟨maximalPoint.asIdeal.comap (algebraMap Γ(source, morphism ⁻¹ᵁ region) _), inferInstance⟩
  have hxe : (fiberEquivalence maximalPoint).1 = hW.fromSpec coordinatePrime := rfl
  have hxW : hW.fromSpec coordinatePrime ∈ morphism ⁻¹ᵁ region := fromSpec_mem_of_isAffineOpen hW coordinatePrime
  have hxz : morphism.base (hW.fromSpec coordinatePrime) = targetPoint := (fiberEquivalence maximalPoint).2
  rw [hxe]
  let algCS : Algebra Γ(source, morphism ⁻¹ᵁ region) (source.presheaf.stalk (hW.fromSpec coordinatePrime)) :=
    source.presheaf.algebra_section_stalk ⟨hW.fromSpec coordinatePrime, hxW⟩
  have hlocS : IsLocalization.AtPrime (source.presheaf.stalk (hW.fromSpec coordinatePrime))
      (maximalPoint.asIdeal.comap (algebraMap Γ(source, morphism ⁻¹ᵁ region) _)) := hW.isLocalization_stalk' coordinatePrime hxW
  have h𝔮R := FiniteLocalModel.comap_R_of_isMaximal Γ(source, morphism ⁻¹ᵁ region) basePrime (target.presheaf.stalk targetPoint) maximalPoint.asIdeal
  have hco : Order.coheight (hW.fromSpec coordinatePrime) = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight (hW.fromSpec coordinatePrime)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (maximalPoint.asIdeal.comap (algebraMap Γ(source, morphism ⁻¹ᵁ region) _)) (source.presheaf.stalk (hW.fromSpec coordinatePrime)),
      FiniteLocalModel.height_eq_one_of_comap_eq _ basePrime hinj h𝔭 h𝔮R] at h1
    exact_mod_cast h1.symm
  refine ⟨hco, ?_, ?_⟩
  · have hφ : (stalkMapOfEq morphism hxz).comp (algebraMap Γ(target, region) (target.presheaf.stalk targetPoint)) =
        (algebraMap Γ(source, morphism ⁻¹ᵁ region) (source.presheaf.stalk (hW.fromSpec coordinatePrime))).comp
          (algebraMap Γ(target, region) Γ(source, morphism ⁻¹ᵁ region)) := by
      ext scalar
      exact stalkMapOfEq_germ morphism hxz region hzU scalar
    rw [FiniteLocalModel.inertiaDeg_eq _ basePrime _ maximalPoint.asIdeal _ (stalkMapOfEq morphism hxz) hφ]
    exact finrank_residueField_stalkMapOfEq morphism hxz
  · intro element hb
    have : IsScalarTower Γ(source, morphism ⁻¹ᵁ region) (source.presheaf.stalk (hW.fromSpec coordinatePrime)) source.functionField :=
      functionField_isScalarTower source (morphism ⁻¹ᵁ region) ⟨hW.fromSpec coordinatePrime, hxW⟩
    obtain ⟨pointElement, hs1, hs2⟩ := FiniteLocalModel.exists_ord_eq Γ(source, morphism ⁻¹ᵁ region) basePrime (target.presheaf.stalk targetPoint)
      maximalPoint.asIdeal (source.presheaf.stalk (hW.fromSpec coordinatePrime)) source.functionField hinj element
    have : Ring.KrullDimLE 1 (source.presheaf.stalk (hW.fromSpec coordinatePrime)) :=
      krullDimLE_of_coheight_le hco.le
    have := FiniteLocalModel.isFractionRing_BL Γ(source, morphism ⁻¹ᵁ region) basePrime source.functionField hinj
    have := FiniteLocalModel.isDomain_B Γ(source, morphism ⁻¹ᵁ region) basePrime hinj
    have hb' : algebraMap (FiniteLocalModel.LocB Γ(source, morphism ⁻¹ᵁ region) basePrime) source.functionField element ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ source.functionField)).mpr hb
    have hs0 : pointElement ≠ 0 := by
      rintro rfl
      rw [map_zero] at hs1
      exact hb' hs1.symm
    rw [Scheme.ord_eq_iff hco hb']
    change Ring.ordFrac (source.presheaf.stalk (hW.fromSpec coordinatePrime)) _ = _
    rw [← hs1, Submodule.ordFrac_algebraMap hs0, hs2]
    rfl

end AlgebraicGeometry

end
