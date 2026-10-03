module

public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Toric.Scheme.BasisChart
public import BondalThomsen.Toric.Divisor.SupportClasses
public import BondalThomsen.Fan.ConeRayQuotient
public import BondalThomsen.DeepFan.CriterionForward
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Module Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def basisConeFixedPointEvaluation (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) →+* 𝕜 :=
  MvPolynomial.constantCoeff.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).toRingHom

theorem basisConeFixedPointEvaluation_eq_coeff (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice)
    (polynomial : affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    fan.basisConeFixedPointEvaluation 𝕜 basis polynomial = polynomial.coeff 1 := by
  change MvPolynomial.constantCoeff (fan.basisConeCoordinateRingEquiv 𝕜 basis polynomial) = _
  induction polynomial using MonoidAlgebra.induction_on with
  | of exponent =>
      change MvPolynomial.constantCoeff (fan.basisConeCoordinateRingEquiv 𝕜 basis
        (MonoidAlgebra.single exponent 1)) = (MonoidAlgebra.single exponent (1 : 𝕜)).coeff 1
      have polynomial_single :
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ)).symm
            (MonoidAlgebra.single (ofAdd ((fan.basisConeDualSemigroupEquiv basis)
              (toAdd exponent))) 1) =
            MvPolynomial.monomial ((fan.basisConeDualSemigroupEquiv basis)
              (toAdd exponent)) (1 : 𝕜) := by
        apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜
          (Fin dimension →₀ ℕ)).injective
        rw [AlgEquiv.apply_symm_apply]
        exact (AddMonoidAlgebra.toMultiplicativeAlgEquiv_single _ _).symm
      have zero_iff : (fan.basisConeDualSemigroupEquiv basis) (toAdd exponent) = 0 ↔
          exponent = 1 := by
        rw [(fan.basisConeDualSemigroupEquiv basis).map_eq_zero_iff]
        rfl
      rw [basisConeCoordinateRingEquiv, AlgEquiv.trans_apply, MonoidAlgebra.domCongr_single]
      change MvPolynomial.constantCoeff
        ((AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ)).symm
          (MonoidAlgebra.single (ofAdd ((fan.basisConeDualSemigroupEquiv basis)
            (toAdd exponent))) 1)) = (Finsupp.single exponent (1 : 𝕜)) 1
      rw [polynomial_single, MvPolynomial.constantCoeff_monomial]
      classical
      by_cases equal : exponent = 1
      · rw [ite_eq_left (zero_iff.mpr equal), equal, Finsupp.single_eq_same]
      · rw [ite_eq_right (mt zero_iff.mp equal), Finsupp.single_eq_of_ne (Ne.symm equal)]
  | add first second first_same second_same =>
      simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply,
        first_same, second_same]
  | smul scalar polynomial same =>
      simp only [map_smul, MvPolynomial.constantCoeff_smul,
        MonoidAlgebra.coeff_smul, Finsupp.smul_apply, same]

theorem coneCharacterSectionMap_coeff_character (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (polynomial : affineCoordinateRing 𝕜 fan.lattice cone) :
    (fan.coneCharacterSectionMap 𝕜 cone character polynomial).coeff (ofAdd character) =
      polynomial.coeff 1 := by
  classical
  change (MonoidAlgebra.mapDomain
    (fun exponent : Multiplicative (dualSemigroup fan.lattice cone) =>
      ofAdd (character + (toAdd exponent).val)) polynomial).coeff (ofAdd character) = _
  rw [MonoidAlgebra.coeff_mapDomain]
  have injective : Function.Injective
      (fun exponent : Multiplicative (dualSemigroup fan.lattice cone) =>
        ofAdd (character + (toAdd exponent).val)) := by
    intro first second same
    apply Subtype.ext
    exact add_left_cancel (congrArg toAdd same)
  simpa using Finsupp.mapDomain_apply_of_injective injective polynomial.coeff 1

variable [FiniteDimensional ℝ Ambient]

omit [FiniteDimensional ℝ Ambient] in
theorem globalDivisorChartCoefficient_fixedPoint (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (divisor : fan.InvariantRayDivisor)
    (global_section : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    fan.basisConeFixedPointEvaluation 𝕜 basis
        (fan.globalDivisorChartCoefficient 𝕜 basis cone_basis divisor global_section) =
      global_section.val.coeff (ofAdd (fan.coneDivisorCharacter basis cone_basis divisor)) := by
  rw [fan.basisConeFixedPointEvaluation_eq_coeff 𝕜,
    ← fan.coneCharacterSectionMap_coeff_character 𝕜 _
      (fan.coneDivisorCharacter basis cone_basis divisor),
    fan.globalDivisorChartCoefficient_reconstruct 𝕜]

omit [FiniteDimensional ℝ Ambient] in
theorem coneDivisorCharacter_admissible_of_fixedPoint_ne_zero (fan : Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (global_section : fan.globalDivisorLaurentSectionSpace 𝕜 divisor)
    (nonzero : fan.basisConeFixedPointEvaluation 𝕜 basis
      (fan.globalDivisorChartCoefficient 𝕜 basis cone_basis divisor global_section) ≠ 0) :
    fan.characterLaurentMonomial 𝕜 (fan.coneDivisorCharacter basis cone_basis divisor) ∈
      fan.globalDivisorLaurentSectionSpace 𝕜 divisor := by
  rw [fan.globalDivisorChartCoefficient_fixedPoint 𝕜] at nonzero
  apply (fan.characterLaurentMonomial_mem_global_iff 𝕜 divisor _).mpr
  exact (fan.mem_globalDivisorLaurentSectionSpace_iff 𝕜 divisor global_section.val).mp
    global_section.property _ (Finsupp.mem_support_iff.mpr nonzero)

def InvariantDivisorGloballyGenerated (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) : Prop :=
  Nonempty (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.GeneratingSections

theorem affine_generatingSections_span {coordinate_ring : CommRingCat}
    (sheaf : (Spec coordinate_ring).Modules) [sheaf.IsQuasicoherent]
    (generators : sheaf.GeneratingSections) :
    Submodule.span coordinate_ring
      (Set.range (fun index => (show moduleSpecΓFunctor.obj sheaf from
        (generators.s index).val (op ⊤)))) =
      (⊤ : Submodule coordinate_ring (moduleSpecΓFunctor.obj sheaf)) := by
  classical
  let : Epi generators.π := generators.epi
  let section_module := moduleSpecΓFunctor.obj sheaf
  let : Module coordinate_ring section_module := section_module.isModule
  let generated : Submodule coordinate_ring section_module := Submodule.span coordinate_ring
    (Set.range (fun index => (show section_module from (generators.s index).val (op ⊤))))
  let quotient_map : section_module ⟶ ModuleCat.of coordinate_ring (section_module ⧸ generated) :=
    ConcreteCategory.ofHom (C := ModuleCat coordinate_ring) generated.mkQ
  let quotient_sheaf_map : sheaf ⟶ tilde (ModuleCat.of coordinate_ring
      (section_module ⧸ generated)) :=
    inv sheaf.fromTildeΓ ≫ (tilde.functor coordinate_ring).map quotient_map
  have inverse_top : moduleSpecΓFunctor.map (inv sheaf.fromTildeΓ) =
      (tilde.adjunction (R := coordinate_ring)).unit.app section_module := by
    apply (cancel_mono (moduleSpecΓFunctor.map sheaf.fromTildeΓ)).mp
    rw [← Functor.map_comp, IsIso.inv_hom_id, moduleSpecΓFunctor.map_id]
    exact ((tilde.adjunction (R := coordinate_ring)).right_triangle_components sheaf).symm
  have killed_top : ∀ index,
      ((SheafOfModules.sectionsMap quotient_sheaf_map (generators.s index)).val (op ⊤)) = 0 := by
    intro index
    change (moduleSpecΓFunctor.map quotient_sheaf_map) ((generators.s index).val (op ⊤)) = 0
    rw [show moduleSpecΓFunctor.map quotient_sheaf_map =
      moduleSpecΓFunctor.map (inv sheaf.fromTildeΓ) ≫
        moduleSpecΓFunctor.map ((tilde.functor coordinate_ring).map quotient_map) from
      Functor.map_comp _ _ _, inverse_top]
    change ((tilde.adjunction (R := coordinate_ring)).unit.app section_module ≫
      ((tilde.functor coordinate_ring) ⋙ moduleSpecΓFunctor).map quotient_map) _ = 0
    rw [← (tilde.adjunction (R := coordinate_ring)).unit.naturality quotient_map]
    have killed : quotient_map ((generators.s index).val (op ⊤)) = 0 := by
      change generated.mkQ ((generators.s index).val (op ⊤)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span (Set.mem_range_self index)
    change ((tilde.adjunction (R := coordinate_ring)).unit.app _) (quotient_map _) = 0
    rw [killed]
    exact ((tilde.adjunction (R := coordinate_ring)).unit.app _).hom.map_zero
  have killed_sections : ∀ index,
      SheafOfModules.sectionsMap quotient_sheaf_map (generators.s index) =
        (tilde (ModuleCat.of coordinate_ring (section_module ⧸ generated))).unitHomEquiv
          (0 : SheafOfModules.unit _ ⟶ _) := by
    intro index
    apply PresheafOfModules.sections_ext
    intro open_set
    rw [← PresheafOfModules.sections_property _ (homOfLE
      (show open_set.unop ≤ ⊤ from le_top)).op, killed_top]
    change ((tilde (ModuleCat.of coordinate_ring (section_module ⧸ generated))).val.map
      (homOfLE (show open_set.unop ≤ ⊤ from le_top)).op) 0 = 0
    exact ((tilde (ModuleCat.of coordinate_ring (section_module ⧸ generated))).val.map
      (homOfLE (show open_set.unop ≤ ⊤ from le_top)).op).hom.map_zero
  have killed_evaluation : generators.π ≫ quotient_sheaf_map = 0 := by
    apply (SheafOfModules.freeHomEquiv _).injective
    funext index
    rw [SheafOfModules.freeHomEquiv_comp_apply]
    simp only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply,
      killed_sections]
    simp [SheafOfModules.freeHomEquiv]
  have zero_map : quotient_sheaf_map = 0 := by
    apply (cancel_epi generators.π).mp
    simpa using killed_evaluation
  have zero_tilde : (tilde.functor coordinate_ring).map quotient_map = 0 := by
    have equality := congrArg (fun morphism => sheaf.fromTildeΓ ≫ morphism) zero_map
    simpa [quotient_sheaf_map] using equality
  have zero_quotient : quotient_map = 0 := by
    apply (tilde.functor coordinate_ring).map_injective
    simpa using zero_tilde
  apply top_unique
  intro section_value _
  have killed := congrArg (fun morphism : section_module ⟶
      ModuleCat.of coordinate_ring (section_module ⧸ generated) => morphism section_value)
    zero_quotient
  exact (Submodule.Quotient.mk_eq_zero generated).mp killed

noncomputable def invariantDivisorSheafChartCoefficientAddEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    affineCoordinateRing 𝕜 fan.lattice (fan.divisorLocalCone 𝕜 complete regular index).val ≃+
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange) :=
  (LinearEquiv.ofInjective (fan.coneCharacterSectionMap 𝕜
    (fan.divisorLocalCone 𝕜 complete regular index).val
    (fan.divisorLocalCharacter 𝕜 complete regular divisor index))
    (fan.coneCharacterSectionMap_injective 𝕜 _ _)).toAddEquiv.trans
      (fan.invariantDivisorSheafChartSectionsEquiv 𝕜 complete regular divisor index)

theorem invariantDivisorSheafChartCoefficient_rationalValue (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones))
    (coefficient : affineCoordinateRing 𝕜 fan.lattice (fan.divisorLocalCone 𝕜 complete regular index).val) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let chart := (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
    letI := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι chart
        (fan.invariantDivisorSheafChartCoefficientAddEquiv 𝕜 complete regular divisor index coefficient)) =
      fan.chartCoordinateGerm 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (fan.divisorLocalCone 𝕜 complete regular index) coefficient *
        (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (fan.divisorLocalCharacter 𝕜 complete regular divisor index) :
            (fan.algebraicRealization 𝕜 regular).functionField) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _
    (fan.laurentRationalSection 𝕜 regular _ _ (fan.coneCharacterSectionMap 𝕜 _ _ coefficient)) = _
  rw [fan.rationalFunctionsEquiv_laurentRationalSection 𝕜,
    fan.laurentRationalMap_coneCharacterSectionMap 𝕜]

theorem invariantDivisorSheafChartCoefficient_smul (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones))
    (scalar coefficient : affineCoordinateRing 𝕜 fan.lattice
      (fan.divisorLocalCone 𝕜 complete regular index).val) :
    fan.invariantDivisorSheafChartCoefficientAddEquiv 𝕜 complete regular divisor index
        (scalar * coefficient) =
      fan.chartCoordinateSectionsEquiv 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index) scalar •
        fan.invariantDivisorSheafChartCoefficientAddEquiv 𝕜 complete regular divisor index coefficient := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := fan.divisorLocalCone 𝕜 complete regular index
  let chart := (fan.affineToricChartι 𝕜 regular cone).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular cone
  apply (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_injective chart
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart).injective
  rw [Scheme.Modules.Hom.app_smul,
    (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart).map_smul]
  rw [fan.invariantDivisorSheafChartCoefficient_rationalValue 𝕜,
    fan.invariantDivisorSheafChartCoefficient_rationalValue 𝕜, map_mul]
  change _ = fan.chartCoordinateGerm 𝕜 regular (fan.completeFan_nonemptyCones complete) cone scalar * _
  exact mul_assoc _ _ _

theorem invariantDivisorSheafChartCoefficient_global (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones))
    (global_section : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    fan.invariantDivisorSheafChartCoefficientAddEquiv 𝕜 complete regular divisor index
      (fan.globalDivisorChartCoefficient 𝕜
        (fan.divisorSectionChartBasis complete regular index).val.2
        (fan.divisorSectionChartBasis complete regular index).property.1 divisor global_section) =
      fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange
        (fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor global_section) := by
  rw [fan.globalDivisorLaurentToSheafSections_on_chart 𝕜]
  change fan.invariantDivisorSheafChartSectionsEquiv 𝕜 complete regular divisor index _ =
    fan.invariantDivisorSheafChartSectionsEquiv 𝕜 complete regular divisor index _
  congr 1
  change (⟨fan.coneCharacterSectionMap 𝕜 _ _
    (fan.globalDivisorChartCoefficient 𝕜 _ _ divisor global_section), _⟩ :
      fan.divisorChartLaurentSectionSpace 𝕜 complete regular divisor index) = _
  apply Subtype.ext
  exact fan.globalDivisorChartCoefficient_reconstruct 𝕜 _ _ divisor global_section

noncomputable def invariantDivisorRestrictedChartSectionsIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.restrict
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)), ⊤) ≅
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange) :=
  (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.restrictAppIso _ ⊤ ≪≫
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.mapIso
      (eqToIso (fan.affineToricChartι 𝕜 regular
        (fan.divisorLocalCone 𝕜 complete regular index)).image_top_eq_opensRange.symm).op

noncomputable def invariantDivisorRestrictedChartCoefficientEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones)) :
    affineCoordinateRing 𝕜 fan.lattice (fan.divisorLocalCone 𝕜 complete regular index).val ≃+
      moduleSpecΓFunctor.obj ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.restrict
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index))) :=
  (fan.invariantDivisorSheafChartCoefficientAddEquiv 𝕜 complete regular divisor index).trans
    (Iso.addCommGroupIsoToAddEquiv
      (fan.invariantDivisorRestrictedChartSectionsIso 𝕜 complete regular divisor index)).symm

theorem invariantDivisorRestrictedChartCoefficient_smul (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (index : Fin (Nat.card fan.cones))
    (scalar coefficient : affineCoordinateRing 𝕜 fan.lattice
      (fan.divisorLocalCone 𝕜 complete regular index).val) :
    fan.invariantDivisorRestrictedChartCoefficientEquiv 𝕜 complete regular divisor index
        (scalar * coefficient) =
      scalar • fan.invariantDivisorRestrictedChartCoefficientEquiv 𝕜 complete regular divisor index
        coefficient := by
  let cone := fan.divisorLocalCone 𝕜 complete regular index
  let inclusion := fan.affineToricChartι 𝕜 regular cone
  let sheaf := (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
  apply (Iso.addCommGroupIsoToAddEquiv
    (fan.invariantDivisorRestrictedChartSectionsIso 𝕜 complete regular divisor index)).injective
  change fan.invariantDivisorSheafChartCoefficientAddEquiv 𝕜 complete regular divisor index
    (scalar * coefficient) = _
  rw [fan.invariantDivisorSheafChartCoefficient_smul 𝕜]
  simp only [invariantDivisorRestrictedChartSectionsIso, Iso.trans_hom,
    Iso.addCommGroupIsoToAddEquiv_apply, ConcreteCategory.comp_apply]
  change _ = sheaf.presheaf.map (eqToHom inclusion.image_top_eq_opensRange.symm).op
    ((inclusion.appIso ⊤).inv ((Scheme.ΓSpecIso _).inv scalar) •
      (show Γ(sheaf, inclusion ''ᵁ ⊤) from
        fan.invariantDivisorRestrictedChartCoefficientEquiv 𝕜 complete regular divisor index coefficient))
  erw [sheaf.map_smul]
  congr 1

theorem generatingSections_restrict_top {source target : Scheme} (inclusion : source ⟶ target)
    [IsOpenImmersion inclusion]
    [Limits.PreservesColimitsOfSize.{0, 0} (Scheme.Modules.restrictFunctor inclusion)]
    (sheaf : target.Modules) (generators : sheaf.GeneratingSections)
    (index : generators.I) :
    ((generators.map (Scheme.Modules.restrictFunctor inclusion)
      (Scheme.Modules.restrictUnitIso inclusion).symm).s index).val (op ⊤) =
      (generators.s index).val (op (inclusion ''ᵁ ⊤)) := by
  let restriction := Scheme.Modules.restrictFunctor inclusion
  let unit_iso := (Scheme.Modules.restrictUnitIso inclusion).symm
  change (((restriction.obj sheaf).freeHomEquiv
    ((SheafOfModules.mapFreeIso restriction generators.I unit_iso).hom ≫
      restriction.map generators.π)) index).val (op ⊤) = _
  rw [SheafOfModules.freeHomEquiv]
  change Scheme.Modules.Hom.app
    (SheafOfModules.ιFree index ≫
      (SheafOfModules.mapFreeIso restriction generators.I unit_iso).hom ≫
        restriction.map generators.π) ⊤ (1 : Γ(source, ⊤)) = _
  rw [SheafOfModules.ιFree_mapFreeIso_hom_assoc, ← Functor.map_comp]
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply]
  change Scheme.Modules.Hom.app
    (unit_iso.hom ≫ restriction.map (sheaf.unitHomEquiv.symm (generators.s index))) ⊤
      (1 : Γ(source, ⊤)) = _
  change (sheaf.unitHomEquiv.symm (generators.s index)).val.app _
    ((inclusion.appIso ⊤).inv 1) = _
  rw [map_one]
  exact congrArg (fun section_value => section_value.val (op (inclusion ''ᵁ ⊤)))
    (sheaf.unitHomEquiv.apply_symm_apply (generators.s index))

theorem invariantDivisorLocalCharacter_admissible_of_generatingSections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (generators : (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.GeneratingSections)
    (index : Fin (Nat.card fan.cones)) :
    fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor index) ∈
      fan.globalDivisorLaurentSectionSpace 𝕜 divisor := by
  classical
  let cone := fan.divisorLocalCone 𝕜 complete regular index
  let inclusion := fan.affineToricChartι 𝕜 regular cone
  let sheaf := (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
  let restriction := Scheme.Modules.restrictFunctor inclusion
  let : Limits.PreservesColimitsOfSize.{0, 0} restriction :=
    (Scheme.Modules.restrictAdjunction inclusion).leftAdjoint_preservesColimits
  let restricted_generators := generators.map restriction
    (Scheme.Modules.restrictUnitIso inclusion).symm
  let restricted_sheaf := restriction.obj sheaf
  let : restricted_sheaf.IsQuasicoherent := inferInstance
  let coefficient_equiv := fan.invariantDivisorRestrictedChartCoefficientEquiv 𝕜
    complete regular divisor index
  let basis_data := fan.divisorSectionChartBasis complete regular index
  let evaluation := fan.basisConeFixedPointEvaluation 𝕜 basis_data.val.2
  have all_span := affine_generatingSections_span restricted_sheaf restricted_generators
  by_contra inadmissible
  have vanishes : ∀ generator_index,
      evaluation (coefficient_equiv.symm
        ((restricted_generators.s generator_index).val (op ⊤))) = 0 := by
    intro generator_index
    let global_value := (generators.s generator_index).val (op ⊤)
    let laurent := (fan.invariantDivisorSheafGlobalSectionsEquiv 𝕜 complete regular divisor).symm
      global_value
    have global_same : fan.globalDivisorLaurentToSheafSections 𝕜 complete regular divisor laurent =
        global_value :=
      (fan.invariantDivisorSheafGlobalSectionsEquiv 𝕜 complete regular divisor).apply_symm_apply _
    have coefficient_same : coefficient_equiv
        (fan.globalDivisorChartCoefficient 𝕜 basis_data.val.2 basis_data.property.1 divisor laurent) =
          (restricted_generators.s generator_index).val (op ⊤) := by
      apply (Iso.addCommGroupIsoToAddEquiv
        (fan.invariantDivisorRestrictedChartSectionsIso 𝕜
          complete regular divisor index)).injective
      change fan.invariantDivisorSheafChartCoefficientAddEquiv 𝕜 complete regular divisor index
        (fan.globalDivisorChartCoefficient 𝕜 basis_data.val.2 basis_data.property.1 divisor laurent) = _
      rw [fan.invariantDivisorSheafChartCoefficient_global 𝕜, global_same]
      rw [generatingSections_restrict_top]
      change sheaf.val.map _ ((generators.s generator_index).val (op ⊤)) = _
      rw [PresheafOfModules.sections_property]
      change _ = sheaf.val.map (eqToHom inclusion.image_top_eq_opensRange.symm).op
        ((generators.s generator_index).val (op (inclusion ''ᵁ ⊤)))
      rw [PresheafOfModules.sections_property]
    rw [← coefficient_same, AddEquiv.symm_apply_apply]
    by_contra nonzero
    exact inadmissible (fan.coneDivisorCharacter_admissible_of_fixedPoint_ne_zero 𝕜
      basis_data.val.2 basis_data.property.1 divisor laurent nonzero)
  have span_vanishes : ∀ section_value ∈ Submodule.span
      (affineCoordinateRing 𝕜 fan.lattice cone.val)
      (Set.range (fun generator_index => (show moduleSpecΓFunctor.obj restricted_sheaf from
        (restricted_generators.s generator_index).val (op ⊤)))),
      evaluation (coefficient_equiv.symm section_value) = 0 := by
    intro section_value member
    induction member using Submodule.span_induction with
    | mem section_value member =>
        obtain ⟨generator_index, rfl⟩ := member
        exact vanishes generator_index
    | zero => simp
    | add first second _ _ first_zero second_zero =>
        simp only [map_add, first_zero, second_zero, add_zero]
    | smul scalar section_value _ zero_value =>
        have scalar_same : coefficient_equiv.symm (scalar • section_value) =
            scalar * coefficient_equiv.symm section_value := by
          apply coefficient_equiv.injective
          rw [AddEquiv.apply_symm_apply]
          rw [fan.invariantDivisorRestrictedChartCoefficient_smul 𝕜,
            AddEquiv.apply_symm_apply]
        rw [scalar_same, map_mul, zero_value, mul_zero]
  have zero_one := span_vanishes (coefficient_equiv 1) (by rw [all_span]; trivial)
  rw [AddEquiv.symm_apply_apply, map_one] at zero_one
  exact one_ne_zero zero_one

theorem divisorLocalCone_eq_basisCone (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    (fan.divisorLocalCone 𝕜 complete regular
      ((Finite.equivFin fan.cones) ⟨_, cone_basis⟩)).val =
        PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
  let cone : fan.cones := ⟨_, cone_basis⟩
  let chosen := fan.divisorChartBasis complete regular cone
  have face_of := chosen.property.2
  have full_span : Submodule.span ℝ
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) : Set Ambient) = ⊤ := by
    let real_basis := fan.lattice.isBaseChange.basis basis
    have basis_range : Set.range real_basis = Set.range (fun index => embedding (basis index)) := by
      congr 1
      funext index
      exact fan.lattice.isBaseChange.basis_apply basis index
    apply top_unique
    rw [← real_basis.span_eq, basis_range]
    exact Submodule.span_mono PointedCone.subset_hull
  have same := BondalThomsen.face_eq_of_fullSpan face_of full_span
  change (fan.divisorChartCone complete regular
    ((Finite.equivFin fan.cones).symm ((Finite.equivFin fan.cones) cone))).val = _
  rw [(Finite.equivFin fan.cones).symm_apply_apply]
  exact same.symm

theorem coneDivisorCharacter_eq_of_basisCone_eq (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    {first_dimension second_dimension : ℕ}
    (first : Basis (Fin first_dimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin second_dimension) ℤ Lattice) (second_cone : fan.IsConeBasis second)
    (same_cone : PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) =
      PointedCone.hull ℝ (Set.range (fun index => embedding (second index)))) :
    fan.coneDivisorCharacter first first_cone divisor =
      fan.coneDivisorCharacter second second_cone divisor := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply first.ext
  intro index
  have contains_first : embedding (first index) ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) :=
    PointedCone.subset_hull (Set.mem_range_self index)
  have same_value :=
    (fan.divisorSupportFunction_on_coneBasis complete regular divisor first first_cone
      (embedding (first index)) contains_first).symm.trans
        (fan.divisorSupportFunction_on_coneBasis complete regular divisor second second_cone
          (embedding (first index)) (same_cone ▸ contains_first))
  simp only [TauCeti.Toric.IsIntegralLattice.realCharacter_apply] at same_value
  exact_mod_cast same_value

theorem hasRaySupportInequalities_of_generatingSections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (generators : (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.GeneratingSections) :
    fan.HasRaySupportInequalities divisor := by
  intro dimension basis cone_basis ray
  let index := (Finite.equivFin fan.cones) ⟨_, cone_basis⟩
  let chosen := fan.divisorSectionChartBasis complete regular index
  have same_cone := fan.divisorLocalCone_eq_basisCone 𝕜 complete regular basis cone_basis
  have same_character := fan.coneDivisorCharacter_eq_of_basisCone_eq complete regular divisor
    chosen.val.2 chosen.property.1 basis cone_basis same_cone
  have admissible := fan.invariantDivisorLocalCharacter_admissible_of_generatingSections 𝕜
    complete regular divisor generators index
  have inequalities := (fan.characterLaurentMonomial_mem_global_iff 𝕜 divisor _).mp admissible ray
  change -divisor ray ≤ fan.coneDivisorCharacter chosen.val.2 chosen.property.1 divisor ray.val
    at inequalities
  rwa [same_character] at inequalities

theorem invariantDivisorGloballyGenerated_iff_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    fan.InvariantDivisorGloballyGenerated 𝕜 complete regular divisor ↔
      fan.HasRaySupportInequalities divisor :=
  ⟨fun ⟨generators⟩ => fan.hasRaySupportInequalities_of_generatingSections 𝕜
    complete regular divisor generators,
    fun support => ⟨fan.invariantDivisorSheafGeneratingSections 𝕜 complete regular divisor support⟩⟩

end TauCeti.Toric.Fan

