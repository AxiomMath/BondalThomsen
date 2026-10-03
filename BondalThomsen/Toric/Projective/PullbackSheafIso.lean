module

public import BondalThomsen.Toric.Projective.GlobalPullback
public import BondalThomsen.ProjectiveBundle.GlobalRelativeQuotient

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

theorem moduleRestrictUnitIso_pullbackUnit {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion] :
    (Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.app
        (SheafOfModules.unit target.ringCatSheaf) ≫
      (Scheme.Modules.pullbackObjUnitIso inclusion).hom =
        (Scheme.Modules.restrictUnitIso inclusion).hom := by
  apply ((Scheme.Modules.restrictAdjunction inclusion).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← Adjunction.homEquiv_unit]
  erw [Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  ext open_set coefficient
  change inclusion.app open_set coefficient = _
  rw [Adjunction.homEquiv_unit]
  change inclusion.app open_set coefficient =
    (inclusion.appIso (inclusion ⁻¹ᵁ open_set)).hom
      (target.presheaf.map (homOfLE (inclusion.image_preimage_le open_set)).op coefficient)
  apply (ConcreteCategory.bijective_of_isIso
    (inclusion.appIso (inclusion ⁻¹ᵁ open_set)).inv).1
  rw [← ConcreteCategory.comp_apply, inclusion.app_appIso_inv,
    ← ConcreteCategory.comp_apply, Iso.hom_inv_id]
  rfl

theorem modulePullbackSectionHom_restrict {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion] {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf) :
    modulePullbackSectionHom inclusion section_map =
      (Scheme.Modules.restrictUnitIso inclusion).inv ≫
        (Scheme.Modules.restrictFunctor inclusion).map section_map ≫
          (Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.app sheaf := by
  have unit_equality := moduleRestrictUnitIso_pullbackUnit inclusion
  have inverse_equality :
      (Scheme.Modules.pullbackObjUnitIso inclusion).inv =
        (Scheme.Modules.restrictUnitIso inclusion).inv ≫
          (Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.app
            (SheafOfModules.unit target.ringCatSheaf) := by
    apply (cancel_mono (Scheme.Modules.pullbackObjUnitIso inclusion).hom).mp
    simp only [Category.assoc, unit_equality, Iso.inv_hom_id]
  unfold modulePullbackSectionHom
  rw [inverse_equality, Category.assoc]
  rw [← (Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.naturality section_map]

theorem moduleHom_restrict_isIso {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    {first second : target.Modules} (morphism : first ⟶ second)
    (local_iso : IsIso (morphism.over inclusion.opensRange)) :
    IsIso ((Scheme.Modules.restrictFunctor inclusion).map morphism) := by
  let := local_iso
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro open_set
  let local_open : Over inclusion.opensRange :=
    Over.mk (homOfLE (show inclusion ''ᵁ open_set ≤ inclusion.opensRange from
      fun _ contained => by rcases contained with ⟨point, member, rfl⟩; exact ⟨point, rfl⟩))
  have app_iso := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map_isIso
    (morphism.over inclusion.opensRange)
  let := app_iso
  have component_iso : IsIso
      (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        (morphism.over inclusion.opensRange)).app (op local_open)) := inferInstance
  exact component_iso

theorem moduleHom_over_isIso_of_restrict {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    {first second : target.Modules} (morphism : first ⟶ second)
    (local_iso : IsIso ((Scheme.Modules.restrictFunctor inclusion).map morphism)) :
    IsIso (morphism.over inclusion.opensRange) := by
  let := local_iso
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget _)).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro local_open
  have image_equality : inclusion ''ᵁ (inclusion ⁻¹ᵁ local_open.unop.left) =
      local_open.unop.left := by
    apply Opens.ext
    exact Set.image_preimage_eq_of_subset local_open.unop.hom.le
  have component_iso := (Scheme.Modules.Hom.isIso_iff_isIso_app.mp local_iso)
    (inclusion ⁻¹ᵁ local_open.unop.left)
  change IsIso (Scheme.Modules.Hom.app morphism local_open.unop.left)
  change IsIso (Scheme.Modules.Hom.app morphism
    (inclusion ''ᵁ (inclusion ⁻¹ᵁ local_open.unop.left))) at component_iso
  rwa [image_equality] at component_iso

theorem modulePullbackSectionHom_comp_isIso {source middle target : Scheme}
    (first : source ⟶ middle) (second : middle ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (local_iso : IsIso (modulePullbackSectionHom second section_map)) :
    IsIso (modulePullbackSectionHom (first ≫ second) section_map) := by
  let := local_iso
  rw [← modulePullbackSectionHom_comp first second section_map]
  change IsIso ((Scheme.Modules.pullbackObjUnitIso first).inv ≫
    (Scheme.Modules.pullback first).map (modulePullbackSectionHom second section_map) ≫
      (Scheme.Modules.pullbackComp first second).hom.app sheaf)
  apply IsIso.comp_isIso'
  · infer_instance
  · apply IsIso.comp_isIso'
    · infer_instance
    · exact inferInstanceAs (IsIso ((Scheme.Modules.pullbackComp first second).hom.app sheaf))

theorem modulePullbackSectionHom_over_isIso {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion] {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (local_iso : IsIso (modulePullbackSectionHom inclusion section_map)) :
    IsIso (section_map.over inclusion.opensRange) := by
  apply moduleHom_over_isIso_of_restrict inclusion
  rw [modulePullbackSectionHom_restrict] at local_iso
  exact (isIso_comp_right_iff _
    ((Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.app sheaf)).mp
      ((isIso_comp_left_iff (Scheme.Modules.restrictUnitIso inclusion).inv _).mp local_iso)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (Index : Type)

theorem polynomialProjDegreeOneCoordinateHom_restrict_isIso (coordinate : Index) :
    IsIso ((Scheme.Modules.restrictFunctor
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι).map
        (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)) := by
  apply moduleHom_restrict_isIso
  erw [Scheme.Opens.opensRange_ι]
  exact polynomialProjDegreeOneCoordinateHom_over_isIso 𝕜 Index coordinate

theorem polynomialProjDegreeOneCoordinateHom_pullbackChart_isIso (coordinate : Index) :
    IsIso (modulePullbackSectionHom (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜)
      (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X 𝕜 coordinate) (by decide))
        (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)) := by
  let chart_iso := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X 𝕜 coordinate) (by decide)
  let := polynomialProjDegreeOneCoordinateHom_restrict_isIso 𝕜 Index coordinate
  have local_iso : IsIso (modulePullbackSectionHom
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι
        (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)) := by
    rw [modulePullbackSectionHom_restrict]
    infer_instance
  let := local_iso
  have transported := modulePullbackSectionHom_comp chart_iso.inv
    (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι
      (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)
  change IsIso (modulePullbackSectionHom
    (chart_iso.inv ≫ (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι)
      (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate))
  rw [← transported]
  unfold modulePullbackSectionHom at ⊢
  change IsIso ((Scheme.Modules.pullbackObjUnitIso chart_iso.inv).inv ≫
    (Scheme.Modules.pullback chart_iso.inv).map
      (modulePullbackSectionHom (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι
        (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)) ≫
      (Scheme.Modules.pullbackComp chart_iso.inv
        (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι).hom.app
          (polynomialProjDegreeOneSheaf 𝕜 Index))
  apply IsIso.comp_isIso'
  · infer_instance
  · apply IsIso.comp_isIso'
    · infer_instance
    · exact inferInstanceAs (IsIso ((Scheme.Modules.pullbackComp chart_iso.inv
        (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι).hom.app
          (polynomialProjDegreeOneSheaf 𝕜 Index)))

end

end BondalThomsen

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)

noncomputable def divisorProjectiveSourceCoordinateHom
    (coordinate : Fin (Nat.card fan.cones)) :
    SheafOfModules.unit (fan.algebraicRealization 𝕜 regular).ringCatSheaf ⟶
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj :=
  BondalThomsen.moduleGlobalSectionHom _
    (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support coordinate)

theorem divisorProjectiveSourceCoordinate_smul_injective
    (chart : Fin (Nat.card fan.cones))
    (open_set : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty open_set] :
    Function.Injective (fun coefficient : Γ(fan.algebraicRealization 𝕜 regular, open_set) =>
      coefficient • fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support chart)) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  intro first second equal
  have rational_equality := congrArg (fun section_value =>
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set
      (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι
        open_set section_value)) equal
  simp only [Scheme.Modules.Hom.app_smul,
    (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set).map_smul] at rational_equality
  have generator_value := fan.invariantDivisorSheafRestrictGlobal_rationalValue 𝕜 complete regular
    divisor open_set
    ⟨fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor chart),
      fan.divisorLocalCharacter_monomial_mem_global 𝕜 complete regular divisor support chart⟩
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set
    (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι open_set
      (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support chart))) =
    fan.laurentRationalMap 𝕜 regular (fan.completeFan_nonemptyCones complete)
      (fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor chart))
    at generator_value
  rw [fan.laurentRationalMap_characterMonomial 𝕜 regular _] at generator_value
  change (fan.algebraicRealization 𝕜 regular).germToFunctionField open_set first * _ =
    (fan.algebraicRealization 𝕜 regular).germToFunctionField open_set second * _ at rational_equality
  rw [generator_value] at rational_equality
  exact (fan.algebraicRealization 𝕜 regular).germToFunctionField_injective open_set
    ((fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
      (fan.divisorLocalCharacter 𝕜 complete regular divisor chart)).isUnit.mul_right_cancel rational_equality)

theorem divisorProjectiveSourceCoordinateHom_over_isIso
    (chart : Fin (Nat.card fan.cones)) :
    IsIso ((fan.divisorProjectiveSourceCoordinateHom 𝕜 complete regular divisor support chart).over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget _)).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro local_open
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let open_set := local_open.unop.left
  by_cases nonempty : Nonempty open_set
  · let := nonempty
    change Function.Bijective (fun coefficient : Γ(fan.algebraicRealization 𝕜 regular, open_set) =>
      coefficient • fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support chart))
    refine ⟨fan.divisorProjectiveSourceCoordinate_smul_injective 𝕜 complete regular divisor support
      chart open_set, ?_⟩
    intro section_value
    exact fan.invariantDivisorSheaf_subchart_generated_by_global 𝕜 complete regular divisor support
      chart open_set local_open.unop.hom.le section_value
  · have open_empty : open_set = ⊥ := by
      apply Opens.ext
      exact Set.eq_empty_iff_forall_notMem.mpr (fun point contains => nonempty ⟨⟨point, contains⟩⟩)
    have scalar_subsingleton : Subsingleton Γ(fan.algebraicRealization 𝕜 regular, open_set) := by
      rw [open_empty]
      infer_instance
    let := scalar_subsingleton
    let : Subsingleton Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, open_set) :=
      Module.subsingleton Γ(fan.algebraicRealization 𝕜 regular, open_set) _
    change Function.Bijective (fun coefficient : Γ(fan.algebraicRealization 𝕜 regular, open_set) =>
      coefficient • fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support chart))
    exact ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

noncomputable def divisorProjectiveSourceCoordinateFrame
    (chart : Fin (Nat.card fan.cones)) :
    SheafOfModules.unit ((fan.algebraicRealization 𝕜 regular).ringCatSheaf.over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange) ≅
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.over
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange := by
  letI := fan.divisorProjectiveSourceCoordinateHom_over_isIso 𝕜 complete regular divisor support chart
  exact asIso ((fan.divisorProjectiveSourceCoordinateHom 𝕜 complete regular divisor support chart).over _)

end TauCeti.Toric.Fan
