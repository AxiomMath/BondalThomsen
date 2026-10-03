module

public import BondalThomsen.Toric.Positivity.InvariantCurveDegree
public import BondalThomsen.Toric.Projective.PullbackSheafIso
public import BondalThomsen.Toric.Divisor.EffectiveHom
public import BondalThomsen.Toric.RankOne.CohomologicalDimension
public import BondalThomsen.Ports.MiyaokaMori.Nef.LineBundleDegreeTensor
public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperCurveWeightedDegree
public import BondalThomsen.Ports.MiyaokaMori.Nef.GenericFiniteCurveMap

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Divisors AlgebraicGeometry.Intersection
open TauCeti.AlgebraicGeometry
open BondalThomsen.ToricRankOneNefVanishing
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace BondalThomsen

theorem normalizationFunctionFieldMap_openImmersionGerm
    {source target : Scheme} [IsIntegral source] [IsIntegral target]
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    (sectionValue : Γ(source, ⊤)) :
    OpenImmersionOrder.functionFieldMap inclusion
      (openImmersionGerm inclusion sectionValue) =
        source.germToFunctionField ⊤ sectionValue := by
  let region := inclusion.opensRange
  let : Nonempty region := ⟨⟨inclusion (genericPoint source), ⟨genericPoint source, rfl⟩⟩⟩
  let transported := (IsOpenImmersion.ΓIsoTop inclusion).hom sectionValue
  have imageContains : inclusion (genericPoint source) ∈ region := ⟨genericPoint source, rfl⟩
  have germEquality := CategoryTheory.congr_fun
    (target.presheaf.germ_stalkSpecializes (IsFrame.genericPoint_mem_region region)
      (specializes_of_eq (genericPoint_eq_of_isOpenImmersion inclusion))) transported
  simp only [ConcreteCategory.comp_apply] at germEquality
  change inclusion.stalkMap (genericPoint source)
    (target.presheaf.stalkSpecializes _
      (target.presheaf.germ region (genericPoint target) _ transported)) = _
  rw [germEquality, inclusion.germ_stalkMap_apply]
  have fullPreimage : ⊤ ≤ inclusion ⁻¹ᵁ region := by
    intro point _
    exact ⟨point, rfl⟩
  have restrictionEquality := source.presheaf.germ_res_apply
    (homOfLE fullPreimage) (genericPoint source) trivial (inclusion.app region transported)
  rw [← restrictionEquality]
  change source.germToFunctionField ⊤ (inclusion.appLE region ⊤ fullPreimage transported) = _
  rw [← openImmersion_sectionsIso_inv inclusion]
  change source.germToFunctionField ⊤
    ((IsOpenImmersion.ΓIsoTop inclusion).inv
      ((IsOpenImmersion.ΓIsoTop inclusion).hom sectionValue)) = _
  have sectionRoundtrip := ConcreteCategory.congr_hom
    (IsOpenImmersion.ΓIsoTop inclusion).hom_inv_id sectionValue
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at sectionRoundtrip
  exact congrArg (source.germToFunctionField ⊤) sectionRoundtrip

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)

theorem rankOneGeneratorDivisor_effective (ray : fan.Ray) :
    0 ≤ fan.rankOneDegreeDivisor complete regular basis 1 ray := by
  classical
  simp only [rankOneDegreeDivisor, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem rankOneGeneratorDivisor_support :
    fan.HasRaySupportInequalities (fan.rankOneDegreeDivisor complete regular basis 1) := by
  apply (fan.rankOne_hasRaySupportInequalities_iff_coefficientDegree_nonnegative
    complete regular basis _).mpr
  simp

def rankOneGeneratorCanonicalSection :
    Γ((fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.rankOneDegreeDivisor complete regular basis 1)).obj, ⊤) :=
  fan.invariantDivisorEffectiveSection 𝕜 complete regular _
    (fan.rankOneGeneratorDivisor_effective complete regular basis)

section GeneralPresentation

variable (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor)

variable [Nonempty fan.cones]

variable {𝕜} in
local instance normalizationIntegral : IsIntegral (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isIntegral 𝕜 regular inferInstance

variable {𝕜} in
local instance normalizationNoetherian : IsNoetherian (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isNoetherian 𝕜 regular

omit [Nonempty fan.cones] in
theorem invariantDivisorCanonicalSectionChartFrame (chart : Fin (Nat.card fan.cones)) :
    IsFrame (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange
      (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor _
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support chart)) := by
  intro smaller contained
  simp only [invariantDivisorSheafRestrictGlobal, res_res]
  by_cases nonempty : Nonempty smaller
  · let := nonempty
    exact ⟨fan.divisorProjectiveSourceCoordinate_smul_injective 𝕜 complete regular divisor support
      chart smaller, fun sectionValue =>
        fan.invariantDivisorSheaf_subchart_generated_by_global 𝕜 complete regular divisor support
          chart smaller contained sectionValue⟩
  · have empty : smaller = ⊥ := by
      apply Opens.ext
      exact Set.eq_empty_iff_forall_notMem.mpr (fun point contains => nonempty ⟨⟨point, contains⟩⟩)
    subst smaller
    let : Subsingleton Γ(fan.algebraicRealization 𝕜 regular, ⊥) := inferInstance
    let : Subsingleton Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, ⊥) :=
      Module.subsingleton Γ(fan.algebraicRealization 𝕜 regular, ⊥) _
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

def invariantDivisorEffectiveRationalPresentation
    (effective : ∀ ray, 0 ≤ divisor ray) :
    LineRationalSectionPresentation (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
      ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.germ ⊤
        (genericPoint (fan.algebraicRealization 𝕜 regular)) trivial
        (fan.invariantDivisorEffectiveSection 𝕜 complete regular divisor effective)) := by
  let bundle := (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
  let sectionValue := fan.invariantDivisorEffectiveSection 𝕜 complete regular divisor effective
  have genericNonzero : bundle.presheaf.germ ⊤
      (genericPoint (fan.algebraicRealization 𝕜 regular)) trivial sectionValue ≠ 0 := by
    simpa only [map_zero] using (InvertibleSheaf.germ_injective_of_isIntegral
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) (U := ⊤)
      (genericPoint _) trivial).ne
        (fan.invariantDivisorEffectiveSection_ne_zero 𝕜 complete regular divisor effective)
  apply LineRationalSectionPresentation.ofFiniteFrames bundle
    (fun chart : Fin (Nat.card fan.cones) =>
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange)
    (fun chart => fan.chartOpen_nonempty 𝕜 regular _) _
    (fun chart => fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor _
      (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support chart))
    (fan.invariantDivisorCanonicalSectionChartFrame 𝕜 complete regular divisor support)
    _ genericNonzero
  apply Set.eq_univ_of_forall
  intro point
  have covered : point ∈ iSup (fun chart : Fin (Nat.card fan.cones) =>
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange) := by
    unfold divisorLocalCone
    erw [(fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).covers.iSup_eq_top]
    trivial
  obtain ⟨chart, contains⟩ := Opens.mem_iSup.mp covered
  exact Set.mem_iUnion.mpr ⟨chart, contains⟩

theorem invariantDivisorEffectiveRationalPresentation_equation
    (effective : ∀ ray, 0 ≤ divisor ray) (chart : Fin (Nat.card fan.cones)) :
    (fan.invariantDivisorEffectiveRationalPresentation 𝕜 complete regular divisor support
      effective).cartier.equation chart =
        (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-fan.divisorLocalCharacter 𝕜 complete regular divisor chart) :
            (fan.algebraicRealization 𝕜 regular).functionField) := by
  let region := (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
  let bundle := (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
  let sectionValue := fan.invariantDivisorEffectiveSection 𝕜 complete regular divisor effective
  let frame := fan.invariantDivisorCanonicalSectionChartFrame 𝕜 complete regular divisor support chart
  have genericEquality : bundle.presheaf.germ ⊤ (genericPoint (fan.algebraicRealization 𝕜 regular))
      trivial sectionValue = bundle.presheaf.germ region (genericPoint _)
        (IsFrame.genericPoint_mem_region region) (bundle.res le_top sectionValue) :=
    (TopCat.Presheaf.germ_res_apply bundle.presheaf (homOfLE le_top)
      (genericPoint _) (IsFrame.genericPoint_mem_region region) sectionValue).symm
  change frame.genericCoordinate (bundle.presheaf.germ ⊤ (genericPoint _) trivial sectionValue) = _
  rw [genericEquality, frame.genericCoordinate_germ (subset := le_rfl)]
  have represented := frame.coord_smul_frame le_rfl (bundle.res le_top sectionValue)
  simp only [res_self] at represented
  have rationalEquality := congrArg (fun value =>
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv region
      (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι
        region value)) represented
  rw [Scheme.Modules.Hom.app_smul,
    (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv region).map_smul] at rationalEquality
  have sectionRational := fan.invariantDivisorEffectiveSection_rationalValue 𝕜 complete regular
    divisor effective region
  have generatorRational := fan.invariantDivisorSheafRestrictGlobal_rationalValue 𝕜 complete regular
    divisor region
    ⟨fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor chart),
      fan.divisorLocalCharacter_monomial_mem_global 𝕜 complete regular divisor support chart⟩
  rw [fan.laurentRationalMap_characterMonomial 𝕜] at generatorRational
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv region
    (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι region
      (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor region
        (fan.invariantDivisorSheafGlobalChartGenerator 𝕜 complete regular divisor support chart))) =
      (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (fan.divisorLocalCharacter 𝕜 complete regular divisor chart) :
          (fan.algebraicRealization 𝕜 regular).functionField) at generatorRational
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv region
    (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι region
      (bundle.res le_top sectionValue)) = 1 at sectionRational
  change (fan.algebraicRealization 𝕜 regular).germToFunctionField region
      (frame.coord le_rfl (bundle.res le_top sectionValue)) * _ = _ at rationalEquality
  erw [generatorRational, sectionRational] at rationalEquality
  rw [fan.rationalCharacterUnit_neg 𝕜]
  simp only [Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_left rationalEquality

end GeneralPresentation

section GeneratorPresentation

variable [Nonempty fan.cones]

variable {𝕜} in
local instance normalizationGeneratorIntegral : IsIntegral (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isIntegral 𝕜 regular inferInstance

variable {𝕜} in
local instance normalizationGeneratorNoetherian : IsNoetherian (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isNoetherian 𝕜 regular

variable {𝕜} in
local instance normalizationGeneratorBaseOver :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def rankOneGeneratorRationalPresentation :
    LineRationalSectionPresentation
      (fan.invariantDivisorLineBundle 𝕜 complete regular
        (fan.rankOneDegreeDivisor complete regular basis 1)).obj
      ((fan.invariantDivisorLineBundle 𝕜 complete regular
        (fan.rankOneDegreeDivisor complete regular basis 1)).obj.presheaf.germ ⊤
        (genericPoint (fan.algebraicRealization 𝕜 regular)) trivial
        (fan.rankOneGeneratorCanonicalSection 𝕜 complete regular basis)) :=
  fan.invariantDivisorEffectiveRationalPresentation 𝕜 complete regular _
    (fan.rankOneGeneratorDivisor_support complete regular basis)
    (fan.rankOneGeneratorDivisor_effective complete regular basis)

theorem rankOneGeneratorRationalPresentation_equation (chart : Fin (Nat.card fan.cones)) :
    (fan.rankOneGeneratorRationalPresentation 𝕜 complete regular basis).cartier.equation chart =
      (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (-fan.divisorLocalCharacter 𝕜 complete regular
          (fan.rankOneDegreeDivisor complete regular basis 1) chart) :
            (fan.algebraicRealization 𝕜 regular).functionField) :=
  fan.invariantDivisorEffectiveRationalPresentation_equation 𝕜 complete regular _ _ _ chart

theorem rankOneGeneratorRationalPresentation_geometricDegree :
    letI := fan.complete_regular_structureMap_isProper 𝕜 complete regular
    (fan.rankOneGeometricDegreeNormalization 𝕜) complete regular basis =
      (fan.rankOneGeneratorRationalPresentation 𝕜 complete regular basis).cartier.degreeOver
        (fan.structureMap 𝕜 regular)
        (fan.rankOneIntegralCurve 𝕜 complete regular basis).dim_eq_one.le := by
  let := fan.complete_regular_structureMap_isProper 𝕜 complete regular
  have degreeOne : fan.rankOneInvertibleSheafDegree 𝕜 complete regular basis
      (fan.invariantDivisorLineBundle 𝕜 complete regular
        (fan.rankOneDegreeDivisor complete regular basis 1)) = 1 := by
    rw [fan.rankOneInvertibleSheafDegree_invariantDivisor 𝕜]
    exact fan.rankOneDegreeDivisor_coefficientDegree complete regular basis 1
  have normalization := fan.rankOneGeometricLineBundleDegree_eq_normalization_mul 𝕜
    complete regular basis (fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.rankOneDegreeDivisor complete regular basis 1))
  rw [degreeOne, one_mul] at normalization
  rw [← normalization]
  exact Intersection.lineBundleDegree_eq_of_presentation (fan.structureMap 𝕜 regular)
    (fan.rankOneIntegralCurve 𝕜 complete regular basis).dim_eq_one.le
    (fan.rankOneGeneratorRationalPresentation 𝕜 complete regular basis)

omit [Nonempty fan.cones] in
theorem rankOneGeneratorLocalCharacter_eq_zero_of_negativeChart
    (chart : Fin (Nat.card fan.cones))
    (negativeChart : (fan.divisorLocalCone 𝕜 complete regular chart).val =
      PointedCone.hull ℝ (Set.range (fun index => embedding (rankOneNegativeBasis basis index)))) :
    fan.divisorLocalCharacter 𝕜 complete regular
      (fan.rankOneDegreeDivisor complete regular basis 1) chart = 0 := by
  let divisor := fan.rankOneDegreeDivisor complete regular basis 1
  have negativeContains : embedding (fan.rankOneNegativeRay complete regular basis).val ∈
      (fan.divisorLocalCone 𝕜 complete regular chart).val := by
    rw [negativeChart, fan.rankOneNegativeRay_val]
    exact PointedCone.subset_hull ⟨0, by simp [rankOneNegativeBasis_apply]⟩
  have characterValue := fan.invariantDivisorCharacterAtlas_presentsDivisor 𝕜
    complete regular divisor chart (fan.rankOneNegativeRay complete regular basis) negativeContains
  change fan.divisorLocalCharacter 𝕜 complete regular divisor chart
    (fan.rankOneNegativeRay complete regular basis).val = -divisor _ at characterValue
  rw [fan.rankOneNegativeRay_val, map_neg] at characterValue
  have divisorValue : divisor (fan.rankOneNegativeRay complete regular basis) = 0 := by
    classical
    simp [divisor, rankOneDegreeDivisor,
      fan.rankOnePositiveRay_ne_negativeRay complete regular basis]
  rw [divisorValue, neg_zero] at characterValue
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  have indexZero : index = 0 := Subsingleton.elim _ _
  change fan.divisorLocalCharacter 𝕜 complete regular divisor chart (basis index) = 0
  rw [indexZero]
  exact neg_eq_zero.mp characterValue

theorem rankOneGeneratorRationalPresentation_equation_negativeChart
    (chart : Fin (Nat.card fan.cones))
    (negativeChart : (fan.divisorLocalCone 𝕜 complete regular chart).val =
      PointedCone.hull ℝ (Set.range (fun index => embedding (rankOneNegativeBasis basis index)))) :
    (fan.rankOneGeneratorRationalPresentation 𝕜 complete regular basis).cartier.equation chart = 1 := by
  rw [fan.rankOneGeneratorRationalPresentation_equation 𝕜,
    fan.rankOneGeneratorLocalCharacter_eq_zero_of_negativeChart 𝕜 complete regular basis chart
      negativeChart, neg_zero, fan.rationalCharacterUnit_zero 𝕜]
  rfl

end GeneratorPresentation

section RationalCharacterCoordinate

variable [Nonempty fan.cones]

variable {𝕜} in
local instance normalizationCoordinateIntegral : IsIntegral (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isIntegral 𝕜 regular inferInstance

def rankOnePositiveCoordinateCharacter (_fan : Fan embedding)
    (basis : Basis (Fin 1) ℤ Lattice) : Lattice →+ ℤ := (basis.coord 0).toAddMonoidHom

omit [FiniteDimensional ℝ Ambient] [Nonempty fan.cones] in
theorem rankOnePositiveCoordinateCharacter_mem :
    fan.rankOnePositiveCoordinateCharacter basis ∈ dualSemigroup fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) := by
  apply (fan.mem_dualSemigroup_basisCone_iff basis _).mpr
  intro index
  have indexZero : index = 0 := Subsingleton.elim _ _
  simp [rankOnePositiveCoordinateCharacter, indexZero, Basis.coord_apply]

omit [FiniteDimensional ℝ Ambient] [Nonempty fan.cones] in
theorem rankOnePositiveCoordinateCharacter_polynomial :
    fan.rankOneAffineLineCoordinateEquiv 𝕜 basis
      (MonoidAlgebra.single (Multiplicative.ofAdd
        (⟨fan.rankOnePositiveCoordinateCharacter basis,
          fan.rankOnePositiveCoordinateCharacter_mem basis⟩ :
          dualSemigroup fan.lattice
            (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))) 1) =
      Polynomial.X := by
  rw [rankOneAffineLineCoordinateEquiv, AlgEquiv.trans_apply,
    fan.basisConeCoordinateRingEquiv_single 𝕜, MvPolynomial.uniqueAlgEquiv_monomial]
  change Polynomial.monomial
    ((fan.basisConeDualSemigroupEquiv basis) ⟨_, fan.rankOnePositiveCoordinateCharacter_mem basis⟩
      (default : Fin 1)) 1 = _
  have exponentOne : (fan.basisConeDualSemigroupEquiv basis)
      ⟨fan.rankOnePositiveCoordinateCharacter basis,
        fan.rankOnePositiveCoordinateCharacter_mem basis⟩ (default : Fin 1) = 1 := by
    simp [basisConeDualSemigroupEquiv, rankOnePositiveCoordinateCharacter, Basis.coord_apply]
  rw [exponentOne]
  exact Polynomial.monomial_one_one_eq_X

theorem rankOneAffineLineFunctionFieldEquiv_chartCoordinate
    (coordinate : affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis
      (fan.chartCoordinateGerm 𝕜 regular (fan.completeFan_nonemptyCones complete)
        ⟨_, fan.rankOne_isConeBasis complete regular basis⟩ coordinate) =
      AffineLinePrincipalOrder.polyToFunctionField 𝕜
        (fan.rankOneAffineLineCoordinateEquiv 𝕜 basis coordinate) := by
  let polynomialIso := fan.rankOneAffineLineChartIso 𝕜 complete regular basis
  let inclusion := fan.affineToricChartι 𝕜 regular
    ⟨_, fan.rankOne_isConeBasis complete regular basis⟩
  have sectionEquality := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (fan.rankOneAffineLineCoordinateEquiv 𝕜 basis).toRingHom)
  have sectionEqualityValue := ConcreteCategory.congr_hom sectionEquality coordinate
  simp only [ConcreteCategory.comp_apply] at sectionEqualityValue
  change (Scheme.ΓSpecIso _).inv (fan.rankOneAffineLineCoordinateEquiv 𝕜 basis coordinate) =
    polynomialIso.hom.appTop ((Scheme.ΓSpecIso _).inv coordinate) at sectionEqualityValue
  have germEquality := BondalThomsen.openImmersionGerm_comp polynomialIso.hom inclusion
    ((Scheme.ΓSpecIso _).inv coordinate)
  rw [← sectionEqualityValue] at germEquality
  have mapped := congrArg (fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis)
    germEquality
  change OpenImmersionOrder.functionFieldMap (fan.rankOneAffineLineChartι 𝕜 complete regular basis)
      (BondalThomsen.openImmersionGerm (fan.rankOneAffineLineChartι 𝕜 complete regular basis)
        ((Scheme.ΓSpecIso _).inv (fan.rankOneAffineLineCoordinateEquiv 𝕜 basis coordinate))) =
    (fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis)
      (fan.chartCoordinateGerm 𝕜 regular (fan.completeFan_nonemptyCones complete)
        ⟨_, fan.rankOne_isConeBasis complete regular basis⟩ coordinate) at mapped
  rw [BondalThomsen.normalizationFunctionFieldMap_openImmersionGerm] at mapped
  exact mapped.symm

theorem rankOnePositiveCoordinateCharacter_rational :
    (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
      (fan.rankOnePositiveCoordinateCharacter basis) :
        (fan.algebraicRealization 𝕜 regular).functionField) =
      fan.rankOneAffineRationalCoordinate 𝕜 complete regular basis := by
  apply (fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis).injective
  rw [rankOneAffineRationalCoordinate, RingEquiv.apply_symm_apply]
  have exactMonomial : fan.chartCoordinateGerm 𝕜 regular (fan.completeFan_nonemptyCones complete)
      ⟨_, fan.rankOne_isConeBasis complete regular basis⟩
      (MonoidAlgebra.single (Multiplicative.ofAdd
        ⟨fan.rankOnePositiveCoordinateCharacter basis,
          fan.rankOnePositiveCoordinateCharacter_mem basis⟩) 1) =
      (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (fan.rankOnePositiveCoordinateCharacter basis) :
          (fan.algebraicRealization 𝕜 regular).functionField) := by
    rw [fan.chartCoordinateGerm_torus 𝕜, faceAffineCoordinateRingMap_single]
    rfl
  rw [← exactMonomial, fan.rankOneAffineLineFunctionFieldEquiv_chartCoordinate 𝕜,
    fan.rankOnePositiveCoordinateCharacter_polynomial 𝕜]

end RationalCharacterCoordinate

section GeneratorCoefficients

variable [Nonempty fan.cones]

variable {𝕜} in
local instance normalizationCoefficientsIntegral : IsIntegral (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isIntegral 𝕜 regular inferInstance

variable {𝕜} in
local instance normalizationCoefficientsNoetherian : IsNoetherian (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isNoetherian 𝕜 regular

variable {𝕜} in
local instance normalizationCoefficientsBaseOver :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

omit [Nonempty fan.cones] in
theorem rankOneGeneratorLocalCharacter_eq_negativeCoordinate_of_positiveChart
    (chart : Fin (Nat.card fan.cones))
    (positiveChart : (fan.divisorLocalCone 𝕜 complete regular chart).val =
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :
    -fan.divisorLocalCharacter 𝕜 complete regular
      (fan.rankOneDegreeDivisor complete regular basis 1) chart =
        fan.rankOnePositiveCoordinateCharacter basis := by
  let divisor := fan.rankOneDegreeDivisor complete regular basis 1
  have positiveContains : embedding (fan.rankOnePositiveRay complete regular basis).val ∈
      (fan.divisorLocalCone 𝕜 complete regular chart).val := by
    rw [positiveChart, fan.rankOnePositiveRay_val]
    exact PointedCone.subset_hull ⟨0, rfl⟩
  have characterValue := fan.invariantDivisorCharacterAtlas_presentsDivisor 𝕜
    complete regular divisor chart (fan.rankOnePositiveRay complete regular basis) positiveContains
  change fan.divisorLocalCharacter 𝕜 complete regular divisor chart
    (fan.rankOnePositiveRay complete regular basis).val = -divisor _ at characterValue
  rw [fan.rankOnePositiveRay_val] at characterValue
  have divisorValue : divisor (fan.rankOnePositiveRay complete regular basis) = 1 := by
    simp [divisor, rankOneDegreeDivisor]
  rw [divisorValue] at characterValue
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  have indexZero : index = 0 := Subsingleton.elim _ _
  change -(fan.divisorLocalCharacter 𝕜 complete regular divisor chart (basis index)) =
    (fan.rankOnePositiveCoordinateCharacter basis) (basis index)
  rw [indexZero, characterValue]
  simp [rankOnePositiveCoordinateCharacter, Basis.coord_apply]

theorem rankOneGeneratorRationalPresentation_equation_positiveChart
    (chart : Fin (Nat.card fan.cones))
    (positiveChart : (fan.divisorLocalCone 𝕜 complete regular chart).val =
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :
    (fan.rankOneGeneratorRationalPresentation 𝕜 complete regular basis).cartier.equation chart =
      fan.rankOneAffineRationalCoordinate 𝕜 complete regular basis := by
  rw [fan.rankOneGeneratorRationalPresentation_equation 𝕜,
    fan.rankOneGeneratorLocalCharacter_eq_negativeCoordinate_of_positiveChart 𝕜
      complete regular basis chart positiveChart,
    fan.rankOnePositiveCoordinateCharacter_rational 𝕜]

omit [Nonempty fan.cones] in
theorem rankOneAffineLineChartι_opensRange :
    (fan.rankOneAffineLineChartι 𝕜 complete regular basis).opensRange =
      (fan.affineToricChartι 𝕜 regular ⟨_, fan.rankOne_isConeBasis complete regular basis⟩).opensRange := by
  unfold rankOneAffineLineChartι
  exact Scheme.Hom.opensRange_comp_of_isIso _ _

omit [Nonempty fan.cones] in
theorem rankOneGenerator_exists_positiveChart :
    ∃ chart : Fin (Nat.card fan.cones), fan.divisorLocalCone 𝕜 complete regular chart =
      ⟨_, fan.rankOne_isConeBasis complete regular basis⟩ := by
  let cone : fan.cones := ⟨_, fan.rankOne_isConeBasis complete regular basis⟩
  let chart := (Finite.equivFin fan.cones) cone
  have chartEquality : fan.divisorLocalCone 𝕜 complete regular chart =
      fan.divisorChartCone complete regular cone := by
    change fan.divisorChartCone complete regular ((Finite.equivFin fan.cones).symm chart) = _
    simp [chart]
  have positiveContains : embedding (fan.rankOnePositiveRay complete regular basis).val ∈
      (fan.divisorChartCone complete regular cone).val := by
    apply (fan.divisorChartBasis complete regular cone).property.2.le
    rw [fan.rankOnePositiveRay_val]
    exact PointedCone.subset_hull ⟨0, rfl⟩
  rcases rankOne_basisHull_eq_positive_or_negative (embedding := embedding) basis
    (fan.divisorChartBasis complete regular cone).val.2 with positiveChart | negativeChart
  · refine ⟨chart, chartEquality.trans ?_⟩
    exact Subtype.ext positiveChart
  · change embedding (fan.rankOnePositiveRay complete regular basis).val ∈
      PointedCone.hull ℝ (Set.range (fun index =>
        embedding ((fan.divisorChartBasis complete regular cone).val.2 index))) at positiveContains
    rw [negativeChart] at positiveContains
    have rayEquality := (fan.rankOnePositiveRay_mem_cone_iff complete regular
      (rankOneNegativeBasis basis) (fan.rankOnePositiveRay complete regular basis)).mp positiveContains
    exact (fan.rankOnePositiveRay_ne_negativeRay complete regular basis rayEquality).elim

theorem rankOneGeneratorRationalPresentation_coefficient_eq_single
    (point : fan.algebraicRealization 𝕜 regular) :
    (fan.rankOneGeneratorRationalPresentation 𝕜 complete regular basis).cartier.coefficient point =
      if point = fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis then 1 else 0 := by
  classical
  let datum := (fan.rankOneGeneratorRationalPresentation 𝕜 complete regular basis).cartier
  let chart := datum.indexAt point
  have contains := datum.indexAt_mem point
  have chartAlternative := rankOne_basisHull_eq_positive_or_negative (embedding := embedding) basis
    (fan.divisorSectionChartBasis complete regular chart).val.2
  change (fan.divisorLocalCone 𝕜 complete regular chart).val =
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∨
    (fan.divisorLocalCone 𝕜 complete regular chart).val =
      PointedCone.hull ℝ (Set.range (fun index => embedding (rankOneNegativeBasis basis index)))
      at chartAlternative
  rw [datum.coefficient_eq_ord_of_mem point chart contains]
  rcases chartAlternative with positiveChart | negativeChart
  · have chartEquality : fan.divisorLocalCone 𝕜 complete regular chart =
        ⟨_, fan.rankOne_isConeBasis complete regular basis⟩ := Subtype.ext positiveChart
    change point ∈ (fan.affineToricChartι 𝕜 regular
      (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange at contains
    rw [chartEquality, ← fan.rankOneAffineLineChartι_opensRange 𝕜 complete regular basis] at contains
    obtain ⟨localPoint, imageEquality⟩ := contains
    rw [show datum.equation chart = fan.rankOneAffineRationalCoordinate 𝕜 complete regular basis from
      fan.rankOneGeneratorRationalPresentation_equation_positiveChart 𝕜 complete regular basis
        chart positiveChart]
    by_cases origin : localPoint = AffineLinePrincipalOrder.originPoint 𝕜
    · have boundary : point = fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis := by
        rw [← imageEquality, origin]
        rfl
      rw [boundary, ite_eq_left rfl]
      exact fan.rankOneAffineRationalCoordinate_order_boundary 𝕜 complete regular basis
    · have notBoundary : point ≠ fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis := by
        intro equality
        apply origin
        exact (fan.rankOneAffineLineChartι 𝕜 complete regular basis).isOpenEmbedding.injective
          (imageEquality.trans equality)
      rw [ite_eq_right notBoundary, ← imageEquality]
      exact fan.rankOneAffineRationalCoordinate_order_other 𝕜 complete regular basis localPoint origin
  · have equationOne : datum.equation chart = 1 :=
      fan.rankOneGeneratorRationalPresentation_equation_negativeChart 𝕜 complete regular basis chart
        negativeChart
    rw [equationOne]
    have oneOrder : (fan.algebraicRealization 𝕜 regular).ord (1 :
        (fan.algebraicRealization 𝕜 regular).functionField) point = 0 := by
      have additive := (fan.algebraicRealization 𝕜 regular).ord_mul
        (f := (1 : (fan.algebraicRealization 𝕜 regular).functionField)) (g := 1)
        one_ne_zero one_ne_zero (x := point)
      simp only [one_mul] at additive
      omega
    rw [oneOrder]
    by_cases boundary : point = fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis
    · have selectedOrder : (fan.algebraicRealization 𝕜 regular).ord
          (fan.rankOneAffineRationalCoordinate 𝕜 complete regular basis) point = 1 := by
        rw [boundary]
        exact fan.rankOneAffineRationalCoordinate_order_boundary 𝕜 complete regular basis
      have boundaryInPositive : point ∈ (fan.rankOneAffineLineChartι 𝕜 complete regular basis).opensRange := by
        rw [boundary]
        exact ⟨AffineLinePrincipalOrder.originPoint 𝕜, rfl⟩
      have coefficientOne : datum.coefficient point = 1 := by
        have actualPositive := boundaryInPositive
        rw [fan.rankOneAffineLineChartι_opensRange 𝕜 complete regular basis] at actualPositive
        obtain ⟨positiveIndex, positiveEquality⟩ := fan.rankOneGenerator_exists_positiveChart 𝕜
          complete regular basis
        have positiveContains : point ∈ datum.opens positiveIndex := by
          change point ∈ (fan.affineToricChartι 𝕜 regular
            (fan.divisorLocalCone 𝕜 complete regular positiveIndex)).opensRange
          rwa [positiveEquality]
        rw [datum.coefficient_eq_ord_of_mem point positiveIndex positiveContains]
        rw [show datum.equation positiveIndex = fan.rankOneAffineRationalCoordinate 𝕜 complete regular basis from
          fan.rankOneGeneratorRationalPresentation_equation_positiveChart 𝕜 complete regular basis
            positiveIndex (congrArg Subtype.val positiveEquality)]
        exact selectedOrder
      rw [datum.coefficient_eq_ord_of_mem point chart contains, equationOne, oneOrder] at coefficientOne
      omega
    · rw [ite_eq_right boundary]

theorem rankOneGeometricDegreeNormalization_eq_one :
    fan.rankOneGeometricDegreeNormalization 𝕜 complete regular basis = 1 := by
  let := fan.complete_regular_structureMap_isProper 𝕜 complete regular
  rw [fan.rankOneGeneratorRationalPresentation_geometricDegree 𝕜 complete regular basis]
  let datum := (fan.rankOneGeneratorRationalPresentation 𝕜 complete regular basis).cartier
  let bound := (fan.rankOneIntegralCurve 𝕜 complete regular basis).dim_eq_one.le
  change rawZeroCycleDegree (fan.structureMap 𝕜 regular) (datum.zeroCycle bound) = 1
  rw [rawZeroCycleDegree_eq_sum_on (fan.structureMap 𝕜 regular) (datum.zeroCycle bound)
    {fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis} (by
      intro point absent
      have different : point ≠ fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis := by
        simpa using absent
      change datum.coefficient point = 0
      rw [fan.rankOneGeneratorRationalPresentation_coefficient_eq_single 𝕜 complete regular basis,
        ite_eq_right different])]
  simp only [Finset.sum_singleton]
  change datum.coefficient (fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis) *
    (residueFieldDegree (fan.structureMap 𝕜 regular)
      (fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis) : ℤ) = 1
  rw [fan.rankOneGeneratorRationalPresentation_coefficient_eq_single 𝕜 complete regular basis,
    ite_eq_left rfl, Scheme.Hom.residueFieldDegree_eq_residueDegree,
    fan.rankOneAffineBoundaryPoint_residueDegree 𝕜 complete regular basis]
  norm_num

theorem rankOneGeometricLineBundleDegree_eq_picardDegree
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis bundle =
      fan.rankOneInvertibleSheafDegree 𝕜 complete regular basis bundle := by
  rw [fan.rankOneGeometricLineBundleDegree_eq_normalization_mul 𝕜,
    fan.rankOneGeometricDegreeNormalization_eq_one 𝕜 complete regular basis, mul_one]

theorem rankOneGeometricDivisorDegree_eq_coefficientDegree (divisor : fan.InvariantRayDivisor) :
    fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) =
        fan.rankOneDivisorCoefficientDegree complete regular basis divisor := by
  rw [fan.rankOneGeometricLineBundleDegree_eq_picardDegree 𝕜 complete regular basis,
    fan.rankOneInvertibleSheafDegree_invariantDivisor 𝕜]

end GeneratorCoefficients

end TauCeti.Toric.Fan
