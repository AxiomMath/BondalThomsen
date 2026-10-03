module

public import BondalThomsen.Toric.RankOne.PicardCohomology
public import BondalThomsen.Toric.Scheme.KrullDimension
public import BondalThomsen.Toric.Scheme.CompleteRegularProperness
public import BondalThomsen.Ports.MiyaokaMori.Nef.LineBundleDegreeTensor
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable {𝕜} in
local instance rankOneCurveBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def rankOneIntegralCurve
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    IntegralCurve 𝕜 (fan.algebraicRealization 𝕜 regular) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  letI := fan.complete_regular_structureMap_isProper 𝕜 complete regular
  refine {
    carrier := fan.algebraicRealization 𝕜 regular
    ι := 𝟙 _
    isProper := ?_
    dim_eq_one := ?_ }
  · change IsProper (𝟙 _ ≫ fan.structureMap 𝕜 regular)
    simpa only [Category.id_comp] using
      fan.complete_regular_structureMap_isProper 𝕜 complete regular
  · change topologicalKrullDim (fan.algebraicRealization 𝕜 regular) = 1
    rw [fan.algebraicRealization_topologicalKrullDim_eq_lattice_finrank 𝕜 complete regular,
      finrank_eq_card_basis basis]
    simp

@[simp] theorem rankOneIntegralCurve_carrier
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    (fan.rankOneIntegralCurve 𝕜 complete regular basis).carrier =
      fan.algebraicRealization 𝕜 regular := rfl

@[simp] theorem rankOneIntegralCurve_ι
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    (fan.rankOneIntegralCurve 𝕜 complete regular basis).ι = 𝟙 _ := rfl

def rankOneGeometricLineBundleDegree
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) : ℤ :=
  (fan.rankOneIntegralCurve 𝕜 complete regular basis).lineBundleDegree bundle.obj

theorem rankOneGeometricLineBundleDegree_eq_of_iso
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    {first second : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)}
    (comparison : first.obj ≅ second.obj) :
    fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis first =
      fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis second :=
  (fan.rankOneIntegralCurve 𝕜 complete regular basis).lineBundleDegree_eq_of_iso comparison

theorem rankOneGeometricLineBundleDegree_tensor
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    (first second : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis
        (InvertibleSheaf.tensorProduct first second) =
      fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis first +
        fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis second :=
  (fan.rankOneIntegralCurve 𝕜 complete regular basis).lineBundleDegree_tensor first.obj second.obj

theorem rankOneGeometricLineBundleDegree_trivial
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis
      (InvertibleSheaf.trivial (fan.algebraicRealization 𝕜 regular)) = 0 := by
  have additive := fan.rankOneGeometricLineBundleDegree_tensor 𝕜 complete regular basis
    (InvertibleSheaf.trivial _) (InvertibleSheaf.trivial _)
  rw [fan.rankOneGeometricLineBundleDegree_eq_of_iso 𝕜 complete regular basis
    ((SheafOfModules.isInvertible _).ι.mapIso
      (InvertibleSheaf.tensorTrivialLeftIso (InvertibleSheaf.trivial _)))] at additive
  linarith

def rankOneGeometricPicardDegree
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular)) →+ ℤ where
  toFun := fun bundleClass => LineBundleClass.lift
    (fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis)
    (fun _ _ comparison => fan.rankOneGeometricLineBundleDegree_eq_of_iso 𝕜
      complete regular basis comparison.some) bundleClass.toMul
  map_zero' := by
    change LineBundleClass.lift _ _ (LineBundleClass.mk (InvertibleSheaf.trivial _)) = 0
    rw [LineBundleClass.lift_mk]
    exact fan.rankOneGeometricLineBundleDegree_trivial 𝕜 complete regular basis
  map_add' := by
    intro firstClass secondClass
    obtain ⟨first, firstEquality⟩ := LineBundleClass.mk_surjective firstClass.toMul
    obtain ⟨second, secondEquality⟩ := LineBundleClass.mk_surjective secondClass.toMul
    change LineBundleClass.lift _ _ (firstClass.toMul * secondClass.toMul) =
      LineBundleClass.lift _ _ firstClass.toMul + LineBundleClass.lift _ _ secondClass.toMul
    rw [← firstEquality, ← secondEquality, ← LineBundleClass.mk_tensorProduct]
    simp only [LineBundleClass.lift_mk]
    exact fan.rankOneGeometricLineBundleDegree_tensor 𝕜 complete regular basis first second

@[simp] theorem rankOneGeometricPicardDegree_mk
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    fan.rankOneGeometricPicardDegree 𝕜 complete regular basis
      (Additive.ofMul (LineBundleClass.mk bundle)) =
        fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis bundle := by
  simp only [rankOneGeometricPicardDegree, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  change LineBundleClass.lift _ _ (LineBundleClass.mk bundle) = _
  exact LineBundleClass.lift_mk bundle

def rankOneGeometricDegreeNormalization
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) : ℤ :=
  fan.rankOneGeometricPicardDegree 𝕜 complete regular basis
    ((fan.rankOneSchemePicardDegreeEquivInt 𝕜 complete regular basis).symm 1)

theorem rankOneGeometricLineBundleDegree_eq_normalization_mul
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis bundle =
      fan.rankOneInvertibleSheafDegree 𝕜 complete regular basis bundle *
        fan.rankOneGeometricDegreeNormalization 𝕜 complete regular basis := by
  let comparison := fan.rankOneSchemePicardDegreeEquivInt 𝕜 complete regular basis
  let geometric := fan.rankOneGeometricPicardDegree 𝕜 complete regular basis
  let integerDegree := geometric.comp comparison.symm.toAddMonoidHom
  have integerEquality (integer : ℤ) : integerDegree integer = integer * integerDegree 1 := by
    have scalarEquality := integerDegree.map_zsmul integer (1 : ℤ)
    simpa using scalarEquality
  have result := integerEquality (comparison (Additive.ofMul (LineBundleClass.mk bundle)))
  change geometric (comparison.symm (comparison (Additive.ofMul (LineBundleClass.mk bundle)))) =
    comparison (Additive.ofMul (LineBundleClass.mk bundle)) * geometric (comparison.symm 1) at result
  rw [comparison.symm_apply_apply] at result
  simpa only [geometric, rankOneGeometricPicardDegree_mk, comparison,
    rankOneInvertibleSheafDegree, rankOneGeometricDegreeNormalization] using result

def rankOneAffineLineCoordinateEquiv
    (fan : Fan embedding) (basis : Basis (Fin 1) ℤ Lattice) :
    affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ≃ₐ[𝕜]
        Polynomial 𝕜 :=
  (fan.basisConeCoordinateRingEquiv 𝕜 basis).trans (MvPolynomial.uniqueAlgEquiv 𝕜 (Fin 1))

def rankOneAffineLineChartIso
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    Spec (CommRingCat.of (Polynomial 𝕜)) ≅
      fan.affineToricChart 𝕜 ⟨_, fan.rankOne_isConeBasis complete regular basis⟩ :=
  Scheme.Spec.mapIso
    (fan.rankOneAffineLineCoordinateEquiv 𝕜 basis).toRingEquiv.toCommRingCatIso.op

def rankOneAffineLineChartι
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    Spec (CommRingCat.of (Polynomial 𝕜)) ⟶ fan.algebraicRealization 𝕜 regular :=
  (fan.rankOneAffineLineChartIso 𝕜 complete regular basis).hom ≫
    fan.affineToricChartι 𝕜 regular ⟨_, fan.rankOne_isConeBasis complete regular basis⟩

variable {𝕜} in
instance rankOneAffineLineChartι_isOpenImmersion
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    IsOpenImmersion (fan.rankOneAffineLineChartι 𝕜 complete regular basis) := by
  unfold rankOneAffineLineChartι
  infer_instance

theorem rankOneAffineLineChartι_comp_structureMap
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    fan.rankOneAffineLineChartι 𝕜 complete regular basis ≫ fan.structureMap 𝕜 regular =
      AffineLinePrincipalOrder.structureMap 𝕜 := by
  unfold rankOneAffineLineChartι
  rw [Category.assoc, fan.chartι_comp_structureMap 𝕜]
  change Spec.map (CommRingCat.ofHom (fan.rankOneAffineLineCoordinateEquiv 𝕜 basis).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 _)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fan.rankOneAffineLineCoordinateEquiv 𝕜 basis).commutes

def rankOneAffineBoundaryPoint
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) : fan.algebraicRealization 𝕜 regular :=
  fan.rankOneAffineLineChartι 𝕜 complete regular basis (AffineLinePrincipalOrder.originPoint 𝕜)

theorem rankOneAffineBoundaryPoint_residueDegree
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) :
    (fan.structureMap 𝕜 regular).residueDegree
      (fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis) = 1 := by
  have equality := Intersection.residueDegree_comp
    (fan.rankOneAffineLineChartι 𝕜 complete regular basis) (fan.structureMap 𝕜 regular)
    (AffineLinePrincipalOrder.originPoint 𝕜)
  rw [fan.rankOneAffineLineChartι_comp_structureMap 𝕜,
    ProjectiveLinePrincipalDegree.residueDegree_eq_one_of_isOpenImmersion
      (fan.rankOneAffineLineChartι 𝕜 complete regular basis),
    AffineLinePrincipalOrder.residueDegree_originPoint, mul_one] at equality
  exact equality.symm

section RationalCoordinate

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)

variable [Nonempty fan.cones]

variable {𝕜} in
local instance rankOneCurveIntegral : IsIntegral (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isIntegral 𝕜 regular inferInstance

variable {𝕜} in
local instance rankOneCurveNoetherian : IsNoetherian (fan.algebraicRealization 𝕜 regular) :=
  fan.algebraicRealization_isNoetherian 𝕜 regular

def rankOneAffineLineFunctionFieldEquiv :
    (fan.algebraicRealization 𝕜 regular).functionField ≃+*
      (Spec (CommRingCat.of (Polynomial 𝕜))).functionField := by
  let inclusion := fan.rankOneAffineLineChartι 𝕜 complete regular basis
  let comparison := ((fan.algebraicRealization 𝕜 regular).presheaf.stalkSpecializes
    (specializes_of_eq (genericPoint_eq_of_isOpenImmersion inclusion))) ≫
      inclusion.stalkMap (genericPoint _)
  haveI : IsIso comparison := by
    unfold comparison
    have congrEquality : (fan.algebraicRealization 𝕜 regular).presheaf.stalkSpecializes
        (specializes_of_eq (genericPoint_eq_of_isOpenImmersion inclusion)) =
      ((fan.algebraicRealization 𝕜 regular).presheaf.stalkCongr
        (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion inclusion).symm)).hom := rfl
    rw [congrEquality]
    infer_instance
  exact (asIso comparison).commRingCatIsoToRingEquiv

def rankOneAffineRationalCoordinate : (fan.algebraicRealization 𝕜 regular).functionField :=
  (fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis).symm
    (AffineLinePrincipalOrder.polyToFunctionField 𝕜 Polynomial.X)

theorem rankOneAffineRationalCoordinate_order_boundary :
    (fan.algebraicRealization 𝕜 regular).ord
      (fan.rankOneAffineRationalCoordinate 𝕜 complete regular basis)
      (fan.rankOneAffineBoundaryPoint 𝕜 complete regular basis) = 1 := by
  rw [rankOneAffineBoundaryPoint, ← OpenImmersionOrder.ord_functionFieldMap]
  change (Spec (CommRingCat.of (Polynomial 𝕜))).ord
    ((fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis)
      ((fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis).symm
        (AffineLinePrincipalOrder.polyToFunctionField 𝕜 Polynomial.X))) _ = 1
  rw [RingEquiv.apply_symm_apply]
  exact AffineLinePrincipalOrder.ord_polyToFunctionField_spanPoint 𝕜 Polynomial.irreducible_X

theorem rankOneAffineRationalCoordinate_order_other
    (point : Spec (CommRingCat.of (Polynomial 𝕜)))
    (different : point ≠ AffineLinePrincipalOrder.originPoint 𝕜) :
    (fan.algebraicRealization 𝕜 regular).ord
      (fan.rankOneAffineRationalCoordinate 𝕜 complete regular basis)
      (fan.rankOneAffineLineChartι 𝕜 complete regular basis point) = 0 := by
  rw [← OpenImmersionOrder.ord_functionFieldMap]
  change (Spec (CommRingCat.of (Polynomial 𝕜))).ord
    ((fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis)
      ((fan.rankOneAffineLineFunctionFieldEquiv 𝕜 complete regular basis).symm
        (AffineLinePrincipalOrder.polyToFunctionField 𝕜 Polynomial.X))) point = 0
  rw [RingEquiv.apply_symm_apply]
  exact AffineLinePrincipalOrder.ord_polyToFunctionField_of_ne_spanPoint 𝕜
    Polynomial.irreducible_X point different

end RationalCoordinate

end TauCeti.Toric.Fan
